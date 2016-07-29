\subsection{An operational semantics for the OILR
Machine}\label{an-operational-semantics-for-the-oilr-machine}

In designing an abstract machine for graph transformation, an
operational semantics is a useful tool for debugging our machine design
and drawing a clear division between concerns at the abstract machine
level, and those at the implementation level.

While an algebraic specification is useful in its own right,
implementing that specification in a sufficiently mathematical
programming language not only gives the benefits described above, but
also allows the specification to be executed to test it for correctness
against the reference interpreter described in section
\ref{referenceinterpreter}. Furthermore, a modern strongly-typed
compiler will identify many potential typographical errors.

Haskell is a natural choice for this kind of operational semantics. We
can build on top of our existing parser and graph representation adding
abstractions where necessary, and end up with a semantics that is
broadly familiar in appearance to a reader accustomed to reading
algebraic specifications.

The \LaTeX source of this chapter, available at
\url{https://github.com/UoYCS-plasma/GP2/tree/master/Haskell/OILR4/Eval.lhs}
is a valid literate Haskell file, and can be compiled with
GHC{[}@todo{]} (tested with versions 7.6.3 and 7.10.3). For this reason
the following header, while not contributing directly to the narrative,
is required.

\begin{code}
{-# LANGUAGE NamedFieldPuns #-}
module OILR4.Eval where

import OILR4.Config
import OILR4.Instructions hiding (Src, Tgt, Sid)

import GPSyntax

import Mapping
import Data.List
import Data.Maybe
\end{code}

The first line declares that we are using the \emph{NamedFieldPuns} GHC
extension to the Haskell language. This gives us a more concise syntax
for pattern-matching fields in record-type data types than the Haskell
default (one which will be familiar to anyone with experience of Ocaml).

The second line tells the compiler that the current module is called
\texttt{OILR4.Eval}.

The rest of the above block imports symbols from Haskell standard
libraries and other modules in the GP2 compiler.

\subsection{Glossary of mnemonics}\label{glossary-of-mnemonics}

\begin{Shaded}
\begin{Highlighting}[]
\FunctionTok{!--} \NormalTok{consider putting this }\KeywordTok{in} \NormalTok{an appendix }\FunctionTok{-->}
\end{Highlighting}
\end{Shaded}

The names of many of the concepts we are going to explore have the
unfortunate property of starting with similar letters, meaning that we
must be careful if we wish to give short names with mnemonic value to
functions, variables and abstract machine instructions.

Before writing any code, then let us define a few common mnemonics that
will be re-used as we build the abstract machine, and again later in the
compiler and run-time system.

\begin{description}
\tightlist
\item[A]
an edge in the host graph, mnemonic for \emph{arc}, as we use E for a
graph element. C

refers to the colour of a host graph node, or the mark of an host graph
edge. E

any element of the host graph, either node or edge. I

an in-edge, directed towards a particular node. L

a looped edge, starting and terminating at the same node in the host
graph. N

a node in the host graph. O

an out-edge, pointing away from a particular node. R

rootedness, a node with the root-flag set. V

refers to a label on either a node or an edge, short for \emph{value} as
L is already used for looped edges.
\end{description}

\subsection{Definition of data}\label{definition-of-data}

Consider the types of data necessary for a graph transformation system.

It should be immediately apparent that we require some way of
representing a graph. Let us keep this definition as simple as possible;
a \texttt{Graph} is a set of \emph{graph elements}.

\begin{code}
type Graph = [Elem]
\end{code}

Note that while a more typical graph representation is as a pair -- a
set of nodes and a set of edges -- in GP2 nodes and edges overlap
significantly in the properties that they can have. As a result, using a
single pool of elements gives us a benefit in terms of code reuse and
conciseness, as only those operations that specifically require a node
or an edge need to differentiate between them.

Next let us make concrete what constitutes a graph element.

Two types of element spring immediately to mind: nodes and edges. It
will rapidly become necessary to uniquely identify graph elements, for
instance when defining an edge between two nodes, we therefore introduce
a unique \texttt{ElemId}.

According to the semantics of GP2, both nodes and edges may have an
optional label, and a mark. Additionally nodes have the property of
\emph{rootedness}. Finally, as GP2 does not permit `dangling' edges,
each edge requires exactly one source and exactly one target node.

\begin{code}
data Elem  = Nod { eid  :: ElemId
                 , elbl :: Maybe ELabel
                 , mark :: Mark
                 , rt   :: Rootedness }
           | Edg { eid  :: ElemId
                 , elbl :: Maybe ELabel
                 , mark :: Mark
                 , src  :: Src
                 , tgt  :: Tgt }
      deriving (Show, Eq)
\end{code}

As each element can be uniquely identified, the source and target of an
edge are simply the identifiers of the nodes that form the end-points of
the arc. The identifiers \texttt{Src} and \texttt{Tgt} \emph{must} exist
within the host graph, or GP2's \emph{dangling condition} \ref{todo} has
been violated.

\begin{code}
type Src = ElemId
type Tgt = ElemId
\end{code}

Integers make a convenient unique identifier capable of handling an
arbitrarily large number of graph elements.

\begin{code}
type ElemId = Int
\end{code}

Rootedness is a simple boolean value.

\begin{code}
type Rootedness = Bool
\end{code}

Labels for the complete GP2 language can either be an atomic value or a
list. However as we only support a subset of GP2's full label handling
(see section \ref{todo}), a simple integer is sufficient.

\begin{code}
type ELabel = Int
\end{code}

Finally for graph elements, the mark is a finite alphabet, which we can
also represent as an integer. At this point in describing our
representation, we make the simplifying assumption that the compiler we
are developing will only ever emit marks that are appropriate to the
type of graph element they are being applied to.

\begin{code}
type Mark = Int
\end{code}

For convenience and ease of reference, let us also define a mapping
between the reference-interpreter's named colours and our own integer
representation.

\begin{code}
markToInt :: Mapping Colour Mark
markToInt = [ (Uncoloured, 0)
            , (Red       , 1)
            , (Blue      , 2)
            , (Green     , 3)
            , (Grey      , 4)
            , (Dashed    , 5) ]
\end{code}

Each matching operation we perform against the graph structure we have
just defined can only match a subset of the elements that comprise the
graph. Consider, as a trivial example, that a portion of a rule that
requires a node cannot match an edge. In fact we can know a lot more at
compile time about the characteristics of any graph element we will be
matching (see section \ref{todo}).

In practice most of our match operations will depend on the elements
found by previous instructions. For example, the \emph{search plans} we
use (see section \ref{todo}) build a match outwards from a starting
point by following edges to new nodes. But where do the starting points
come from?

A program's rule-graphs contain a wealth of information about the
characteristics a host-graph node or edge must have in order to match.
Consider the trivial rule shown in figure \ref{todo}, which finds a node
and deletes it. GP2's dangling condition (section \ref{todo}) requires
that any incident edges must be explicitly deleted before node deletion.
Therefore \texttt{n1} cannot match a node with \emph{any} incident
edges. Notice also that \texttt{n1} lacks a mark (or, more precisely, is
marked with \texttt{Uncoloured}), and is unlabelled, both of which
further restrict the possible nodes that can match.

These simple observations tell us that, for this particular rule, only
unlabelled, unmarked nodes with a total degree of zero constitute match
candidates for \texttt{n1}.

Let us refer to a hash of this information -- degree, labelled-ness,
mark, plus rootedness -- as the \emph{signature} of a node \texttt{Sig},
which we assume will be available when required by the OILR machine.

\begin{figure}[htbp]
\centering
\includegraphics{img/placeholder.pdf}
\caption{A simple node-deleting rule}
\end{figure}

For any given rule node then, there exists a set of one or more
signatures compatible with that rule-node. We refer to that set as the
\emph{search space}. Each node has only a single signature, therefore
the sets of nodes described by different signature are disjoint. Each
search space thus describes a set of candidate matches for a node in the
rule graph.

As with other components of our system, for ease of reference, we assign
a unique integer identifier to each search space.

\begin{code}
type Spaces = Mapping SpcId [Sig]
type SpcId  = Int
type Sig    = Int
\end{code}

Once we have found a graph element, we need somewhere to store it while
we manipulate it. The obvious choice is between a stack and a register
file. The former simplifies our instructions by making parameter-passing
implicit at the expense of introducing `stack-shuffling' primitives into
the instruction set, while the latter eliminates the need for stack
shuffling at the cost of instructions requiring additional register
parameters.

We opt for registers because having fixed registers ids passed to
machine instructions simplifies the process of rearranging rule matching
code with alternative search-plans (see section \ref{todo}). In
addition, the number of registers required by any rule can be trivially
known at compile-time, having as an upper-bound the sum of the number of
graph elements on the left- and right-hand-sides of the rule-graph.

Not wanting to throw away all of the benefits of a stack, later we will
introduce an accumulator register to serve as an implicit destination
for some operations (section \ref{todo}).

The statefulness of our search spaces complicates matters somewhat.
While the naive approach of thinking of the contents of a register as
representing a simple graph element, in practice each match describes
one step in the traversal of a set of of nodes or edges. For this reason
it makes sense to represent the contents of the register as a list.

Think of this as equivalent to storing a pointer into a linked-list in a
hardware register, giving easy access to both the under-consideration
element at the head of the list, and the unexplored portion of the
search space following it. The empty set serves as a convenient
null-value akin to the null pointer at the end of a C linked-list.

\begin{code}
type RegFile = Mapping RegId [Elem]
\end{code}

Register names are again simple integers, which in this case only need
be unique within the scope of a particular rule-call.

\begin{code}
type RegId = Int
\end{code}

Note that the undesirable possibility of matching the same graph element
twice in the same rule still exists, in violation of GP2's injectivity
requirements (section \ref{todo}). The introduction of \emph{binding}
graph elements in section \ref{todo}, will address this risk.

Another important component of an abstract machine is the program
itself, represented as an immutable ordered list of instructions.

\begin{code}
type Program = [Instr]
\end{code}

The abstract machine shares its definition of \texttt{Instr} with the
compiler. We will set out the details of the instruction set in section
\ref{todo} below.

The immutability of the program means that we can safely use simple
integer offsets into the list as addresses.

\begin{code}
type Addr = Int
\end{code}

Numeric addresses do not make for readable program listings, so let us
introduce a textual label so that jumps may be expressed with more
clarity. The compiler has the ultimate responsibility of ensuring that
labels are unique.

\begin{code}
type JLabel = String
\end{code}

The semantics of GP2 require us to be able to undo changes made to the
graph. To facilitate this we wish to record a pair representing the
before and after state of a graph element as we change it.

\begin{code}
type Change = (Before, After)
\end{code}

When a new element is introduced there is no before state. Likewise for
deleted elements, the after state is absent, therefore it is necessary
to use a representation for both the before and after state that can
accommodate a null value.

\begin{code}
type Before = Maybe Elem
type After = Maybe Elem
\end{code}

Finally, GP2's non-determinstic \emph{program OR} construction requires
one bit of randomness per call, so let us introduce the notion of an
\emph{entropy pool} represented by a set of random booleans.

\begin{code}
type EntropyPool = [Bool]
\end{code}

\subsection{Building the
machine-state}\label{building-the-machine-state}

Having established what kinds of data the OILR machine is going to
process, let us systematically construct a representation of the virtual
machine state using the data-types we just described.

\begin{code}
data VM = VM {
\end{code}

In the previous section (\ref{todo}) identifying one type of data
informed other types of information we needed. Here there are several
possible ways to group machine components, for example describing
registers, then flags, then sections of heap memory, and so on. As our
components can interact in potentially complex ways, grouping by
function rather than structure will help to tell a coherent story while
minimising the need for cross-referencing.

Our separation of concerns will therefore be

\begin{enumerate}
\def\labelenumi{\arabic{enumi}.}
\tightlist
\item
  Program execution and flow control
\item
  Graph management
\item
  Graph search
\end{enumerate}

\#\#\# Program execution and flow control

Certain basic components are common to most procedural programmable
machines, abstract or otherwise.

\begin{enumerate}
\def\labelenumi{\arabic{enumi}.}
\tightlist
\item
  a code store
\item
  a way to track where in the code store execution has reached
\item
  a stack of return addresses, to allow arbitrarily nested procedure
  calls
\end{enumerate}

The OILR machine in no different in this respect, but the need for
non-deterministic execution necessitates some additional machinery.

\#\#\#\#\# Program text \{-\} Executable code output from the compiler
is read-only. Machine instructions must not operate on this portion of
memory.

\begin{code}
    txt :: Program,
\end{code}

\#\#\#\#\# Program counter \{-\} The program counter \(PC\) stores the
address, within the text section, of the next instruction to be
executed.

\begin{code}
    pc :: Addr,
\end{code}

\#\#\#\#\#\# Return stack \{-\} The return stack \(RS\) is a list of
return addresses of rule- and procedure-calls. As \(RS\) has strict
last-in-first-out semantics, is not amenable to inspection or
modification by the compiled program, and is represented here as a list,
there is no need for an explicit stack pointer.

\begin{code}
    rs  :: [Addr],
\end{code}

\#\#\#\#\# Entropy-pool \{-\} The entropy-pool \(EP\) is a register that
returns a random boolean value each time it is read, as required to
implement GP2's non-deterministic flow-control instruction (see section
\ref{todo}).

\begin{code}
    ep :: EntropyPool,
\end{code}

\#\#\#\#\# Boolean flag \{-\} When we start implementing high-level flow
control instructions in section \ref{todo} we will find a need for a
record of whether the most recently executed rule succeeded or failed.
This record potentially needs to persist until the next rule-call. For
example, this information will be required by the instruction that ends
transactional code blocks (section \ref{todo}) and by conditional jumps
(section \ref{todo}).

A single success or failure can trigger multiple changes in program
behaviour, and such instructions may be remote from the site of the
original failure.

Rather than introducing an exception handling system, or passing return
values between rule and procedure calls, having a single global boolean
flag serves our purposes with minimal additional complexity.

\begin{code}
    bf  :: Bool,
\end{code}

As well being implicitly set by the success or failure of graph search
instructions, we will introduce instructions that allow the compiled
program to manipulate this value directly for situations where the
success of the previous rule must be over-ridden. An example of this
requirement is GP2's \texttt{skip} null-rule, which always succeeds.

\#\#\# Graph management

The components we need for managing the graph are:

\begin{enumerate}
\def\labelenumi{\arabic{enumi}.}
\tightlist
\item
  a place to store the host graph
\item
  a way to generate unique identifiers for new graph elements
\item
  a log of changes to the graph in case a transactional code block fails
  and needs to be rolled-back
\end{enumerate}

\#\#\#\#\# The host-graph \{-\} The \emph{host-graph} is the graph data
transformed by the instructions we will develop in section \ref{todo}.
It can be arbitrarily large, up to an implementation-defined (or
hardware-constrained) maximum number of graph elements. An
implementation should not place arbitrary restrictions on number of
nodes, or number of edges, only on total graph size.

The host graph only becomes available at run-time. It is the only type
of data in heap memory that is amenable to manipulation directly by the
compiled program.

\begin{code}
    g :: Graph,
\end{code}

\#\#\#\#\# Auto-increment register \{-\} \(AI\) is a global register
producing a non-repeating sequence of integers. It is used whenever we
need a unique identifier for a newly created graph element.

\begin{code}
    ai :: [ElemId],
\end{code}

\#\#\#\#\# The transaction stack \{-\} The \emph{transaction stack}
\(TS\) contains a log of changes made to the graph. This allows us to
undo changes to the graph should a transactional code block fail.

\begin{code}
    ts  :: [Change],
\end{code}

\#\#\# Graph search

Finally we need a supporting framework for searching the host graph.

\begin{enumerate}
\def\labelenumi{\arabic{enumi}.}
\tightlist
\item
  collections of signatures used by particular rules
\item
  a local register file to hold matched graph elements
\item
  a working register for holding intermediate results of searches and
  label arithmetic
\end{enumerate}

\#\#\#\#\# Search-spaces \{-\} Search spaces are read-only, and only
accessed by the program implicitly through the \texttt{BND} instruction.

\begin{code}
    ss  :: Spaces,
\end{code}

\#\#\#\#\# Local register file \{-\} The \emph{local register file}
\(regs\) is a per-rule storage area allocated on calling a rule before
any graph searching takes place, and deallocated once the rule has
completed.

\begin{code}
    regs :: RegFile,
\end{code}

\#\#\#\#\# Working register \{-\} The \emph{working register} \(WR\) is
the closest we have to a general-purpose register. Search operations
store a reference to candidate graph elements here and arithmetic
operators use \(WR\) as an accumulator for intermediate values. \(WR\)
can take a special null-value which is guaranteed to not be a valid
integer.

\begin{code}
    wr :: Maybe Int,
\end{code}

\#\#\#\#\# The failure stack \{-\} Lastly, the failure stack \(FS\)
records where in a rule execution should jump back to should a match
operation fail, including exiting the rule in the event that the rule
fails entirely.

This is not strictly necessary, but as we will see in section \ref{todo}
our graph search instructions are already complex, typically accepting
three arguments, and the presence of the fail-stack eliminates the need
for an extra jump-target parameter to be passed to each instruction.

Introducing an additional stack for back-tracking during graph search
does incur a small performance overhead at run-time, but the gains in
terms of ease of code-motion and simplification of the code generator,
make it a worthwhile trade-off (see section \ref{todo}).

\begin{code}
    fs :: [Addr] }
\end{code}

\#\#\# General notes

Some points to note about the design of the OILR machine described so
far.

\#\#\#\#\# Stacks \{-\} The OILR Machine has three special-purpose
stacks, each with different semantics.

All stacks are conceptually arbitrarily large, which is to say their
size is implementation-defined. Additionally none of the stacks is
amenable to direct manipulation by the program, and so I have chosen to
regard them semantically as lists in the operational semantics, and
therefore requiring no stack-pointers.

The maximum depth of the failure stack during any rule call is a
function of the size of the register file for that rule, and can
therefore be computed exactly at compile time (section \ref{todo}). It
should therefore never overflow.

Behaviour on overflow of the other two stacks is undefined.

\#\#\#\#\# Registers \{-\} The two special-purpose registers
\emph{auto-increment} and \emph{entropy pool} are both read-only from
the point of view of the program, in so far as they cannot be set using
any OILR machine instruction. Both are automatically updated by the
run-time system when read from.

\#\#\#\#\# Memory \{-\} The program text area is read-only, and is never
modified at run-time.

Search spaces are read by the internals of the run-time system, but
their contents are provided by the compiler and immutable at run-time.

The host graph is read-write, and its contents may be searched and
modified using the OILR instruction set.

\#\#\# Commentary

As can be seen from figure \ref{todo}, the resulting machine state is
quite complex, possessing three stacks, one global flag, three global
registers plus a per-rule register file, and a heap containing program
code, a set of program-specific search spaces and the host graph.

Some of this complexity will disappear when in section \ref{todo} we map
the OILR machine onto a run-time system in a lower-level language. For
example if we choose our rule representation carefully, the return stack
\(RS\) and program counter \(PC\) map neatly on to the corresponding
features of the underlying physical machine, and the working register
\(WR\) becomes implicit in the return values of the functions used to
implement our instructions.

\subsection{Building the instruction
set}\label{building-the-instruction-set}

Now let us now build an instruction set for the OILR machine.

Some of the things we wish to express in an instruction -- notably graph
search -- turn out to be quite complex. Others share significant
functionality. In the interests of clarity and not brevity it will
therefore be useful to abstract some of the functionality contained
within certain instructions into separate helper functions. In
situations where this is appropriate we shall assume the existence of
these helper functions, with a forward-reference their definition in the
following section.

\#\#\#\#\# Instructions \{-\} Instructions are the interface by which
the outside world interacts with the OILR machine. They are typically
the composition of one or more micro-ops, and the smallest subdivision
of code emitted by the compiler.

Example: an operation that searches the graph for a node with particular
characteristics, and then binds that node into a machine register,
jumping back to a previous instruction on failure. The smallest
instruction is one micro-operation in size, while the largest is eight.

\#\#\#\#\# Helper-functions \{-\} Primitives describe functionality
shared between different instructions.

For example a function that takes a \texttt{Graph} and an
\texttt{ElemId}, and returns the corresponding graph element, would be
considered a helper-function.

\#\#\# Structure of this section

Instructions will be motivated and described. Following this we will
look at the implementation of the helper functions we introduced in the
Instructions section.

Table \ref{todo} summarises the numbers of each type of operation.

\input{Tables/instruction_count.tex}

Table: Comparison of number of primitives, micro-operations and
instructions

\subsection{The instruction set}\label{the-instruction-set}

\#\#\# The type of an instruction

First let us consider the type of our instruction decoding routine.

\texttt{decode} should take an instruction \texttt{Instr} and return an
operation that transforms a virtual machine state \texttt{VM} into a
modified virtual machine state.

\begin{code}
decode :: Instr -> VM -> VM
\end{code}

\#\#\# Trivial instructions

In developing an instruction set, let us begin with the three simplest
operations.

\#\#\#\#\# NOP \emph{no-operation} \{-\}

As an illustrative example, let us describe a no-op instruction called
\texttt{NOP}, which returns the unmodified abstract machine.

\begin{code}
decode NOP vm = vm
\end{code}

\#\#\#\#\# TRU \emph{set bf to True}, FLS \emph{set bf to False} \{-\}

Our next examples allow us to programmatically set the global boolean
flag register \(bf\) to true and false respectively.

\begin{code}
decode TRU vm = vm { bf=True }
decode FLS vm = vm { bf=False }
\end{code}

\#\#\# Program structure \& jump labels

Now that we have seen some trivial examples, let us introduce
instructions for controlling the flow of program execution.

The first two program structure `instructions' serve as labels for
jumps, rules and procedures. In reality they represent code addresses
rather than run-time behaviour, and in a full compiled implementation
they can be elided from the instruction stream entirely. Nevertheless in
the semantics we will use them as markers to remove the need to maintain
a separate table of addresses of jump targets for branches.

Because they have no run-time behaviour we can also represent them using
the \texttt{nop} micro-operation.

\#\#\#\#\# DEF \emph{rule or procedure definition} \{-\}

\begin{code}
decode (DEF _) vm = vm
\end{code}

\#\#\#\#\# TAR \emph{branch target} \{-\}

\begin{code}
decode (TAR _) vm = vm
\end{code}

\#\#\# Procedure-level branching

We will find that we need several different types of branching operation
at the procedure level. Branching within rules is implicit within the
behaviour of matching and condition checking instructions, and will be
discussed separately in section \ref{todo}.

Four types of branching operation are necessary:

\begin{enumerate}
\def\labelenumi{\arabic{enumi}.}
\tightlist
\item
  branch unconditionally
\item
  branch if \(BF\) is true
\item
  branch if \(BF\) is false
\item
  branch based on a value read from the entropy pool
\end{enumerate}

Each of the following branch instructions shares the common behaviour of
converting a textual label into an integer address. We abstract this out
into the \texttt{findBranchTarget} helper function, detailed in section
\ref{todo}.

\#\#\#\#\# BRN \emph{branch unconditionally} \{-\}

Find the address of the label in the program text, and set the
program-counter.

\begin{code}
decode (BRN jl) vm@(VM {txt}) =
    vm { pc=findBranchTarget jl txt }
\end{code}

\#\#\#\#\# BNZ \emph{branch if non-zero} \{-\}

Branch conditionally, jumping to \texttt{jl} only when \(BF\) is true.

\begin{code}
decode (BNZ jl) vm@(VM {bf,txt}) =
    if bf then vm {pc=pc'} else vm
    where pc' = findBranchTarget jl txt
\end{code}

\#\#\#\#\# BRZ \emph{branch if zero} \{-\}

We will also need to branch conditionally, jumping to \texttt{jl} only
when \(BF\) is false.

\begin{code}
decode (BRZ jl) vm@(VM {bf,txt}) = 
    if bf then vm else vm {pc=pc'}
    where pc' = findBranchTarget jl txt
\end{code}

\#\#\#\#\# BRA \emph{branch randomly} \{-\}

Finally for branching, we need an instruction to branch fifty percent of
the time, determined at random. This is necessary to implement the
program-OR feature of the GP2 language (see section \ref{todo}), and is
the reason for the \(EP\) register.

\begin{code}
decode (BRA jl) vm@(VM {ep=x:xs,txt}) =
    if x then vm' { pc=pc' } else vm'
    where pc' = findBranchTarget jl txt
          vm' = vm { ep=xs }
\end{code}

\#\#\# Rule and procedure calls

Simple function calls work in much the same way in the OILR machine as
in typical computer architectures: a \texttt{CALL} instruction pushes
the current value of the program counter onto a stack before branching
unconditionally to the specified label. Rules and procedures are treated
identically.

GP2 also supports a second type of call -- \emph{as long as possible}
(\texttt{ALAP}) which calls the same rule or procedure repeatedly until
it fails (which may never terminate). The other significant observation
is that as long as possible calls that return, always do so successfully
(even if the first call fails; think of this as analogous to the
\texttt{*} operation in regular expressions, which matches zero or more
occurrences). For this reason the OILR machine's boolean flag must be
reset to true after any ALAP call.

We already have the conditional branching instructions necessary to
implement ALAP calling behaviour, however as there are run-time
optimisations we can apply specifically to ALAP rule calls it will prove
valuable to have some way to readily identify such sites in the code. We
will therefore introduce an extra instruction that follows the call and
implements the ALAP looping behaviour.

\#\#\#\#\# ONCE \emph{call rule or procedure} \{-\}

\texttt{ONCE} calls the rule or procedure identified by \texttt{jl},
unconditionally executing it exactly once. It leaves the global boolean
flag in the state it was in when \texttt{jl} returned.

\begin{code}
decode (ONCE jl) vm@(VM {txt,pc,rs}) =
    vm {pc=pc',rs=pc:rs}
    where pc' = findBranchTarget jl txt
\end{code}

\#\#\#\#\# ALAP \emph{repeated rule or procedure call for as long as
possible} \{-\}

\texttt{ALAP} repeatedly calls the rule or procedure identified by
\texttt{jl}, for as long as it completes successfully (by setting the
return address to the \texttt{ALAP} instruction instead of its
successor), then resets the boolean flag to true before continuing.

There is no guarantee that a call to \texttt{ALAP} will terminate.

\begin{code}
decode (ALAP jl) vm@(VM {txt,pc,rs,bf}) =
    if bf then vm { rs=(pc-1):rs, pc=pc' } else vm {bf=True}
    where pc' = findBranchTarget jl txt
\end{code}

We only need a single unconditional return instruction. Unlike branching
it is not necessary to return conditionally or randomly.

\#\#\#\#\# RET \emph{return} \{-\}

The return instruction pops the top of the return stack to the program
counter.

\begin{code}
decode RET vm@(VM {rs=a:as}) = vm {pc=a, rs=as}
\end{code}

\#\#\# Transactional code blocks

To implement GP2's procedure-level back-tracking, we need an
infrastructure for handling transactions on the host graph.

Because transactions can be nested to arbitrary depth, we need some way
of knowing where the part of the stack representing the innermost
transaction ends. For this purpose we can assume a distinctive sentinel
value \texttt{tSentinel} which is always pushed at the start of a new
transaction, and removed at the end. We shall provide a concrete
definition for this in section \ref{todo}.

There are two possible ways to end a transaction; conditional or
unconditional roll-back. The latter is necessitated by GP2's \texttt{if}
construct, which always discards the result of its predicate (see
section \ref{todo}). Let us abstract the shared behaviour into a
helper-function, \texttt{rollback}, defined on page \ref{todo}.

\#\#\#\#\# TRN \emph{begin transaction} \{-\}

To start a back-tracking section let us just push the sentinel value
onto the transaction stack.

\begin{code}
decode TRN vm@(VM {ts}) = vm { ts=tSentinel:ts }
\end{code}

\#\#\#\#\# ETR \emph{end transaction} \{-\}

There is a little additional complexity to ending a transactional code
block. The most common case we have to deal with is a conditional
commit; if the boolean flag is true, indicating that the most recently
executed rule completed successfully, then we commit the transaction,
otherwise we restore the state of the graph at the start of the
transactional section.

\begin{code}
decode ETR vm@(VM {bf,ts,g}) = vm { ts=tail ts', g=g' }
    where (tr,ts') = break (/=tSentinel) ts
          g'  = case bf of
                True -> g
                False -> rollback g tr
\end{code}

\#\#\#\#\# BAK \emph{unconditionally roll-back transaction} \{-\}

A rarer case, but still necessary to implement GP2's \texttt{if} block,
which always discards the results of its predicate term, is an
unconditional \texttt{rollback} micro-op.

\begin{code}
decode BAK vm = vm { ts=tail ts', g=g' }
    where (tr, ts') = break (/=tSentinel) ts
          g' = rollback g tr
\end{code}

\#\#\# Graph search instructions

Instructions within rules that search the host graph exhibit complex
behaviour. Each needs to perform five tasks:

\begin{enumerate}
\def\labelenumi{\arabic{enumi}.}
\tightlist
\item
  unbind previously bound graph elements
\item
  retrieve matches from a search space
\item
  bind matched elements to local registers
\item
  set the global boolean flag to indicate success or failure
\item
  manipulate the failure stack:

  \begin{enumerate}
  \def\labelenumii{\alph{enumii})}
  \tightlist
  \item
    on success, push an address onto the failure stack
  \item
    on failure, jump back to the address popped from the failure stack,
    either returning to the previous match instruction, or exiting the
    rule entirely if there is no previous match instruction
  \end{enumerate}
\end{enumerate}

Some of this shared behaviour can be abstracted out into helper
functions. \texttt{bind} and \texttt{unbind}, \texttt{fail},
\texttt{fillFromSS}.

Faced with the complexity of these instructions, both in terms of number
of arguments, and their semantics, one might ask the question of whether
or not the branch-on-failure behaviour constitutes a separate
instruction. There is not a clear answer, but noting that there is no
situation in which a match instruction is not immediately followed by a
conditional branch, we shall treat the branch as part of the matching
operation and accept more complex instructions in exchange for a
reduction in length of the instruction stream (and the opportunity for a
more efficient implementation of the compound operation in the run-time
system).

\#\#\#\#\# BND \emph{bind node} \{-\}

Our most basic matching instruction is already distressingly
complicated. In common with later match instructions has three possible
behaviours.

\begin{enumerate}
\def\labelenumi{\arabic{enumi}.}
\item
  the target register is empty, indicating that either this instruction
  has not previously run in this invocation of the rule, or that the
  previous time we visited this failed back to a previous point and we
  are visiting this match instruction from a new matching state. In both
  cases the expected behaviour is the same; populate the register from
  the search space and bind the first element.
\item
  the target register is a singlet list, indicating that the previously
  bound node was the last possibility and we have failed to find a
  match. In this case the prescribed behaviour is to fail back to the
  previous match instruction.
\item
  the target register contains two or more elements, indicating that
  there is at least one more possible match to try. In which case bind
  the next node.
\end{enumerate}

There is one further complication: If \texttt{fillFromSS} finds that the
search space contains no unbound nodes, then the instruction fails. This
contingency will be checked in the definition of \texttt{fillFromSS}.

\begin{code}
decode (BND r ss) vm =
    case getReg regs r of
        []   -> (pushF . bind r . fillFromSS r ss) vm
        [n]  -> (fail . unbind r ) vm
        ns   -> (pushF . bind r . unbind r) vm
\end{code}

\#\#\#\#\# BOE \emph{bind out-edge} \{-\}

Now, given two nodes bound in registers, we wish to find an out-edge
from the first to the second. In this case we do not have a pre-computed
search space, but instead use the intersection of the out-edges of the
source node and the in-edges of the target.

\begin{code}
decode (BOE r0 r1 r2) vm =
    case getReg regs r0 of
        []   -> (pushF . bind r0 . fillFromBtw r0 r1 r2) vm
        [n]  -> (fail . unbind r0) vm
        ns   -> (pushF . bind r0 . unbind r0) vm
\end{code}

\#\#\#\#\# BON \emph{bind out-edge and node} \{-\}

Suppose that we have a node, and our search plan requires us to follow
an out-edge, and match both the edge and the node on the other end.

Effectively we are combining the behaviour of the previous two
instructions, however as we find the edge before the target node, this
requires subtly different behaviour.

\begin{Shaded}
\begin{Highlighting}[]
\FunctionTok{!--} \DataTypeTok{TODO}\FunctionTok{:} \NormalTok{outA needs to consider the availability }\KeywordTok{of} \NormalTok{the target node as well as the edge }\FunctionTok{-->}
\end{Highlighting}
\end{Shaded}

\begin{code}
decode (BON r0 r1 r2) vm = 
    case getReg regs r0 of
        []  -> (pushF . bind r0 . bind r1 . fill2FromOutA r0 r1 r2) vm
        [n] -> (fail . unbind r0 . unbind r1) vm
        ns  -> (pushF . bind r0 . bind r1 . unbind r0 . unbind r1) vm
\end{code}

\#\#\#\#\# BIN \emph{bind in-edge and node} \{-\}

Let us do the same again for in-edges to an already bound node.

\begin{code}
decode (BIN r0 r1 r2) vm =
    case getReg regs r0 of
        []  -> (pushF . bind r0 . bind r1 . fill2FromInA r0 r1 r2) vm
        [n] -> (fail . unbind r0 . unbind r1) vm
        ns  -> (pushF . bind r0 . bind r1 . unbind r0 . unbind r1) vm
\end{code}

\#\#\#\#\# BLO \emph{bind loop on node} \{-\}

Giving looped-edges special status will facilitate some performance
tuning opportunities later when we come to write the run-time system.

\begin{code}
decode (BLO r0 r1) vm = 
    case getReg regs r0 of
        []   -> (pushF . bind r0 . fillFromLoops r0 r1) vm
        [n]  -> (fail . unbind r0) vm
        ns   -> (pushF . bind r0 . unbind r0) vm
\end{code}

\#\#\#\#\# BED \emph{bind bidi-edge}, BEN \emph{bind bidi-edge and node}
\{-\}

The following two instructions are a convenience for supporting GP2's
``bidi'' edge matching behaviour modifier, which allows matching an edge
in either direction between two nodes. They could both be implemented
using existing conditional branching machinery, but including them as
instructions simplifies code generation and makes the generated code
more uniform, by avoiding the need to mix the stack-based branching of
rules with the explicit branching used in procedures.

\begin{code}
decode (BED r0 r1 r2) vm =
    case getReg regs r0 of
        []   -> (pushF . bind r0 . fillFromA r0 r1 r2) vm
        [n]  -> (fail . unbind r0) vm
        ns   -> (pushF . bind r0 . unbind r0) vm

decode (BEN r0 r1 r2) vm =
    case getReg regs r0 of
        []  -> (pushF . bind r0 . bind r1 . fill2FromA r0 r1 r2) vm
        [n] -> (fail . unbind r0 . unbind r1) vm
        ns  -> (pushF . bind r0 . bind r1 . unbind r0 . unbind r1) vm
\end{code}

\#\#\# Conditions

In many situations the above graph search instructions will be
sufficient to identify nodes and edges that match elements of the
program left-hand-side, because of the way search spaces are built only
from nodes that have appropriate structural characteristics.

However the fact that we have an alphabet of theoretically unbounded
size in the integer labels that our subset of GP2 supports means that we
cannot realistically guarantee total certainty in all situations.
Furthermore, GP2 permits matching of labels based on arbitrarily complex
arithmetic relationships to other labels.

Marks on edges are also an issue -- this information is not encoded in
the edge matching and following instructions.

For these reasons we are going to require a set of instructions to run
complex post-hoc tests on graph elements that we have already identified
as candidates using the instructions from the previous section.

Like matching instructions, graph conditions modify the boolean flag
and, on failure, invalidate part of the match by setting the program
counter to a previous match instruction using the failure stack. The
graph itself and local registers are left unmodified, and these
instructions do not push their own addresses to the failure stack,
because conditions only need to be re-checked after the contents of a
register has changed.

\#\#\#\#\# NEC \emph{negative edge condition} \{-\}

A common requirement in graph transformation is checking for the
\emph{absence} of an edge. This is a simplified version of the
\texttt{BOE} instruction (see \ref{todo}).

\begin{code}
decode (NEC r0 r1) vm =
    case btw r0 r1 of
        [] -> vm
        _  -> fail vm
\end{code}

\#\#\#\#\# CME \emph{check marked element} \{-\}

Search spaces for nodes already consider the colour of the node's mark,
meaning that any node bound by \texttt{BND} is assured to be of a
compatible colour. Unfortunately this guarantee does not extend to nodes
found by following edges, or to the edges themselves.

Although there is a wildcard that matches any mark, GP2 syntax does not
permit binding colours to variables or comparing colours of different
nodes. Thus we only need compare the colour of a bound graph element to
a constant.

\begin{code}
decode (CME r c) vm@(VM {regs}) =
    if mark . head . getReg regs r == c 
        then vm
        else fail vm
\end{code}

\#\#\#\#\# CLX \emph{check label exists} \{-\}

The issue is more complex with labels. Guaranteeing the presence or
absence of a label during compile-time search space construction is
straightforward, as we will see when we discuss the process in section
\ref{todo}. However for edges and for the nodes we reach by following
them, we must explicitly test for the existence (or non-existence) of a
label.

\begin{code}
decode (CLX r bool) vm@(VM { regs }) =
    if labelled . head . getReg reg r == bool
        then vm 
        else fail vm
\end{code}

\#\#\#\#\# CLB \emph{check label} \{-\}

Unfortunately as the labels themselves are drawn from a potentially
unbounded alphabet (integers), \emph{a priori} guarantees concerning a
label's actual value are beyond our reach. For this reason, explicit
tests of labels are potentially required to assure ourselves of the
correctness of a match, even after a \texttt{BND} instruction.

\begin{code}
decode (CKL r n) vm =
    if label . head . getReg reg r == Just n
        then vm
        else fail vm
\end{code}

\begin{Shaded}
\begin{Highlighting}[]
\FunctionTok{!--} \DataTypeTok{TODO}\FunctionTok{:} \NormalTok{there's a host }\KeywordTok{of} \NormalTok{others that we aren't testing}\FunctionTok{.} \FunctionTok{:}\NormalTok{( for example relative labels }\FunctionTok{-->}
\end{Highlighting}
\end{Shaded}

\#\#\# Graph element creation

Compared to the matching operations described above in section
\ref{todo} the instructions to introduce new graph elements are
straightforward. The only subtleties here are that we a) must have
reserved a register to accommodate the new element, and b) must bind the
new element to that register, so that later instructions can potentially
operate on the new element.

\#\#\#\#\# ABN \emph{add and bind node} \{-\}

Create a new node and bind it to register \texttt{r}.

\begin{code}
decode (ABN r) vm = (bind r . createN) vm
\end{code}

\#\#\#\#\# ABE \emph{add and bind edge} \{-\}

Create a new edge from the node bound in \texttt{r1} to the node bound
in \texttt{r2}, and bind the resulting edge in \texttt{r0}.

\begin{code}
decode (ABE r0 r1 r2) vm = (bind r0 . createA r1 r2) vm
\end{code}

\#\#\#\#\# ABL \emph{Add and bind loop} \{-\}

Create a new looped-edge on the node bound in \texttt{r1}, and bind the
new edge in \texttt{r0}.

\begin{code}
decode (ABL r0 r1) vm = (bind r0 . createA r1 r1) vm
\end{code}

\#\#\# Graph element deletion

Deleting graph elements is similarly straightforward. Note that, from
the point of view of the semantics, these three instructions are
identical. However, when we come to implement the run-time system in
section \ref{todo} we shall find it useful to distinguish between
deletion of nodes, edges and loops due to the different `house-keeping'
requirements and invariants associated with each type of graph element.

\#\#\#\#\# DBN \emph{delete bound element}, DBL \emph{delete bound
loop}, DBE \emph{delete bound edge} \{-\}

\begin{code}
decode (DBN r) vm = ( deleteE r . unbind r ) vm
decode (DBL r) vm = ( deleteE r . unbind r ) vm
decode (DBE r) vm = ( deleteE r . unbind r ) vm
\end{code}

\#\#\# Graph element attribute setting

The final type of modification we find in rules is that of adjusting the
attributes -- mark, label, rootedness\ldots{} -- of graph elements.

\#\#\#\#\# RBN \emph{set root flag on bound node} \{-\}

Sets the root-flag on the node bound in \texttt{r} to be the boolean
value \texttt{b}.

\begin{code}
decode (RBN r b) vm = ( setR r b ) vm
\end{code}

\#\#\#\#\# CBL \emph{set colour of bound element} \{-\}

Sets the mark on the element -- either node or edge -- bound in
\texttt{r} to the colour \texttt{c}. It is the responsibility of the
compiler to only emit marks appropriate to the type of graph element
being modified.

\begin{code}
decode (CBL r c) vm = ( setC r c ) vm
\end{code}

\#\#\#\#\# LBL \emph{label bound element} \{-\}

Sets the label on the element bound in \texttt{r} to the integer value
\texttt{n}.

\begin{code}
decode (LBL r n) vm = ( setB r . lit n ) vm
\end{code}

\begin{Shaded}
\begin{Highlighting}[]
\FunctionTok{!--} \DataTypeTok{TODO}\FunctionTok{:} \NormalTok{what about label deletion}\FunctionTok{?} \FunctionTok{-->}
\end{Highlighting}
\end{Shaded}

\#\#\# Miscellaneous instructions

Allocate a local register file of size \texttt{n}.

\begin{code}
decode (REGS n) vm@(VM {regs}) =
    vm { regs = regs' ++ regs }
    where regs' = [ (n, []) | n <- [1..] ] 
\end{code}

\begin{Shaded}
\begin{Highlighting}[]
\FunctionTok{!--} \NormalTok{todo}\FunctionTok{:} \NormalTok{check [}\DecValTok{0}\FunctionTok{..}\NormalTok{] or [}\DecValTok{1}\FunctionTok{..}\NormalTok{]}\FunctionTok{???} \FunctionTok{-->}
\end{Highlighting}
\end{Shaded}

Unbind elements bound into the register file by this rule, where
\texttt{n} is the size of the register file.

\begin{code}
decode (UBN n) vm@(VM {regs,g}) =
    vm { regs=regs', g=g' }
    where (xs, regs') = splitAt n regs
          g' = [ e | (e:_) <- xs ] ++ g 
\end{code}

\#\# Helper functions

\texttt{bind} takes the graph element identified by the value in \(WR\),
removes it from the host graph in order to preserve match injectivity,
and places it in the specified register.

\begin{code}
unbind :: RegId -> VM -> VM
unbind r vm@(VM {regs,g}) = vm {regs=regs',g=e:g}
    where regs' = setReg r es regs
          e:es  = getReg r regs

bind :: RegId -> VM -> VM
bind r vm@(VM {regs,g}) = vm { g=g' }
    where g' = g \\ [e]
          e:es  = getReg r regs
\end{code}

\texttt{getReg} takes a register id and local register file and returns
the contents of the register. Attempting to get the value of an empty
local register is an error.

\begin{code}
getReg :: RegId -> RegFile -> [Elem]
getReg r rs = definiteLookup r rs
\end{code}

Of course, we need to place a value into a register.

\begin{code}
setReg :: RegId -> [Elem] -> RegFile -> RegFile
setReg r val rs = [ (k,v') | (k,v) <- rs
                  , let v' = if r==k then val else v ]
\end{code}

\#\#\# Putting it all together

The only thing left to do is to install the OILR machine's utterly dead
but still beating heart, and make the whole shambolic pile stutter into
a twisted parody of life, making a mockery of all that is good and
wholesome in the world.

\texttt{fetch} looks up the instruction identified by the program
counter \(PC\) in the text section of the heap, and passes this
instruction to the evaluator \texttt{decode}. The program counter is
incremented, and fetch recurses.

\begin{code}
fetch :: VM -> VM
fetch vm@(VM {pc,txt}) = ( decode i ) vm {pc=pc+1}
    where i = head $ drop pc txt
\end{code}

We now have a complete operational semantics for the OILR machine.

\subsection{Discussion}\label{discussion}

The semantics of the OILR machine as not as simple as hoped. Particular
areas of complexity occur in rules rather than procedures, and result
from tracking the states of multiple search spaces while navigating a
looping path through the match instructions.

There are undesirable characteristics to be found in the instruction
stream: the \texttt{FIND} and \texttt{FOLO} search instructions are
always preceded by a \texttt{SF*} search-space reset instruction.
Ideally we would like to combine these behaviours. As we will see in
section \ref{todo} this is quite possible in a low-level implementation
of the instruction set, but relies on pointers and state variables, so
is hard to express mathematically.

\#\#\# Future work

It became apparent while writing this chapter that, by extending search
spaces with run-time logic it would be possible to simplify the
instruction stream. Adding such a filter would facilitate the
elimination of most (possibly all) post-hoc tests in the rules, which
would prevent some unnecessary back-tracking. The benefit of such a step
would be heavily dependent on the program being run. The potential gains
of this modification will be explored in section \ref{todo}.

\begin{Shaded}
\begin{Highlighting}[]
\FunctionTok{!--} \NormalTok{vim}\FunctionTok{:} \NormalTok{set filetype}\FunctionTok{=}\NormalTok{pandoc spell lbr et }\FunctionTok{:} \FunctionTok{-->}
\end{Highlighting}
\end{Shaded}

