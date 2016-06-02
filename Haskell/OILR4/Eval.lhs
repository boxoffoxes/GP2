
\section{An operational semantics for the OILR Machine}


In designing our abstract machine for graph transformation, an operational semantics is a useful tool for debugging our machine design and drawing a clear division between concerns at the abstract machine level, and those at the implementation level.

While an algebraic specification is useful in its own right, implementing that specification in a sufficiently mathematical programming language, not only gives us the benefits described above, but also allows us to execute our specification and test it for correctness against the reference interpreter we described in section \ref{referenceinterpreter}. Furthermore, if we select the language carefully, its compiler will identify many potential typographical errors.

Haskell is a natural choice for this kind of operational semantics. We can build on top of our existing parser and graph representation adding abstractions where necessary, and end up with a semantics that is broadly familiar in appearance to a reader accustomed to reading algebraic specifications.


\subsection{Mnemonic letters used in the OILR machine}

Before writing any code, let's define a few common mnemonics that will be re-used as we build the instruction set, and again later in the compiler and run-time system. This will help to ensure consistent naming.

A
  ~ an edge in the host graph, mnemonic for _arc_, as we use E for a graph element.
C
  ~ refers to the colour of a host graph node, or the mark of an host graph edge.
E
  ~ any element of the host graph, either node or edge.
I
  ~ an in-edge, directed towards a particular node.
L
  ~ a looped edge, starting and terminating at the same node in the host graph.
N
  ~ a node in the host graph.
O
  ~ an out-edge, pointing away from a particular node.
R
  ~ rootedness, a node with the root-flag set.
V
  ~ refers to a label on either a node or an edge, short for _value_ as L is already used for looped edges.


> {-# LANGUAGE NamedFieldPuns #-}
> module OILR4.Eval where
> 
> import OILR4.Instructions hiding (Src, Tgt, Sid)
> 
> import GPSyntax
>
> import Mapping
> import Data.List
> import Data.Maybe

Our machine state is superficially quite complex, possessing three stacks, two global flags, two global registers plus a per-rule register file, and a heap containing program code, a set of indices, a set of program-specific search spaces, and a host graph.

> data VM = VM { rs  :: [Maybe ElemId],   fs :: [Int],   ts  :: [Int]
>              , bf  :: Bool,             tf :: Bool
>              , pc  :: Int,            regs :: RFile
>              , wr  :: Maybe ElemId,     ec :: ElemId
>              , txt :: [Instr],        inds :: Index
>              , ss  :: Mapping Int Space, g :: Graph }

As we will see later, some of this complexity disappears when we map the OILR machine onto a run-time system in a lower-level language. For example if we choose our rule representation carefully, the return stack $RS$ and program counter $PC$ map neatly on to the corresponding features of the underlying physical machine, and the working register $WR$ becomes implicit in the return values of the functions used to implement our instructions.

GP2 semantics differentiate between the structure of a node- and edge-label, for our purposes however, a shared data-type will suffice; an attempt to set the $root$ flag of an Edge, or the colour of a node to `Dashed` would be symptomatic of a bug in our compiler.

> type ElemId = Int
> type RegId = Int
> type Graph = [Elem]
> data Elem  = Nod ElemId Label Rootedness
>            | Edg ElemId Label Src Tgt
> type Label = (Maybe Int, Colour, Bound)
> type Rootedness = Bool
> type Bound = Bool
> type Src = ElemId
> type Tgt = ElemId
> type Space = [ElemId]
> type Addr = Int

A search space is a list of `Index` ids.

> type SSpc  = Mapping SpcId [ElemId]
> type SpcId = Int

And an index is a list of graph element identifiers.

> type Index = Mapping Iid [ElemId]
> type Iid = Int

> type MicroOp = VM -> VM

Now we know how our data is structured, let's define some micro-operations, from which our instructions will be built. Micro-ops all have similar signatures, ending `VM -> VM`. In this way building instructions is a straightforward case of composing the right micro-operations.

> orFail :: MicroOp
> orFail vm@(VM {fs=(addr:as)}) = decode $ vm { pc=addr, fs=as }

> pushFS :: MicroOp
> pushFS vm@(VM {fs,pc}) = vm { fs=pc:fs }

> decode :: VM -> VM
> decode vm@(VM {pc,txt}) = ( incPC . evalI i ) vm
>     where i = head $ drop pc txt

> incPC :: MicroOp
> incPC vm@(VM {pc}) = vm { pc=pc+1 }

> idOf :: Elem -> ElemId
> idOf (Nod i _ _) = i
> idOf (Edg i _ _ _) = i

> getElemById :: ElemId -> VM -> Elem
> getElemById id (VM {g}) = case find (\l -> idOf l == id) g of
>                               Just l  -> l
>                               Nothing -> error "Compiler error: invalid id requested"

> getElemByReg :: RegId -> VM -> Elem
> getElemByReg id vm = getElemById (getReg id vm) vm

> changeElem :: Elem -> VM -> VM
> changeElem chg@(Nod id _ _) vm@(VM {g}) = vm { g=g' }
>       where g' = [ l' | l <- g , let l' = if idOf l == id then chg else l ]

Bind the element in `WR` to register r.


> bind :: RegId -> MicroOp
> bind r vm@( VM {wr,g,regs} ) = setReg r wr $ vm {g=g'}
>       where g' = [ l' | l <- g, let l' = if idOf l == lid then bind' l else l ] 
>             bind' (Nod id (n,c,False) r)   = Nod id (n,c,True) r
>             bind' (Edg id (n,c,False) s t) = Edg id (n,c,True) s t
>             lid = getReg r vm

> unbind :: RegId -> MicroOp
> unbind r vm@(VM {g}) = changeElem (setBound (getElemByReg r vm) False) vm

> notBF :: VM -> VM
> notBF vm = vm { bf = not (bf vm) }

> setBFFromWR :: VM -> VM
> setBFFromWR vm@(VM {wr}) = vm { bf=isJust wr }

> setBF :: Bool -> VM -> VM
> setBF b vm = vm { bf=b }

> resetSS :: SpcId -> VM -> [ElemId]
> resetSS s vm = error "not implemented"

> setSpc :: SpcId -> [ElemId] -> VM -> VM
> setSpc s ns vm@(VM {ss}) = vm { ss=ss' }
>       where ss' = [ (id, spc') | (id, spc) <- ss, let spc' = if id==s then ns else spc ]

> ssNext :: SpcId -> VM -> VM
> ssNext s vm = ( setSpc s ns ) $ vm { wr = n}
>       where (n, ns) = case spc of
>                      []     -> (Nothing, resetSS s vm)
>                      (id:ns) -> (Just id, ns)
>             spc = definiteLookup s (ss vm)


`getReg` is an API function, not a micro-op, as it does not have type `VM -> VM`

> getReg :: RegId -> VM -> ElemId
> getReg r vm = fromJust $ definiteLookup r (regs vm)

> setReg :: RegId -> Maybe ElemId -> VM -> VM
> setReg rid lid vm@(VM {regs,wr}) = vm { regs=regs' }
>       where regs' = [ (id, v') | (id, v) <- regs, let v' = if rid==id then lid else v ]


> setRoot :: Elem -> Bool -> Elem
> setRoot (Nod id l _) b = Nod id l b
> setRoot _ _ = error "Compiler error: tried to set root flag on an edge."

> setColour :: Elem -> Colour -> Elem
> setColour elem c = case elem of
>                      Nod id (l,_,b) r   -> Nod id (l,c,b) r
>                      Edg id (l,_,b) s t -> Edg id (l,c,b) s t
                
> setLabel :: Elem -> Int -> Elem
> setLabel elem n = case elem of
>                       Nod id (_,c,b) r   -> Nod id (Just n, c, b) r
>                       Edg id (_,c,b) s t -> Edg id (Just n, c, b) s t

> setBound :: Elem -> Bool -> Elem
> setBound elem bool = case elem of
>                       Nod id (l,c,b) r   -> if b==bool then error "Compiler error: bound-flag unmodified on node" else Nod id (l, c, bool) r
>                       Edg id (l,c,b) s t -> if b==bool then error "Compiler error: bound-flag unmodified on edge" else Edg id (l, c, bool) s t

> edgeTest :: RegId -> RegId -> VM -> VM
> edgeTest rs rt vm = case find (edge (getReg rs vm) (getReg rt vm)) (g vm) of
>                           Nothing -> vm { bf = False }
>                           Just e  -> vm { bf = True }
>       where edge :: ElemId -> ElemId -> Elem -> Bool
>             edge s t (Edg _ _ src tgt) | src==s && tgt==t = True
>             edge _ _ _ = False


`edgeBtw` searches the graph for an unbound edge between nodes bound in two registers, storing the result in `wr`.

> edgeBtw :: RegId -> RegId -> MicroOp
> edgeBtw s t vm@(VM {g}) = vm { wr = Just (idOf e) }
>       where e = find (edge (getReg s vm) (getReg t vm)) g
>             edge :: Src -> Tgt -> Elem -> Bool
>             edge s t e@(Edg _ _ x y) | x==s && y==t = True
>             edge s t _ = False

Next we want to be able to introduce nodes to the graph. `newNode` creates such a node, and places a reference to the newly created node in `wr`.

> newNode :: MicroOp
> newNode vm@(VM {g,wr,ec}) = vm {g=n:g, wr=Just ec, ec=ec+1}
>       where n  = Nod ec (Nothing, Uncoloured, False) False

Similarly `newEdge` introduces an edge from the node bound in register `sr` to the node bound in register `tr`, storing the new graph element in the working register.

> newEdge :: RegId -> RegId -> MicroOp
> newEdge sr tr vm@(VM {g,wr,ec}) = vm {g=e:g, wr=Just ec, ec=ec+1}
>       where e  = Edg ec (Nothing, Uncoloured, False) src tgt
>             src = getReg sr vm
>             tgt = getReg tr vm

We also find it useful to define a micro-operation to delete a graph element bound to a named local register.

> delElem :: Reg -> MicroOp
> delElem r vm@(VM {g}) = vm { g=g' }
>       where g'  = [ l | l <- g , idOf l /= did ]
>             did = getReg r vm



> source :: RegId -> RegId -> MicroOp
> source dr edg vm = error "not implemented"
> target :: RegId -> RegId -> MicroOp
> target dr edg vm = error "not implemented"


`outE` searches the for an unbound edge in the set of edges that have the node bound in local register `src` as their origin. The result of this search is stored in `wr`.

> outE :: RegId -> MicroOp
> outE src vm = error "not implemented"


`inE` is the dual to `outE`, which searches instead for unbound edges terminating at the node bound in register `tgt`. Again the result is stored in `wr`.

> inE :: RegId -> RegId -> MicroOp
> inE dr tgt vm = error "not implemented"


`loopE` retrieves and unbound loop that starts and ends in the node bound in register `r`.

> loopE :: RegId -> RegId -> MicroOp
> loopE sr vm = error "not implemented"






> setL :: RegId -> Int -> MicroOp
> setL r n vm = changeElem l' vm
>       where l' = setLabel (getElemByReg r vm) n

> setC :: RegId -> Colour -> MicroOp
> setC r c vm = changeElem l' vm
>       where l' = setColour (getElemByReg r vm) c


A register file is a mapping from the register's identifier to the value contained within.

> type RFile = Mapping Reg (Maybe ElemId)

An instance of the OILR machine also contains a text section containing the program, and sets of indices called search spaces, however as these are not amenable to modification by machine instructions we can elide them from our representation.
 <!-- TODO: can we really??? --> 





In defining our instruction set we will find that abstracting out some commonly-used functionality will aid readability.

To fetch the value stored in a register we shall define `getR`, which takes a register id and a register file and returns the integer value held by the register.

Similarly, to store a value in a register we define `setR`.


We also need to wrap some low level graph operations to hide differences between the OILR machine and the reference interpreter.

In some situations, such as graph element deletion, the OILR machine does not draw a distinction between a node and an edge, whereas our underlying graph representation does. Our implementation of this unified function therefore has two distinct definitions, depending on whether element in question is a node or an edge.

For graph element creation we can simply use the underlying graph functions `newNode` and `newEdge`.







 <!--getE
      OILR Int          -- Number of OILR indices
    -- Label arithmetic
    | CLL Dst Src          -- Copy eLement Label from Src to Dst
    | ADL Dst Src          -- ADd Label of Src to label of Dst
    | ADI Dst Int          -- ADd Immediate Int to label of Dst (use negative to subtr)


    -- Graph oracle
    | ASRT Sid Int         -- Assert that spc Sid must contain at least Int nodes

    -- Stack machine
    -- | BLO Dst              -- push Bound eLement Out-degree to stack
    | BLI Dst              -- push Bound eLement In-degree to stack
    | BLL Dst              -- push Bound eLement looP-degree to stack
    | BLR Dst              -- push Bound eLement Rootedness to stack
    | BLN Dst              -- push Bound eLement's Numeric label to stack
    | BLC Dst              -- push Bound eLement Colour to stack

    | SHL Int              -- SHift top-of-stack Left by Int bits
    | OR                   -- bitwise OR top 2 values on the stack
    | AND                  -- bitwise AND top 2 value on the stack
-->



The instruction evaluator `evalI` executes the decoded instruction. 

> evalI :: Instr -> VM -> VM

\subsection{Definitions \& program structure}

Procedure and rule definition.

> evalI (DEF id) = nop

Targets for labelled-branch instructions.

> evalI (TAR id) = nop


> evalI (BRZ id) = \vm@(VM {bf}) -> if bf then nop else branch id
> evalI (BNZ id) = \vm@(VM {bf}) -> if bf then branch id else nop


Branch randomly. This instruction is required to implement the program-OR feature of the GP2 language, and is the reason we maintain a pool of pseudo-random numbers in the OILR machine.

> evalI (BRA id) = error "not implemented"

Unconditional branch.

> evalI (BRN id) = \vm@(VM {bf}) -> branch id


> evalI (ONCE Id) = call
> evalI (ALAP id) = call 





Return to the address on the top of the return stack.

> evalI RET = ret


Return if $BF$ is false.

> evalI RTZ = \(VM {bf}) -> if bf then nop else ret


Return if $BF$ is true.

> evalI RNZ = \(VM {bf}) -> if bf then ret else nop



\subsection{Transactional code blocks}

Start a back-tracking section.

> evalI BBT = startTCB


The next two instructions will end a transactional code block. The subtlety here is that the semantics of the OILR machine permit nesting of transactions, so we cannot simply set the $TF$ to false.

End a transactional code block, unconditionally rolling-back the changes made. This is necessary for implementing GP2's `if` construct, which always discards the result of evaluating its predicate term.

> evalI BAK = (endTCB . rollback)


End a transactional code block, discarding the T-stack if $BF$ is true, otherwise rolling back the changes to the host graph.

> evalI EBT = \vm -> ( endTCB  .  if bf vm then commit else rollback )


\subsection{Graph search instructions}

These instructions have complex behaviour. They all modify local registers, and update the global boolean flag to indicate success or failure, and on failure they over-write the program counter, and either jumping back to a previous matching instruction or exiting the rule entirely.  Although it may be less obvious, they also change the graph, by setting the bound-flags on matched graph elements. This latter step preserves injectivity of matching.

Faced with the complexity of these instructions, both in terms of number of arguments, and their semantics, the question of whether or not the branch-on-failure behaviour constitutes a separate instruction lacks a clear answer. As we note that there is no situation in which a match instruction is not immediately followed by a conditional branch, we shall treat the branch as part of the matching operation and accept more complex instructions in exchange for a reduction in length of the instruction stream and the possibility of more efficient implementation of the compound operation in the run-time system.

Bind node.

> evalI (BND r ss) = ( bind r . orFail . setBFFromWR . ssNext ss . unbind r )

Bind out-edge.

> evalI (BOE r0 r1 r2) = ( bind r0 . orFail . setBFFromWR . edgeBtw r1 r2 )



Bind out-edge and node.

> evalI (BON r0 r1 r2) = ( bind r1 . target r0 . orFail . bind r0 . outE r0 r2 )

Bind in-edge and node.

> evalI (BIN r0 r1 r2) = ( bind r1 . source r0 . orFail . bind r0 . inE r0 r2 )

Bind loop on node.

> evalI (BLO r0 r1  addr) = ( orFail . bind r0 . loopE r1 )

While not strictly necessary, we introduce the following instructions as a convenience for supporting GP2's "bidi" edge matching construct. When we come to implement a run-time system, we have the possibility to intelligently select which direction to try first based on observed characteristics of the host graph.

> evalI (BED r0 r1 r2) = error "not implemented" 
> evalI (BEN r0 r1 r2) = error "not implemented"


\subsection{Conditions}

Like matching instructions, graph conditions modify the boolean flag and, on failure, invalidate part of the match by setting the program counter to a previous match instruction. The graph and local registers are left unmodified.

Negative edge condition.

> evalI (NEC r0 r1) = ( notBF . edgeTest r0 r1 )

Check marked edge. The colour of a node is encoded in the OILR indexing structure, any node returned by the matching instruction is guaranteed to be of a compatible colour. Edges lack this guarantee, so we must perform a post-hoc test for a correct mark.

> evalI (CME r) = error "not implemented"


Check label. OILR indexing only guarantees the presence or absence of a label. Therefore for nodes we much ensure that the value of the label is compatible with the rule left-hand-side. For edges the semantics of this instruction must be such that we must also verify that the edge has (or doesn't have) a label in the first place.

 <!-- TODO: THIS IS INADEQUATE FOR EDGES -- we don't ever check the label-exists flag -->

> evalI (CKL r n) = error "not implemented"


\subsection{Graph modification instructions}

Add and bind node.

> evalI (ABN r) = ( bind r . newNode )

Add and bind edge.

> evalI (ABE r0 r1 r2) = ( bind r0 . newEdge r1 r2 )

Add and bind loop.

> evalI (ABL r0 r1) = ( bind r0 . newEdge r1 r1 )


Delete bound node.

> evalI (DBN r) = ( delElem r . unbind r )

Delete bound loop.

> evalI (DBL r) = ( delElem r . unbind r )

Delete bound edge.

> evalI (DBE r) = ( delElem r . unbind r )

Set root flag on bound node.

> evalI (RBN r b) = ( setRoot r b )

Set colour of bound element.

> evalI (CBL r c) = ( setC r c )

Label bound element.

> evalI (LBL r n) = ( setL r n )


\subsection{Miscellaneous instructions}

> evalI NOP = id
> evalI TRU = setBF True
> evalI FLS = setBF False


Allocate a local register file of size `n`.

> evalI (REGS n) = mkRegs n

Reset a search space.

> evalI (RST s) = resetSS s

(TODO: is this instruction really necessary?)

> evalI SUC = nop

Unbind elements bound into the register file for this rule, where `n` is the size of the register file.

> evalI (UBN n) = unbindAll n

 <!-- vim:set spell lbr : -->
