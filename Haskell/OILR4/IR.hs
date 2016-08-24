module OILR4.IR where

import Data.List

import GPSyntax
import Graph
import Mapping

type Id = String

data OilrMod = Create OilrElem
             | Check OilrElem
             | Same OilrElem
             | Change OilrElem OilrElem
             | Delete OilrElem
    deriving (Show, Eq)

instance Ord OilrMod where
    a `compare` b = constrainedness a `compare` constrainedness b

data IRLabel = IRInt Int
             | IRVar Id  -- Integer variable
             | IRLst Id  -- GP 2 list. preserved but not manipulated
             | IRAdd IRLabel IRLabel
             | IRAny
             | IREmpty
     deriving (Show, Eq)

data Sig = Sig { outDeg      :: Int
               , inDeg       :: Int
               , loopDeg     :: Int
               , rootDeg     :: Bool
               , biDeg       :: Int}
         | NoSig
     deriving (Show, Eq) 

data OilrElem = IRNode  Id  Colour  IRLabel  Sig
              | IREdge  Id  Colour  IRLabel  Bool  Id Id
              | IREql   IRLabel IRLabel
              | IRNot   OilrElem
              | IRNothing
     deriving (Show, Eq)

type OilrRule = [OilrMod]

data OilrIR   = IRProc Id OilrExpr
              | IRRule Id OilrRule
     deriving (Show, Eq)
type OilrProg = [OilrIR]

data OilrExpr = IRSeqn [OilrExpr]
              | IRIf   OilrExpr OilrExpr OilrExpr
              | IRTry  OilrExpr OilrExpr OilrExpr
              | IRTrns OilrExpr   -- transaction that rolls-back if OilrExpr fails
              | IRRuleSet [Id] | IRCall Id | IRLoop OilrExpr
              | IRProgOr OilrExpr OilrExpr
              | IRTrue | IRFals
     deriving (Show, Eq)

type Spc = [Sig]


constrainedness :: OilrMod -> Int
constrainedness (Delete el@(IRNode _ _ _ _))   = eCon el * 10
constrainedness (Same el)   = eCon el
constrainedness (Change el _) = eCon el
constrainedness (Create (IRNode _ _ _ _))  = 1
constrainedness _ = 0

eCon :: OilrElem -> Int
eCon (IRNode _ c l sig) = lCon l + cCon c + sCon sig + 1
eCon _                  = 0

lCon :: IRLabel -> Int
lCon (IRVar _) = 0
lCon IRAny     = 0
lCon IREmpty   = 1
lCon (IRInt _) = 1
lCon (IRLst _) = 0

cCon :: Colour -> Int
cCon Any     = 0
cCon _       = 1

sCon :: Sig -> Int
sCon (Sig o i l r bi)
    | r         = o+i+(2*l)+1
    | otherwise = o+i+(2*l)
sCon NoSig = 0

-- IR pretty-printer
prettyIR :: OilrProg -> String
prettyIR pr = concatMap prettyDecl pr
    where  prettyDecl (IRProc id e) = concat [ "\nIRProc ", id, " (\n\t", prettyExpr e, "\n)"]
           prettyDecl (IRRule id es) = concat [ "\nIRRule ", id, " [\n\t", prettyRule es, "\n]"]
           prettyExpr = show
           prettyRule es = intercalate "\n\t" $ map show es

-- IR compilation wrapper function
makeIR :: GPProgram -> OilrProg
makeIR (Program ds) = map declIR ds

-- Compile a proc or rule declaration to OILR IR
declIR :: Declaration -> OilrIR
declIR (Main cs)                          = declIR (Proc "Main" [] cs)
declIR p@(Proc id ds [c])                 = IRProc id $ exprIR c
declIR p@(Proc id ds cs)                  = IRProc id $ exprIR (Sequence cs)
declIR (AstRuleDecl r@(AstRule id vts _ _)) = IRRule id $ ruleIR r

-- Compile a procedure expression to OILR IR
exprIR :: Expr -> OilrExpr
exprIR (RuleSet rs)            = IRRuleSet rs
exprIR (Sequence es)           = IRTrns (IRSeqn $ map exprIR es)
exprIR (IfStatement cn th el)  = IRIf (exprIR cn) (exprIR th) (exprIR el)
--        IRSeqn [IRDscd (exprIR cn), IRBran (exprIR th) (exprIR el)]
exprIR (TryStatement cn th el) = IRTry (exprIR cn) (exprIR th) (exprIR el)
--        IRSeqn [IRTrns (exprIR cn), IRBran (exprIR th) (exprIR el)]
exprIR (ProgramOr a b)          = IRProgOr (exprIR a) (exprIR b)
exprIR (ProcedureCall p)        = IRCall p
exprIR (Looped (RuleSet rs))    = IRLoop (IRRuleSet rs)
exprIR (Looped (ProcedureCall p))=IRLoop (IRCall p)
exprIR (Looped s@(Sequence _))  = IRLoop (exprIR s)
exprIR Skip                     = IRTrue
exprIR Fail                     = IRFals


-- Compile a rule body to OILR IR
-- data AstRule = AstRule RuleName [Variable] (AstRuleGraph, AstRuleGraph) Condition
-- note that all variables are defaulted to ListVar at parse time and 
-- only fixed up later. This is why we need to pass around the symbol 
-- table vts, so we can reconcile variables with their actual types.
ruleIR :: AstRule -> OilrRule
ruleIR (AstRule id vs (lhs, rhs) cond) = ruleGraphIR vs lhs rhs ++ irConds
    where irConds = case ruleCondIR vs cond of
                        IRNothing              -> []
                        e@(IREdge _ _ _ _ _ _) -> [Same e]
                        c                      -> [Check c]

-- Compile a pair of GP2 graphs to an IR rule
ruleGraphIR :: [Variable] -> AstRuleGraph -> AstRuleGraph -> OilrRule
ruleGraphIR vs lhs rhs = nodes ++ edges
    where nodes = map (irNode vs sigs) $ allNodePairs lhs rhs
          edges = makeIREdges vs lhs rhs
          sigs  = makeSigs lhs

makeSigs :: AstRuleGraph -> Mapping Id Sig
makeSigs (AstRuleGraph ns es) = map makeSig ns
    where makeSig :: RuleNode -> (Id, Sig)
          makeSig (RuleNode id r _) = (id, Sig (nO id es) (nI id es) (nL id es) r (bi id es)) 
          nO :: Id -> [AstRuleEdge] -> Int
          nO id es = length $ filter (\(AstRuleEdge _ bi src tgt _) -> not bi && src == id && tgt /= id) es
          nI :: Id -> [AstRuleEdge] -> Int
          nI id es = length $ filter (\(AstRuleEdge _ bi src tgt _) -> not bi && tgt == id && src /= id) es
          nL :: Id -> [AstRuleEdge] -> Int
          nL id es = length $ filter (\(AstRuleEdge _ _ src tgt _) -> src == id && tgt == id) es
          bi :: Id -> [AstRuleEdge] -> Int -- bidi edges are a pain!
          bi id es = length $ filter (\(AstRuleEdge _ bi src tgt _) -> bi && src == id || tgt == id && src /= tgt) es


-- Make sure conditional rules are compiled correctly
ruleCondIR :: [Variable] -> Condition -> OilrElem
ruleCondIR vs NoCondition         = IRNothing
ruleCondIR vs (Not c)             = IRNot $ ruleCondIR vs c
ruleCondIR vs (Edge s t Nothing)                = IREdge "" Any IRAny           False s t
ruleCondIR vs (Edge s t (Just (RuleLabel l c))) = IREdge "" c   (makeIRLabel vs l) False s t
ruleCondIR vs (Eq as bs)          = IREql (makeIRLabel vs as) (makeIRLabel vs bs)
ruleCondIR vs c = error $ "Unsupported conditional: " ++ show c

---------------------------------------------------------------------
-- Node mangling...
---------------------------------------------------------------------

-- Match-up LHS and RHS nodes
allNodePairs :: AstRuleGraph -> AstRuleGraph -> [(Maybe RuleNode, Maybe RuleNode)]
allNodePairs lhs rhs = [ (findNode lhs id, findNode rhs id) | id <- nids ]
    where nids = allNodeIds lhs rhs

-- Get a node by its Id
findNode :: AstRuleGraph -> Id -> Maybe RuleNode
findNode (AstRuleGraph ns _) id =
    case [ rn | rn@(RuleNode ident _ _) <- ns , id==ident] of
    []  -> Nothing
    [n] -> Just n
    _   -> error "Found several nodes with the same id!"

-- Get the set of all node ids found in either side of the rule
allNodeIds :: AstRuleGraph -> AstRuleGraph -> [Id]
allNodeIds (AstRuleGraph lns _) (AstRuleGraph rns _) =
    [ lid | (RuleNode lid _ _) <- lns ] `union` [ rid | (RuleNode rid _ _) <- rns ]


---------------------------------------------------------------------
-- Edge mangling
---------------------------------------------------------------------


-- There is no concept of an edge interface in GP2, so we need to be 
-- clever about matching similar edges on the LHS and RHS of the rule.
--
-- The situation is complicated by the presence of bidi rule edges

-- Wrapper function for edge-handling complexity!
makeIREdges :: [Variable] -> AstRuleGraph -> AstRuleGraph -> OilrRule
makeIREdges vs (AstRuleGraph _ les) (AstRuleGraph _ res) =
    packEdges [] [ makeIREdge vs e | e <- les ]
                 [ makeIREdge vs e | e <- res ]


-- AstRuleEdge EdgeName Bool NodeName NodeName RuleLabel

-- Match LHS and RHS edges based on structural equality
packEdges :: OilrRule -> [OilrElem] -> [OilrElem] -> OilrRule
packEdges acc [] []     = reverse acc
packEdges acc [] (r:rs) =        packEdges (Create r:acc) [] rs
packEdges acc (l:ls) [] =        packEdges (Delete l:acc) ls []
packEdges acc (l:ls) rs = case partition (==l) rs of
    (r:_, _) ->                  packEdges (Same l            :acc) ls (delete r rs)
    ([] , _) -> case partition (irEdgeSimilarity l) rs of
                    (r:_, _)  -> packEdges (Change l r        :acc) ls (delete r rs)
                    ([],  _)  -> packEdges (Delete l:acc) ls rs
    -- TODO: make this more efficient by distinguishing structural changes from textual

-- Edge equality test (including labels)
edgeEquality :: AstRuleEdge -> AstRuleEdge -> Bool
edgeEquality (AstRuleEdge _ False lsrc ltgt ll) (AstRuleEdge _ False rsrc rtgt rl) = 
    lsrc == rsrc && ltgt == rtgt && ll == rl
edgeEquality (AstRuleEdge _ True _ _ _) (AstRuleEdge _ False _ _ _) = False
edgeEquality (AstRuleEdge _ True lsrc ltgt ll) (AstRuleEdge _ True rsrc rtgt rl) = 
    ( lsrc == rsrc && ltgt == rtgt || lsrc == rtgt && rsrc == ltgt ) && ll == rl


-- Test for GP2-valid structural equality between edges (not considering labels)
irEdgeSimilarity :: OilrElem -> OilrElem -> Bool
irEdgeSimilarity (IREdge _ _ _ True  lsrc ltgt) (IREdge _ _ _ bi rsrc rtgt)
    | (lsrc == rsrc && ltgt == rtgt ) = bi
    | (lsrc == rtgt && ltgt == rsrc ) = bi
    | otherwise                       = False
irEdgeSimilarity (IREdge _ _ _ False lsrc ltgt) (IREdge _ _ _ False rsrc rtgt)
    | lsrc == rsrc && ltgt == rtgt  = True
    | otherwise                     = False
-- TODO: does this consider manipulation of variables!?!



-- TODO: edge id?
makeIREdge :: [Variable] -> AstRuleEdge -> OilrElem
makeIREdge vs (AstRuleEdge _ bidi src tgt (RuleLabel l c)) =
    IREdge "" c (makeIRLabel vs l) bidi src tgt


---------------------------------------------------------------------
-- IR creation functions
---------------------------------------------------------------------

irNode :: [Variable] -> Mapping Id Sig -> (Maybe RuleNode, Maybe RuleNode) -> OilrMod
irNode vs sigs = irElem (makeIRNode vs sigs) (==)

irEdge :: [Variable] -> (Maybe AstRuleEdge, Maybe AstRuleEdge) -> OilrMod
irEdge vs = irElem (makeIREdge vs) edgeEquality

irElem :: (a -> OilrElem) -> (a -> a -> Bool) -> (Maybe a, Maybe a) -> OilrMod
irElem mkElem _   (Just l, Nothing) = Delete (mkElem l)
irElem mkElem _   (Nothing, Just r) = Create (mkElem r)
irElem mkElem eql (Just l,  Just r)
            | l `eql` r  =  Same   (mkElem l)
            | otherwise  =  Change (mkElem l) (mkElem r)

makeIRNode :: [Variable] -> Mapping Id Sig -> RuleNode -> OilrElem
makeIRNode vs sigs (RuleNode id root (RuleLabel l c)) = IRNode id c i sig
    where i = makeIRLabel vs l
          sig = case lookup id sigs of
                    Nothing -> NoSig
                    Just s  -> s { rootDeg=root }

makeIRLabel :: [Variable] -> [RuleAtom] -> IRLabel
makeIRLabel vs []                  = IREmpty
makeIRLabel vs [Val (Int i)]       = IRInt i
makeIRLabel vs [Neg (Val (Int i))] = IRInt (-i)  -- work-around for parser bug
makeIRLabel vs [Val v]             = error $ "Unsupported literal value: " ++ show v
makeIRLabel vs [Var (v, ListVar)]  = case lookup v vs of
                                        Just IntVar  -> IRVar v
                                        Just ListVar -> IRLst v  -- TODO: only valid if v is not evaluated!
                                        t -> error $ v ++ " is of unsupported type: " ++ show t
makeIRLabel vs [Plus a b]          = IRAdd (makeIRLabel vs [a]) (makeIRLabel vs [b])
makeIRLabel vs [Var (v, t)]        = error $ "All variables coming out of the parser should have type ListVar, but variable " ++ v ++ " had type " ++ show t
makeIRLabel vs [atom]              = error $ "Unsupported atom: " ++ show atom
makeIRLabel vs (x:xs)              = error "List type labels are not supported"


