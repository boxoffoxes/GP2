module OILR4.Instructions where

import Data.List
import Data.Bits

import OILR4.Config
import OILR4.IR
import OILR4.Spaces

import GPSyntax   -- for colour
import Mapping    -- for mappings

import Debug.Trace


-- Match registers, for readability
type Dst = Int
type Src = Int
type Tgt = Int
type Reg = Int
type Sid = Int   -- Search Space Id

-- Other instr params
type Col = Int

type Target = String


-- Machine structure
--
-- Registers:  bool-flag   b-frame-pointer   match-reg-file

type Prog = [Definition]
type Definition = ( String,  ([Instr], DefBody, [Instr]) )
data DefBody = ProcBody [Instr]
             --          lhs     rhs
             | RuleBody [[Instr]] [Instr]
    deriving (Show, Eq)

data Instr =
      REGS Int          -- Size of local register file
    -- | RST Sid           -- Reset search-space state
    | REC               -- RECursion instruction. Emitted when recursive optimisation enabled.
    | UBN Int           -- UnBiNd elements in n registers (possibly superfluous?)
    -- Graph modification
    | ABN Dst           -- Add and Bind Node to register Dst
    | ABE Dst Src Tgt   -- Add and Bind Edge to register Dst between nodes in Src & Tgt
    | ABL Dst Src       -- Add and Bind Loop to register Dst on node Src
    | DBL Dst           -- Delete Bound Loop
    | DBE Dst           -- Delete Bound Node
    | DBN Dst           -- Delete Bound Node 
    
    | RBN Dst Bool      -- set Root on Bound Node to Bool
    | MBL Dst Col       -- Mark Bound eLement
    | LBL Dst Int       -- Label Bound eLement with Int

    -- Dummy instructions used internally for constructing search but never emitted.
    | BND Dst Sid          -- Bind next unbound NoDe in Spc to Dst
    | BOE Dst Src Tgt      -- Bind Out Edge from Src to Tgt
    | BED Dst Reg Reg      -- Bind an EDge between Regs in either direction
    | BON Dst Dst Src      -- Bind Out-edge and Node by following one of Src's outgoing edges
    | BIN Dst Dst Tgt      -- Bind In-edge and Node by following one of Tgt's incoming edges
    | BEN Dst Dst Reg      -- Bind Edge and Node in either direction from Reg
    | BLO Dst Reg          -- Bind a LOop on node in Reg -}

    | NEC Src Tgt          -- Negative Edge Condition from Src to Tgt
    | CKM Reg Col          -- Check Mark on element in Reg is Col
    | CKB Reg Bool Int     -- ChecK existence of Label of element in Reg is Bool and has value Val
    | CKR Reg Bool         -- Check Root-flag is Bool
    | CKO Reg Int          -- Check Out-degree of node in Reg is Int
    | CKI Reg Int          -- Check In-degree of node in Reg is Int
    | CKL Reg Int          -- Check Loop-degree of node in Reg is Int

    -- Label arithmetic
    | CLL Dst Src          -- Copy eLement Label from Src to Dst
    | ADL Dst Src          -- ADd Label of Src to label of Dst
    | ADI Dst Int          -- ADd Immediate Int to label of Dst (use negative to subtr)
    | RLL Dst              -- Remove label from element

    -- Definitions & program structure
    | DEF Id               -- DEFine function Idopen source dev site
    | ONCE Id              -- call Id ONCE
    | ALAP Id              -- call Id for As Long As Possible
    | L Target           -- jump TARget
    | BF Target            -- Branch on Failure (ie if bool flag is false)
    | BS Target            -- Branch on Success
    | BRA Target           -- Branch RAndomly. Take the branch 50% of the time.
    | BRN Target           -- unconditional BRaNch to Target
    | RET                  -- RETurn to IP on top of call-stack
    | RTZ                  -- ReTurn if Zero
    | RNZ                  -- Return if Non-Zero

    -- Transactional code blocks
    | TRN                  -- Begin BackTracking section
    | BAK                  -- unconditionally roll-BAcK backtracking section changes
    | ETR                  -- End BackTracking secion: commit if flag is true, rollback otherwise
    -- There is no rollback command. This needs to be done manually with reverse rules.

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

    -- Misc
    | NOP                  -- No-OP
    | TRU                  -- set the boolean register to TRUe
    | FLS                  -- set the boolean register to FaLSe

    -- These are new instructions to support the graph oracle ("ORIcL"?)
--    | NEED Int Spc         -- assert that a rule requires there to be Int nodes in Spc
--    | CHFT Int Feature     -- increase or decrease the number of available Feature by Int
--    | STFT Int Feature     -- set the number of available Feature to be Int
    deriving (Show, Eq, Ord)


prettyProg :: Prog -> String
prettyProg prog = intercalate "\n" $ map prettyDefn prog
    where prettyDefn (id, (pre, body, post)) = '\n':id ++ (intercalate "\n" $ ":":(map prettify $ concat [pre, smoosh body, post]))
          prettify (L tgt) = tgt ++ ":"
          prettify (BS tgt) = "\tBS " ++ tgt
          prettify (BF tgt) = "\tBF " ++ tgt
          prettify (BRA tgt) = "\tBRA " ++ tgt
          prettify (BRN tgt) = "\tBRN " ++ tgt
          prettify (ONCE tgt) = "\tONCE " ++ tgt
          prettify (ALAP tgt) = "\tALAP " ++ tgt
          prettify i = '\t':show i
          smoosh (ProcBody is) = is
          smoosh (RuleBody lhs rhs) = concat [concat lhs, rhs]

hasTransactions :: OilrExpr -> Bool
hasTransactions (IRTrns e)    = True
hasTransactions (IRIf c t e)  = True
hasTransactions (IRCall _)    = False
hasTransactions (IRRuleSet _) = False
hasTransactions (IRLoop e)    = hasTransactions e
hasTransactions (IRProgOr a b) = or [ hasTransactions a , hasTransactions b ]
hasTransactions (IRTry c t e) = or $ map hasTransactions [c,t,e]
hasTransactions (IRSeqn es)   = or $ map hasTransactions es

compileProg :: OilrConfig -> [OilrIR] -> (OilrConfig, Prog)
compileProg cfg ir = foldr compile (cfg, []) ir

compile :: OilrIR -> (OilrConfig, Prog) -> (OilrConfig, Prog)
compile (IRProc name e)  (cfg, is) = (cfg',  ((mangle name, ([], defn, [RET])):is) )
    where defn = ProcBody $ tidyInsStream [] (compileExpr t e)
          t = length is * 1000
          cfg' = if hasTransactions e then cfg { compilerFlags=EnableTransactions:(compilerFlags cfg) } else cfg
compile (IRRule name es) (cfg, is) = (cfg', defn:is)
    where (defn, cfg') = compileRule (mangle name) cfg es

-- Compile a rule definition
nullBody = RuleBody [] []
compileRule :: String -> OilrConfig -> OilrRule -> (Definition, OilrConfig)
compileRule name cfg ms = (defn, cfg')
    where defn = (name, (pre, body, post))
          merger = if NoMultiInstr `elem` compilerFlags cfg
                        then id
                        else (yama [] [])
          sorter = if NoSearchPlan `elem` compilerFlags cfg
                        then id
                        else (sortInstr [] [])
          oracle = if UseOracle `elem` compilerFlags cfg
                        then makeOracle
                        else (\_ -> [])
          recrsr = if NoRecursion `elem` compilerFlags cfg
                        then []
                        else [REC]
          pre  = [REGS (length regs)] ++ oracle lhs
          body = RuleBody ((merger $ sorter $ reverse lhs) ++ [recrsr]) (sort rhs)
          post = concat [ [UBN (length regs)]
                        -- , concat rhs
                        , [RET] ]
          (cfg', vars, regs, RuleBody lhs rhs) = foldr compileMod (cfg, [], [], nullBody) $ reverse ms


edgeTo :: Reg -> [Instr] -> Bool
edgeTo n (BOE _ _ t:_) =  n==t
edgeTo _ _ = False

edgeFrom :: Reg -> [Instr] -> Bool
edgeFrom n (BOE _ s _:_) =  n==s
edgeFrom _ _ = False

{- Yet Another Merge Attempt! -}
yama :: [[Instr]] -> [Reg] -> [[Instr]] -> [[Instr]]
yama acc seen (i@(BND r _:ncs):is) =
    case (find (edgeTo r) is, find (edgeFrom r) is) of
        (Just x@(BOE e s t:ecs), _  ) ->
            if s `elem` seen
                then yama ((BON e t s:(ncs++ecs)):acc) (r:seen) $ is \\ [x]
                else yama (i:acc) (r:seen) is
        (Nothing, Just x@(BOE e s t:ecs)) ->
            if t `elem` seen
                then yama ((BIN e s t:(ncs++ecs)):acc) (r:seen) $ is \\ [x]
                else yama (i:acc) (r:seen) is
        (Nothing, Nothing)            -> yama (i:acc) (r:seen) is
yama acc seen (i:is) = yama (i:acc) seen is
yama acc _ [] = reverse acc
    
makeOracle :: [[Instr]] -> [Instr]
makeOracle is = ors
    where ors = concatMap makeOra is
          makeOra (BND _ s:_) = [ASRT s 1]
          makeOra _           = []


sortInstr :: [Reg] -> [[Instr]] -> [[Instr]] -> [[Instr]]
sortInstr rs acc (i@(BND r _:_):is) = sortInstr rs' (i:acc) $ concat [promoted, rest]
    where (promoted, rest) = partition promotable is
          rs' = r:rs
          promotable (BLO _ n:_)   | n `elem` rs' = True
          promotable (BOE _ s t:_) | s `elem` rs' && t `elem` rs' = True
          promotable (BED _ a b:_) | a `elem` rs' && b `elem` rs' = True
          -- TODO: should we promote NECs or not?
          promotable (NEC s t:_)   | s `elem` rs' && t `elem` rs' = True
          promotable _ = False
sortInstr rs acc (i:is) = sortInstr rs (i:acc) is
sortInstr _  acc []     = reverse acc


mkLabellingCode :: Mapping Id Int -> Reg -> IRLabel -> [Instr]
mkLabellingCode _ r (IREmpty)    = []
mkLabellingCode _ r (IRInt n)    = [LBL r n]
mkLabellingCode vars r (IRVar v) = [CLL r $ definiteLookup v vars] 
mkLabellingCode vars r (IRAdd x y) = case (x, y) of
    (IRVar _, IRInt n) -> mkLabellingCode vars r x ++ [ADI r n]
    (IRVar _, IRVar v) -> mkLabellingCode vars r x ++ [ADL r $ definiteLookup v vars]

createElem :: Mapping Id Int -> Mapping Id Int -> Reg -> OilrElem -> [Instr]
createElem vars regs reg (IRNode id m l sig) = concat [ mrk, lbl, rt, [ABN reg] ]
    where mrk = if m == Uncoloured then [] else [MBL reg $ definiteLookup m colourIds]
          rt  = case sig of
                    (Sig _ _ _ True _) -> [RBN reg True]
                    _                  -> []
          lbl = (compileNewLabel vars reg . normaliseLabel) l 
createElem vars regs reg (IREdge id m l _ s t)             = concat [ lbl, mrk, [abe regs reg s t] ]
    where mrk = if m == Uncoloured then [] else [MBL reg $ definiteLookup m colourIds]
          lbl = case l of
                    IREmpty -> []
                    IRInt n -> [LBL reg n]

compileNewLabel :: Mapping Id Int -> Reg -> IRLabel -> [Instr]
compileNewLabel vars reg IREmpty   = []
compileNewLabel vars reg (IRInt n) = [LBL reg n]
compileNewLabel vars reg (IRVar v) = [CLL reg $ definiteLookup v vars]
compileNewLabel vars reg x         = reverse $ LBL reg 0 : compileNewLabel' x
    where 
          compileNewLabel' (IRInt n) = [ADI reg n]
          compileNewLabel' (IRVar v) = [ADL reg $ definiteLookup v vars]
          compileNewLabel' (IRAdd (IRVar v) t) = compileNewLabel' (IRVar v) ++ compileNewLabel' t

normaliseLabel :: IRLabel -> IRLabel
normaliseLabel (IRAdd (IRInt n) (IRInt m)) = IRInt (n+m)
normaliseLabel (IRAdd n@(IRInt _) v@(IRVar _)) = IRAdd v n
normaliseLabel (IRAdd a b) = IRAdd (normaliseLabel a) (normaliseLabel b)
normaliseLabel l = l


compileMod :: OilrMod -> (OilrConfig, Mapping Id Int, Mapping Id Int, DefBody) -> (OilrConfig, Mapping Id Int, Mapping Id Int, DefBody)
compileMod (Create x) (cfg, vars, regs, body) =
    (cfg,vars,(id,r):regs, growRule body [] $ createElem vars regs r x)
{- case x of
    (IRNode id _ _ _     ) -> ( cfg, vars, (id,r):regs, growRule body [] [ABN r] )
    (IREdge id _ _ _ s t ) -> ( cfg, vars, (id,r):regs, growRule body [] [abe regs r s t] ) -}
    where r = length regs
          id = case x of
                   (IRNode i _ _ _)   -> i
                   (IREdge i _ _ _ _ _) -> i
compileMod (Delete x) (cfg, vars, regs, body) = case x of
    (IRNode id _ l _)      -> ( cfg', vars, (id,r):regs, growRule body (BND r sid:mkTests r x) [DBN r] )
    e@(IREdge id c l bi s t)
        | s == t    -> ( cfg, addV l r vars, (id,r):regs, growRule body (bed regs r e:mkTests r e) [DBL r] )
        | otherwise -> ( cfg, addV l r vars, (id,r):regs, growRule body (bed regs r e:mkTests r e) [DBE r] )
    where r = length regs
          cfg' = makeSpc cfg (Delete x)
          sid = fst $ head $ searchSpaces cfg'
compileMod (Same x)   (cfg, vars, regs, body) = case x of
    IRNode id _ l _      -> (cfg', addV l r vars, (id,r):regs, growRule body (BND r sid:mkTests r x) [])
    e@(IREdge id _ l _ _ _) -> (cfg, addV l r vars, (id,r):regs, growRule body (bed regs r e:mkTests r e) [])
    where r = length regs
          cfg' = makeSpc cfg (Same x)
          sid = fst $ head $ searchSpaces cfg'
compileMod (Change left right) (cfg, vars, regs, body) = case (left, right) of
    (IRNode id _ l _     , IRNode _ _ _ _)
            -> (cfg', addV l r vars, (id,r):regs, growRule body (BND r sid:mkTests r left) (diffs vars regs r left right) )
    (IREdge id c l _ _ _, IREdge _ _ _ _ _ _)
            -> (cfg,  addV l r vars, (id,r):regs, growRule body (bed regs r left:mkTests r left) (diffs vars regs r left right) )
    where r = length regs
          cfg' = makeSpc cfg $ Change left right
          sid = fst $ head $ searchSpaces cfg'
compileMod (Check (IRNot (IREdge id _ _ _ s t))) (cfg, vars, regs, body) =
                            (cfg, vars, regs, growRule body [nec regs s t] [])
-- compileMod x _ = error $ show x

addV :: IRLabel -> Reg -> Mapping Id Reg -> Mapping Id Reg
addV (IRVar v) r vars = (v,r):vars
addV _ _ vars = vars


growRule :: DefBody -> [Instr] -> [Instr] -> DefBody
growRule (RuleBody lhs rhs) lhsIns rhsIns = RuleBody lhs' rhs'
    where lhs'  = lhsIns:lhs
          rhs'  = rhsIns ++ rhs

compileRhsLabel :: Mapping Id Int -> Reg -> IRLabel -> IRLabel -> [Instr]
compileRhsLabel vars reg l IREmpty   = case l of
                                            IREmpty -> []
                                            _       -> [RLL reg]
compileRhsLabel vars reg l (IRInt n) = [LBL reg n]
compileRhsLabel vars reg l (IRVar v) = [CLL reg (definiteLookup v vars)]
compileRhsLabel vars reg l (IRAdd (IRVar v) (IRInt n)) = [CLL reg (definiteLookup v vars), ADL reg n]

diffs :: Mapping Id Int -> Mapping Id Int -> Reg -> OilrElem -> OilrElem -> [Instr]
diffs vars regs r (IRNode ib cb lb (Sig _ _ _ rb _)) (IRNode ia ca la (Sig _ _ _ ra _)) =
    concat [ if cb /= ca then [MBL r $ definiteLookup ca colourIds] else []
           , if lb /= la then compileRhsLabel vars r lb la else []     -- TODO: label support
           , if rb /= ra then [RBN r ra] else [] ]
diffs vars regs r (IREdge ib cb lb bb sb tb) (IREdge ia ca la ba sa ta)
    -- i = id, c = colour, l = label, b = bidi, s = source node, t = target node
    | sb == sa && tb == ta =
        case bb == ba || ba of 
        True -> concat [ if cb /= ca then [MBL r $ definiteLookup ca colourIds] else []
                       , if lb /= la then [LBL r 0] else [] ]  -- TODO: label support
        False -> [ DBE r, abe regs r sa ta, MBL r $ definiteLookup ca colourIds, LBL r 0]
    | otherwise            = error "Edge source and target should not change"


mkBTest :: Reg -> IRLabel -> [Instr]
mkBTest r IREmpty = [CKB r False 0]
mkBTest r (IRVar _) = []  -- a simple variable always matches, no test needed. TODO: IS THIS TRUE FOR UNLABELLED?
mkBTest r (IRInt i) = [CKB r True i]
mkBTest r l = error $ "Unimplemented label format: " ++ show l

mkCTest :: Reg -> Colour -> [Instr]
mkCTest r Any = []
mkCTest r c = [CKM r (definiteLookup c colourIds)]

mkRTest :: Reg -> Bool -> [Instr]
mkRTest r True = [CKR r True]
mkRTest r _    = []


mkTests :: Reg -> OilrElem -> [Instr]
mkTests r (IRNode _ cb lb (Sig _ _ _ rb _)) = concat [mkCTest r cb, mkBTest r lb, mkRTest r rb]
mkTests r (IREdge _ cb lb _ _ _)            = concat [mkCTest r cb, mkBTest r lb]

{- mkLabelTest :: Reg -> IRLabel -> [Instr]
mkLabelTest r IREmpty = [CKB r False 0]
mkLabelTest r (IRVar _) = []
mkLabelTest r (IRInt i) = [CKB r True i]
mkLabelTest r l = error $ "Unimplemented label format: " ++ show l

mkEdgeTests :: Reg -> IRLabel -> Colour -> [Instr]
mkEdgeTests r l Dashed = CKM r (definiteLookup Dashed colourIds):mkLabelTest r l
mkEdgeTests r l _ = mkLabelTest r l -}

bed :: Mapping Id Reg -> Reg -> OilrElem -> Instr
bed regs r (IREdge _ c l _ s t) | s==t =
    BLO r (definiteLookup s regs)
bed regs r (IREdge _ c l False s t) =
    BOE r (definiteLookup s regs) (definiteLookup t regs)
bed regs r (IREdge _ c l True s t) =
    BED r (definiteLookup s regs) (definiteLookup t regs)


abe :: Mapping Id Reg -> Reg -> Id -> Id -> Instr
abe regs r s t | s==t      = ABL r (definiteLookup s regs)
               | otherwise = ABE r (definiteLookup s regs) (definiteLookup t regs)

nec :: Mapping Id Reg -> Id -> Id -> Instr
nec regs s t = NEC (definiteLookup s regs) (definiteLookup t regs)

-- compileExpr :: (Int, [Instr]) -> OilrExpr -> (Int, [Instr])
compileExpr :: Int -> OilrExpr -> [Instr]
compileExpr i (IRRuleSet rs)       = compileSet (i+1) rs
compileExpr i (IRIf  cn th el) = concat [ TRN:compileExpr (i+1) cn
                                        , [ BAK, bf i "elseI" ]
                                        , compileExpr (i+1) th
                                        , [ brn i "endI" , tar i "elseI" ]
                                        , compileExpr (i+1) el
                                        , [ tar i "endI" ] ]
compileExpr i (IRTry cn th el) = concat [ compileExpr (i+1) cn 
                                        , [ bf i "elseT" ]
                                        , compileExpr (i+1) th
                                        , [ brn i "endT" , tar i "elseT" ]
                                        , compileExpr (i+1) el
                                        , [ tar i "endT" ] ]
compileExpr i (IRTrns e)     = concat [ [TRN] , compileExpr (i+1) e , [ETR] ]
compileExpr i (IRSeqn es)    = compileSequence (i+1) es
compileExpr i (IRLoop (IRRuleSet [r])) = [ ALAP (mangle r) ]
compileExpr i (IRLoop e)     = concat [ [tar i "bgn" ],
                                        compileExpr (i+1) e,
                                        [bs i "bgn", TRU] ]
compileExpr i (IRCall id)    = [ ONCE (mangle id) ]
compileExpr i IRTrue         = [ TRU ]
compileExpr i IRFals         = [ FLS ]


tidyInsStream :: [Instr] -> [Instr] -> [Instr]
tidyInsStream acc []             = reverse acc
tidyInsStream acc (BND r s:CKB t _ _:is) | r == t = tidyInsStream (BND r s:acc) is
tidyInsStream acc (TRU:BF _:is) = tidyInsStream (TRU:acc) is
tidyInsStream acc (ALAP r: BF _:is) = tidyInsStream (ALAP r:acc) is
tidyInsStream acc (i:is)         = tidyInsStream (i:acc) is


compileSequence :: Int -> [OilrExpr] -> [Instr]
compileSequence i es = intercalate [(bf i "end")] [ compileExpr i' e | (e, i') <- zip es [i..] ] ++ [tar i "end"]

compileSet :: Int -> [Id] -> [Instr]
compileSet i [r] = [ ONCE (mangle r) ]
compileSet i rs = intercalate [(bs i "end")] [ [ONCE (mangle r)] | r <- rs ] ++ [tar i "end"]


mangle :: String -> String
mangle "Main"  = "OILR_Main"
mangle s@(i:_) | i `elem` ['A'..'Z'] = "OILR_proc_" ++ s
               | otherwise           = "OILR_rule_" ++ s

bs = labelledInstr BS
bf = labelledInstr BF
bra = labelledInstr BRA
brn = labelledInstr BRN
tar = labelledInstr L

labelledInstr :: (String -> Instr) -> Int -> String -> Instr
labelledInstr ins i s = ins ( s ++ ('_':show i) )

