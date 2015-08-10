module OILR3.CBackend (hostToC, progToC) where

import OILR3.Instructions
import OILR3.CRuntime

import Data.List
import Data.Bits
import Debug.Trace

type OilrProg = [Instr Int Int]
type OilrIndexBits = (Int, Int, Int, Int)

hostToC :: OilrProg -> String
hostToC is = makeCFunction "_HOST" $ map hostCompileInstruction is

hostCompileInstruction :: Instr Int Int -> String
hostCompileInstruction (ADN n)   = makeCFunctionCall "addNode" []
hostCompileInstruction (ADE e src tgt) = makeCFunctionCall "addEdgeById" [src,tgt]
hostCompileInstruction (RTN n)   = makeCFunctionCall "setRootById" [n]
hostCompileInstruction i         = error $ "Instruction " ++ show i ++ " not implemented for host graphs"

makeLoops :: OilrProg -> Maybe Int -> OilrProg -> OilrProg
makeLoops acc prev [] = reverse acc
makeLoops acc prev (i:is) = case (i, prev) of
    ( LUN n pr  , Nothing ) -> makeLoops (CRS n pr:ORF:i:acc) (Just n) is
    ( LUN n pr  , Just p  ) -> makeLoops (CRS n pr:ORB p:i:acc) (Just n) is
    ( LUE n _ _ , Just p  ) -> makeLoops (ORB p:i:acc) (Just p) is -- don't update the jump point!
    ( LUE _ _ _ , Nothing ) -> error "Tried to match an edge before a node"
    _                       -> makeLoops (i:acc) prev is
        

progToC :: [OilrProg] -> String
progToC iss = consts ++ cRuntime ++ searchSpaces ++ predeclarations iss ++ concat defns
    where
        searchSpaces = compileSearchSpaces [ (i, is)
                                           | (i, is) <- zip [1..] $ map snd $ makeSearchSpacesForDecl oilr (concat iss) ]
        defns = map (compileDefn . (makeLoops [] Nothing) ) iss
        consts = "#define OILR_INDEX_SIZE (1<<" ++ (show $ oilrIndexTotalBits oilr) ++ ")\n"
        oilr = oilrBits iss

-- Generate C declarations so that the ordering of definitions
-- doesn't matter
predeclarations :: [OilrProg] -> String
predeclarations iss = concatMap declare iss
    where
        declare ((DEF "Main"):_) = ""
        declare ((DEF s):_) = "\nvoid " ++ s ++ "();"
        declare _ = error "Found an ill-formed definition"


oilrIndexTotalBits :: OilrIndexBits -> Int
oilrIndexTotalBits (o,i,l,r) = o+i+l+r

extractPredicates :: OilrProg -> [Pred]
extractPredicates is = concatMap harvestPred is
    where harvestPred (LUN _ p) = [p]
          harvestPred _         = []


oilrBits :: [OilrProg] -> OilrIndexBits
oilrBits iss = (f o, f i, f l, f r)
    where
        f = (bits . maximum . map extract) 
        (o, i, l, r) = unzip4 $ extractPredicates $ concat iss
        extract (Equ n) = n
        extract (GtE n) = n
        bits n = head $ dropWhile (\x -> 2^x <= n) [0,1..]

sigsForPred :: OilrIndexBits -> Pred -> (Pred, [Int])
sigsForPred (oBits, iBits, lBits, rBits) p@(o, i, l, r) =
    (p, nub [ o' `shift` oShift + i' `shift` iShift + l' `shift` lShift + r' `shift` rShift
                | o' <- case o of Equ n -> [n] ; GtE n -> [n..(1 `shift` oBits)]
                , i' <- case i of Equ n -> [n] ; GtE n -> [n..(1 `shift` iBits)]
                , l' <- case l of Equ n -> [n] ; GtE n -> [n..(1 `shift` lBits)]
                , r' <- case r of Equ n -> [n] ; GtE n -> [n..(1 `shift` rBits)] ])
    where
        rShift = 0
        lShift = rShift + rBits
        iShift = lShift + lBits
        oShift = iShift + iBits


makeSearchSpacesForDecl :: OilrIndexBits -> OilrProg -> [ (Pred, [Int]) ]
makeSearchSpacesForDecl bits is = map (sigsForPred bits) preds
    where
        preds = ( nub . extractPredicates ) is


compileSearchSpaces :: [ (Int, [Int]) ] -> String
compileSearchSpaces ss = "long search_spaces[][] = {\n" ++ concatMap makeSpace ss ++ "};\n\n"
    where
        makeSpace (p, is) = '{' : ( concat $ intersperse ", " $  map show is ) ++ "},\n"


compileDefn :: OilrProg -> String
compileDefn is = concatMap compileInstr is


compileInstr :: Instr Int Int -> String
compileInstr (ADN n)         = makeCFunctionCall "addNodeByTrav" [n]
compileInstr (ADE e src tgt) = makeCFunctionCall "addEdgeByTrav" [e, src, tgt]
compileInstr (RTN n)         = makeCFunctionCall "setRootByTrav" [n]
compileInstr (URN n)         = makeCFunctionCall "unsetRootByTrav" [n]
compileInstr (DEN n)         = makeCFunctionCall "deleteNodeByTrav" [n]
compileInstr (DEE e)         = makeCFunctionCall "deleteEdgeByTrav" [e]

compileInstr RET           = "return;"
compileInstr (CAL s)       = makeCFunctionCall s []
compileInstr (ALP s)       = asLongAsPossible s []
compileInstr ORF           = "if (!boolFlag) return ;\n"
compileInstr (ORB n)       = "if (!boolFlag) goto " ++ labelFor n ++ ";\n"

compileInstr (DEF "Main")  = startCFunction "_GPMAIN"
compileInstr (DEF s)       = startCFunction s
compileInstr END           = endCFunction 

compileInstr (CRS n sig)     = makeCFunctionCall "resetTrav" [n] -- TODO
compileInstr (LUN n sig)     = labelFor n  ++ ": " ++  makeCFunctionCall "findNode" [n]
compileInstr (LUE n src tgt) = makeCFunctionCall "findEdge" [n, src, tgt]

makeCFunction :: String -> [String] -> String
makeCFunction name lines = concat [startCFunction name,  body, "\n}\n"]
    where
        body = intercalate "\n\t" lines

startCFunction :: String -> String
startCFunction name = concat [ "\nvoid ", name, "() {\n\t" ]

endCFunction :: String
endCFunction = "}\n"

asLongAsPossible :: String -> [Int] -> String
asLongAsPossible fname args = concat [ "do {\n", makeCFunctionCall fname args, "} while (success);\n" ]


makeCFunctionCall :: String -> [Int] -> String
makeCFunctionCall fname args = concat [ fname , "(", argStr, ");\n" ]
    where
        argStr = intercalate ", " $ map show args

labelFor :: Int -> String
labelFor n = "trav_no_" ++ show n
 
