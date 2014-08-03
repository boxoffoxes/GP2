module Main where

import System.IO
import System.Environment
import System.Console.GetOpt

import ApplyRule
import ExAr
import Graph (graphToGP2)
import GraphIsomorphism
import GPSyntax
import ParseGraph
import ParseLib
import ParseProgram
import PrintGraph
import ProcessAst
import RunProgram

-- Optional: For testing
import GraphMatch
import Graph
import ParseRule

testProg = fst $ makeGPProgram $ parse program programStr

programStr = concat ["Main = r\nr (a:list)\n",
                     "[ (n1, a) | (e1, n1, n1, 1) ]\n=>\n",
                     "[ (n1, a) | (e1, n1, n1, empty) ]\n",
                     "interface = {n1}"]

testRule = makeRule (parse rule ruleStr) "Global" []

ruleStr = concat ["r (a:list)\n",
                  "[ (n1, a) | (e1, n1, n1, 1) ]\n=>\n",
                  "[ (n1, a) | (e1, n1, n1, empty) ]\n",
                  "interface = {n1}"]

testlhs = fst $ makeRuleGraph (parse ruleGraph lhsStr) "Global" "r" [("a", Symbol (Var_S ListVar False) "Global" "r")]

lhsStr = "[ (n1, a) | (e1, n1, n1, 1) ]"

testHG = makeHostGraph $ parse hostGraph hostStr

hostStr = "[ (n1, 1) (n2, 2) | (e1, n1, n1, 1) ]"

printGraph :: HostGraph -> String
printGraph = graphToGP2 . makePrintableGraph


printResult :: FilePath -> Result -> IO ()
printResult fileName (gs, fc, uc) = do
   putStrLn $ show fc ++ " fails."
   putStrLn $ show uc ++ " unfinished computations."
   printGraphData fileName 1 gs

-- It's better if this function creates files in a new directory,
-- but I do not know how to do this.
printGraphData :: FilePath -> Int -> [GraphData] -> IO ()
printGraphData _ _ [] = putStrLn ""
printGraphData fileName k ((graph, count):gcs) = do
    let outputFile = fileName ++ show k 
    writeFile outputFile $ printGraph graph
    if count == 1 
        then putStrLn $ "1 occurrence of the graph in file " ++ outputFile
        else putStrLn $ show count ++ " occurrences of the graph in file " ++ outputFile 
    printGraphData fileName (k+1) gcs

-- TODO: convert progFile into a string of the actual program name
-- i.e. trim off the file extension.

usage = "Usage: gp2 <prog> <hostGraph> <maxDepth>"

main = do
    args <- getArgs
    case getOpt Permute [] args of
        (flags, [progFile, graphFile, max], []) -> do
            p <- readFile progFile
            g <- readFile graphFile
            let progName = takeWhile (/= '.') progFile
            let maxRules = read max
            -- Print host graph parse output
            putStrLn $ show $ hostGraph g
            let host = makeHostGraph $ parse hostGraph g
            putStrLn $ "\nGP 2 program " ++ progFile ++ " executed on host graph in " ++ graphFile ++ ".\n"
            -- Print program parse output
            putStrLn $ show $ program p
            let (prog, syms) = makeGPProgram $ parse program p
            putStrLn $ "Program execution stopped at " ++ show maxRules ++ " rule applications.\n"
            let result = runProgram prog maxRules host
            printResult progName result
        (_, _, errs) -> do
            error (concat errs ++ usage)
