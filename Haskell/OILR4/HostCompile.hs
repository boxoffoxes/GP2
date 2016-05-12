module OILR4.HostCompile (compileHostGraph) where

import OILR4.Config
import OILR4.Instructions

import GPSyntax
import Graph
import Mapping

import Debug.Trace
import Data.List

data GraphElem = N NodeKey | E EdgeKey deriving (Eq, Ord, Show)
type GraphElemId = (RuleGraph, GraphElem)
type OilrCode = [Instr]

compileHostGraph :: HostGraph -> OilrCode
compileHostGraph g = nodes g ++ edges g

-- -------------------------------------------------------------------
-- host graph OILR instruction generation
-- -------------------------------------------------------------------



compileAtoms :: Int -> [HostAtom] -> [Instr]
compileAtoms _ [] = []
compileAtoms id [Int i] = [LBL id i]
compileAtoms _ as = error $ "Unsupported label in host: " ++ show as

nodes :: HostGraph -> OilrCode
nodes g = concatMap node $ allNodes g
    where
        node (n, HostNode _ root (HostLabel as c)) =
            ABN (nodeNumber n)
            : (if root then RBN (nodeNumber n) True else NOP)
            : (if c == Uncoloured then NOP else CBL (nodeNumber n) (definiteLookup c colourIds ) )
            : compileAtoms (nodeNumber n) as


edges :: HostGraph -> OilrCode
edges g = concatMap edge $ allEdges g
    where
        edge (e, hl) = ABE (edgeNumber e) (nodeNumber $ source e) (nodeNumber $ target e) : edgeLabel e hl
        {- HACK! -1 indicates that backend should use most recently created element id. This will totally bite me one day. -}
        edgeLabel e (HostLabel as Dashed) = CBL (-1) 1:compileAtoms (-1) as
        edgeLabel _ _ = []


