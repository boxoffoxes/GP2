import OILR4.Instructions

type Graph = ([Nodes], [Edges])

type VM = (PC, [Reg], Graph, Bool)

type Ins = VM -> VM




evalI :: [

