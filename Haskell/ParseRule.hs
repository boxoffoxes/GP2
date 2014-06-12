module ParseRule where

import Data.Maybe

import ParseLib
import GPSyntax

rule :: Parser Rule
rule = pure Rule 
       <*> lowerIdent 
       <*> (pure concat <*> maybeOne parameters)
       <*> ruleGraphs
       <*> interface
       <*> (pure head <*> exactlyOne ( keyword "where" |> condition ) <|> pure NoCondition)
       <*> keyword "injective" |> keyword "=" |> (keyword "true" <|> keyword "false")
           

-- In a rule parameter declaration, multiple variables can be declared
-- with a single type. 

parameters :: Parser [Variables]
parameters = keyword "(" |> (pure (:) <*> varList <*> maybeSome (keyword ";" |> varList)) <| keyword ")" 

varList :: Parser Variables
varList = pure (,)
    <*> ( pure (:) <*> lowerIdent <*> maybeSome ( keyword "," |> lowerIdent ) ) <| keyword ":"
    <*> gpType  


gpType :: Parser VarType
gpType = pure gptype <*> label
   where gptype t = fromJust $ lookup t gpTypes

ruleGraphs :: Parser (AstRuleGraph, AstRuleGraph)
ruleGraphs = pure (,) <*> ruleGraph <*> ( keyword "=>" |> ruleGraph )

ruleGraph :: Parser AstRuleGraph
ruleGraph = keyword "[" |> pure AstRuleGraph <*> nodeList <*> edgeList <| keyword "]"

interface :: Parser Interface
interface = keyword "interface" |> keyword "=" |> keyword "{" 
         |> (pure concat <*> maybeOne ( pure (:) <*> lowerIdent <*> maybeSome interfaceNodes ) )
         <| keyword "}"

interfaceNodes :: Parser ID
interfaceNodes = keyword "," |> lowerIdent 

nodeList :: Parser [RuleNode]
nodeList = pure (++) <*> maybeOne node <*> maybeSome (keyword "," |> node)
-- A node is a triple (Node ID, Root Node, Node Label)
-- The second component is "(R)" if root node, [] otherwise.
node :: Parser RuleNode
node = keyword "(" |> pure RuleNode 
  <*> lowerIdent
  <*> (root <| keyword ",") 
  <*> gpLabel <| keyword ")"

edgeList :: Parser [RuleEdge]
edgeList = keyword "|" |> ( pure (++) <*> maybeOne edge <*> maybeSome (keyword "," |> edge) )

                                                                           
edge :: Parser RuleEdge
edge = keyword "(" |> pure RuleEdge 
   <| lowerIdent
   <*> (bidirectional <| keyword ",")
   <*> (lowerIdent <| keyword ",") 
   <*> (lowerIdent <| keyword ",") 
   <*> (gpLabel <| keyword ")")

bidirectional :: Parser Bool
bidirectional = pure (not . null) <*> (maybeOne $ keyword "(B)")

gpLabel :: Parser RuleLabel
gpLabel = pure RuleLabel <*> list <*> ruleColour


list :: Parser GPList
list = pure f <*> keyword "empty" <|> pure (:) <*> atom <*> maybeSome (keyword ":" |> atom)
  where f "empty" = []

atom :: Parser RuleAtom
atom = pure Var <*> lowerIdent
   <|> pure Val <*> value
   <|> keyword "indeg" |> keyword "(" |> pure Indeg <*> lowerIdent <| keyword ")"
   <|> keyword "outdeg" |> keyword "(" |> pure Indeg <*> lowerIdent <| keyword ")"
   <|> keyword "llength" |> keyword "(" |> pure Llength <*> list <| keyword ")"
   <|> keyword "slength" |> keyword "(" |> pure Slength <*> list <| keyword ")"
   <|> keyword "~" |> pure Neg <*> atom
   <|> keyword "+" |> pure Plus <*> atom <*> atom
   <|> keyword "-" |> pure Minus <*> atom <*> atom
   <|> keyword "*" |> pure Times <*> atom <*> atom
   <|> keyword "/" |> pure Div <*> atom <*> atom
   <|> keyword "." |> pure Concat <*> atom <*> atom


ruleColour :: Parser Colour
ruleColour = keyword "#" |> pure col <*> label
     <|> pure Uncoloured
 where
     col c = fromJust $ lookup c ruleColours

condition :: Parser Condition
condition = keyword "int" |> pure TestInt <*> lowerIdent
        <|> keyword "char" |> pure TestStr <*> lowerIdent
        <|> keyword "str" |> pure TestChar <*> lowerIdent
        <|> keyword "atom" |> pure TestAtom <*> lowerIdent
        <|> keyword "edge" |> keyword "(" |> 
            pure Edge <*> (lowerIdent <| keyword ",") 
                      <*> lowerIdent 
                      <*> (pure head <*> maybeOne (keyword "," |> gpLabel))
        <|> pure Eq <*> list <| keyword "=" <*> list
        <|> pure NEq <*> list <| keyword "!=" <*> list
        <|> pure Greater <*> atom <| keyword ">" <*> atom
        <|> pure GreaterEq <*> atom <| keyword ">=" <*> atom
        <|> pure Less <*> atom <| keyword "<" <*> atom
        <|> pure LessEq <*> atom <| keyword "<=" <*> atom
        <|> keyword "not" |> pure Not <*> condition
        <|> keyword "or"  |> pure Or  <*> condition <*> condition
        <|> keyword "and" |> pure And <*> condition <*> condition 







