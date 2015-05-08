#include "symbol.h"

SymbolList *addSymbol(SymbolList *list, SymbolType type, string scope, string rule_name,
                      bool is_var, bool in_lhs, bool wildcard, bool bidirectional)
{
   SymbolList *symbol = malloc(sizeof(SymbolList));
   if(symbol == NULL) {
      print_to_log("Error (makeSymbol): malloc failure.\n");
      exit(1);
   }
   symbol->type = type;
   symbol->scope = scope == NULL ? NULL : strdup(scope);
   symbol->rule_name = rule_name == NULL ? NULL : strdup(rule_name);
   symbol->is_var = is_var;
   symbol->in_lhs = in_lhs;
   symbol->wildcard = wildcard;
   symbol->bidirectional = bidirectional;
   symbol->next = list;
   return symbol;
}

bool symbolInScope(SymbolList *symbol, string scope, string rule_name)
{
   return !strcmp(symbol->scope, scope) && !strcmp(symbol->rule_name, rule_name);
}

void freeSymbolList(gpointer key, gpointer value, gpointer user_data) 
{
   SymbolList *list = (SymbolList*)value;
   while(list != NULL)
   {
      if(list->scope) free(list->scope);    
      if(list->rule_name) free(list->rule_name);
      SymbolList *temp = list;
      list = list->next;
      free(temp);
   }
}


void addBiEdge(BiEdgeList *list, string scope, string containing_rule, 
               char graph, string source, string target)
{
   BiEdgeList *new_edge = malloc(sizeof(BiEdgeList));
   if(new_edge == NULL)
   {
      print_to_log("Error (addBiEdge): malloc failure.\n");
      exit(1);
   }
   new_edge->value.scope = strdup(scope); 
   new_edge->value.containing_rule = strdup(containing_rule);
   new_edge->value.graph = graph;
   new_edge->value.source = strdup(source);
   new_edge->value.target = strdup(target);
   new_edge->next = NULL;

   /* Append new_edge to bidirectional_edges. */
   if(list == NULL) list = new_edge;
   else 
   { 
      BiEdgeList *iterator = list;
      while(iterator->next) iterator = iterator->next; 
      iterator->next = new_edge;
   }
}

void freeBiEdgeList(BiEdgeList *list) 
{
    if(list == NULL) return;
    BiEdge bi_edge = list->value;
    if(bi_edge.scope) free(bi_edge.scope);
    if(bi_edge.containing_rule) free(bi_edge.containing_rule);
    if(bi_edge.source) free(bi_edge.source);
    if(bi_edge.target) free(bi_edge.target);
      
    if(list->next) freeBiEdgeList(list->next);             
    free(list);
}
