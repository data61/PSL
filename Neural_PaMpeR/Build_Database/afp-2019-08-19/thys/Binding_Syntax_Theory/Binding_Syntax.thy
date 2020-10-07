section "Bindings Syntax"

theory Binding_Syntax
imports Semantic_Domains Recursion
begin
 
(*<*) 

subsection "Some Useful End-Product Theorems"


context FixVars begin

text "Properties of the constructors and operators on terms" 
find_theorems (400) name: "local." -name: "q" -name: "alpha"
end
  
text "Fresh induction:"

thm FixVars.term_fresh_forall_induct
  
text "Substitution- and freshness- aware iteration and recursion:"

context FixSyn begin
find_theorems name: "local." rec 
end
  
text "Semantic interpretation:"
 
context FixSyn begin
find_theorems name: "local." semInt
end
    
text "Properties of well-sorted terms:" 
context FixSyn begin
find_theorems (600) name: "local." -name: "ig" -name: "ip" -name: "q" -name: "alpha" -name: "termMOD"
   -iter  -rec -name: "iter"  -name: "rec" -asTerm -asAbs -asInp -asBinp -semInt -semIntAbs
   -asIMOD -fromMOD 
    -name: gFresh -name: gSwap -name: gSubst -name: gVar -name: gCons -name: gVar -name: gOp
    -name: sFresh -name: sSwap -name: sSubst -name: sVar -name: sCons -name: sVar -name: sOp
   -name: eFresh -name: eSwap -name: eSubst -name: eVar -name: IMor -name: iwls -good -goodAbs
   -goodInp -goodBinp -name: Imorph -name: sWls -ERR -OK -name: error -name: FSb -name: FSw
   -name: gInduct
end
  
(*>*) 

end
