theory Eg2
imports Dependent_SIFUM_Type_Systems.Language
begin

datatype var\<^sub>C = control_var\<^sub>C | buffer\<^sub>C | high_var\<^sub>C | low_var\<^sub>C | temp\<^sub>C | reg\<^sub>C

type_synonym addr\<^sub>C = var\<^sub>C
type_synonym val = nat
type_synonym mem\<^sub>C = "addr\<^sub>C \<Rightarrow> val"

(* Address expression evaluation *)
datatype aexp\<^sub>C = Const "val" |
                 Load "addr\<^sub>C"

fun 
  ev\<^sub>A\<^sub>C :: "mem\<^sub>C \<Rightarrow> aexp\<^sub>C \<Rightarrow> val"
where
  "ev\<^sub>A\<^sub>C mem (Const v) = v" |
  "ev\<^sub>A\<^sub>C mem (Load x) = mem x"

(* Boolean expression evaluation *)
datatype bexp\<^sub>C = Eq "addr\<^sub>C" "val"

fun
  ev\<^sub>B\<^sub>C :: "mem\<^sub>C \<Rightarrow> bexp\<^sub>C \<Rightarrow> bool"
where
  "ev\<^sub>B\<^sub>C mem (Eq x v) = ((mem x) = v)"

(* NB: dma ~ "domain assignment"
 * Domain assignment function based on the value of a control variable,
 * Low if 0, High otherwise. *)
definition
  dma_control_var\<^sub>C :: "val \<Rightarrow> Sec"
where
  "dma_control_var\<^sub>C v \<equiv> if v = 0 then Low else High"

(* buffer's security level is controlled by control_var.
 * high_var's is High.
 * All other memory's security level is Low. *)
definition
  dma\<^sub>C :: "mem\<^sub>C \<Rightarrow> addr\<^sub>C \<Rightarrow> Sec"
where
  "dma\<^sub>C m x \<equiv> if x = buffer\<^sub>C then dma_control_var\<^sub>C (m control_var\<^sub>C) else if x = high_var\<^sub>C then High else Low"

(* Function that gives the control variables of a given variable.
 * Only buffer is controlled by a control variable, control_var *)
definition
  \<C>_vars\<^sub>C :: "addr\<^sub>C \<Rightarrow> addr\<^sub>C set"
where
  "\<C>_vars\<^sub>C x \<equiv> if x = buffer\<^sub>C then {control_var\<^sub>C} else {}"

primrec
  aexp_vars\<^sub>C :: "aexp\<^sub>C \<Rightarrow> var\<^sub>C set"
where
  "aexp_vars\<^sub>C (Const _) = {}" |
  "aexp_vars\<^sub>C (Load v) = {v}"
  
primrec
  bexp_vars\<^sub>C :: "bexp\<^sub>C \<Rightarrow> var\<^sub>C set"
where
  "bexp_vars\<^sub>C (Eq v w) = {v}"

locale sifum_example2 =
  sifum_lang_no_dma ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C aexp_vars\<^sub>C bexp_vars\<^sub>C +
  assumes eval_det: "(lc, lc') \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C \<Longrightarrow> (lc, lc'') \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A\<^sub>C ev\<^sub>B\<^sub>C \<Longrightarrow> lc' = lc''"

definition
  \<C>\<^sub>C :: "addr\<^sub>C set"
where
  "\<C>\<^sub>C \<equiv> \<Union>x. \<C>_vars\<^sub>C x"

context sifum_example2 begin

definition
  read_buffer\<^sub>C :: "(var\<^sub>C, aexp\<^sub>C, bexp\<^sub>C) Stmt"
where
  "read_buffer\<^sub>C \<equiv> 
     ModeDecl Skip (Acq control_var\<^sub>C AsmNoWrite) ;; 
     ModeDecl Skip (Acq temp\<^sub>C AsmNoReadOrWrite) ;;
     Assign temp\<^sub>C (Load buffer\<^sub>C) ;;
     Assign reg\<^sub>C (Load control_var\<^sub>C);;
     If (Eq reg\<^sub>C 0) (Assign low_var\<^sub>C (Load temp\<^sub>C)) (Assign high_var\<^sub>C (Load temp\<^sub>C)) ;;
     Assign temp\<^sub>C (Const 0) ;;
     ModeDecl Skip (Rel temp\<^sub>C AsmNoReadOrWrite)"

end

end
