theory BoolProgs_Extras
imports
  BoolProgs
  "HOL-Library.Mapping"
begin

context begin interpretation BoolProg_Syntax .

subsection \<open>Macros\<close>

text \<open>Counters \<approx> bounded natural numbers\<close>

(* Vars: offset, number of vars, value *)
fun set_counter :: "nat list \<Rightarrow> bexp list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> com"
where
  "set_counter vs bs _ 0 _ = vs ::= bs"
| "set_counter vs bs pos (Suc l) 0 = set_counter (pos#vs) (FF#bs) (Suc pos) l 0"
| "set_counter vs bs pos (Suc l) (Suc n) = set_counter (pos#vs) (TT#bs) (Suc pos) l n"

(* Vars: offset, number of vars, value to compare to *)
definition counter_eq :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bexp" where
  "counter_eq pos m n = (if n > m then FF else
                           let posT = [0..<n] in
                           let posF = [n..<m] in
                           let bexps = (map (\<lambda>x. V (pos + x)) posT) @ (map (\<lambda>x. Not (V (pos + x))) posF) in
                           foldl And TT bexps)"

(* Vars: offset, number of vars *)
fun inc_counter :: "nat list \<Rightarrow> bexp list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> com"
where
  "inc_counter vs bs pos 0 = vs ::= bs"
| "inc_counter vs bs pos (Suc n) = IF V pos THEN inc_counter vs bs (Suc pos) n ELSE (pos#vs) ::= (TT#bs)"

fun dec_counter_toggle :: "nat list \<Rightarrow> bexp list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> com" where
 "dec_counter_toggle vs bs False _ = vs ::= bs"
|"dec_counter_toggle vs bs True pos = ((pos - 1)#vs) ::= (FF#bs)"

fun dec_counter' :: "nat list \<Rightarrow> bexp list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> com"
where
  "dec_counter' vs bs start pos 0 = dec_counter_toggle vs bs start pos"
| "dec_counter' vs bs start pos (Suc n) = 
                      IF Not (V pos) THEN (dec_counter_toggle vs bs start pos)
                      ELSE dec_counter' vs bs True (Suc pos) n"

(* Vars: offset, number of vars *)
definition dec_counter :: "nat list \<Rightarrow> bexp list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> com" where
  "dec_counter vs bs = dec_counter' vs bs False"

(* Array access via run-time variable. Emulated by checking all possible values.
Vars: ctr: function 'nat \<Rightarrow> bexp' - returns true if the counter is of a specific value
      act: function 'nat \<Rightarrow> com' - action to take with value if counter is value
        m: number of values (checked are [0,m[) *)
definition array_access where
  "array_access ctr act m = foldl (\<lambda>bexp c. IF ctr c THEN act c ELSE bexp) SKIP [0..<m]"

definition array_check where
  "array_check ctr chk m = foldl (\<lambda>bexp c. And (Or (Not (ctr c)) (chk c)) (Or (ctr c) bexp)) FF [0..<m]"

subsection \<open>Gather statistics\<close>

fun stat' where
  "stat' (a,t,c,g) instr = (case instr of
  AssI _ _ \<Rightarrow> (Suc a,t,c,g)
| TestI _ _ \<Rightarrow> (a,Suc t,c,g)
| ChoiceI _ \<Rightarrow> (a,t,Suc c,g)
| GotoI _ \<Rightarrow> (a,t,c,Suc g))"

definition stats where
  "stats ls = foldl stat' (0,0,0,0) ls"

subsection \<open>Misc\<close>
(* this is only used for the code setup in Programs/* *)
type_synonym const_map = "(String.literal, bexp) mapping"
type_synonym fun_map = "(String.literal, nat \<Rightarrow> bexp) mapping"

definition mapping_from_list :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) mapping"
where
  "mapping_from_list = foldl (\<lambda>m (k,v). Mapping.update k v m) Mapping.empty"
end

end
