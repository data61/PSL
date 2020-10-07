(* Author: R. Thiemann *)
section \<open>Elimination of CARD('n)\<close>

text \<open>In the following theory we provide a method which modifies theorems
  of the form $P[CARD('n)]$ into $n != 0 \Longrightarrow P[n]$, so that they can more
  easily be applied.
  
  Known issues: there might be problems with nested meta-implications and meta-quantification.\<close>

theory Cancel_Card_Constraint
imports 
  "HOL-Types_To_Sets.Types_To_Sets"
  "HOL-Library.Cardinality"
begin

lemma n_zero_nonempty: "n \<noteq> 0 \<Longrightarrow> {0 ..< n :: nat} \<noteq> {}" by auto

lemma type_impl_card_n: assumes "\<exists>(Rep :: 'a \<Rightarrow> nat) Abs. type_definition Rep Abs {0 ..< n :: nat}"
  shows "class.finite (TYPE('a)) \<and> CARD('a) = n"
proof -
  from assms obtain rep :: "'a \<Rightarrow> nat" and abs :: "nat \<Rightarrow> 'a" where t: "type_definition rep abs {0 ..< n}" by auto
  have "card (UNIV :: 'a set) = card {0 ..< n}" using t by (rule type_definition.card)
  also have "\<dots> = n" by auto
  finally have bn: "CARD ('a) = n" .
  have "finite (abs ` {0 ..< n})" by auto
  also have "abs ` {0 ..< n} = UNIV" using t by (rule type_definition.Abs_image)
  finally have "class.finite (TYPE('a))" unfolding class.finite_def .
  with bn show ?thesis by blast
qed  

ML_file \<open>cancel_card_constraint.ML\<close>


(* below you find an example what the attribute cancel_card_constraint can do and how
   it works internally *)

(*
(* input: some type based lemma with CARD inside, like t0 *)
consts P :: "nat \<Rightarrow> nat \<Rightarrow> bool" 
axiomatization where t0: "P (CARD ('a :: finite)) (CARD('a) * m)"

(* t0 is converted into a property without the cardinality constraint via the new attribute *)
lemma t_1_to_6: "n \<noteq> 0 \<Longrightarrow> P n (n * m)"
  by (rule t0[cancel_card_constraint])

(* The internal steps are as follows. *)

(* 1st step: pull out CARD and introduce new variable n *)
lemma t1: "CARD('a :: finite) = n \<Longrightarrow> P n (n * m)" 
  using t0[where 'a = 'a] by blast

(* 2nd step: get rid of sorts *)
lemma t2: "class.finite TYPE('a) \<Longrightarrow> CARD('a) = n \<Longrightarrow> P n (n * m)"
  by (rule t1[internalize_sort "?'a::finite"])

(* 3rd step: restructure thm so that first two assumptions are merged into one *)
lemma t3: "class.finite TYPE('a) \<and> CARD('a) = n \<Longrightarrow> P n (n * m)" 
  using t2 by blast

(* 4th step: choose an appropriate carrier set *)
lemma t4: "\<exists>Rep Abs. type_definition Rep Abs {0..<n} \<Longrightarrow> P n (n * m)"
  by (rule t3[OF type_impl_card_n])

(* 5th step: cancel type definition *)
lemma t5: "{0..<n} \<noteq> {} \<Longrightarrow> P n (n * m)"
  by (rule t4[cancel_type_definition])

(* 6th step: simplify non-empty assumption to obtain final theorem *)
lemma t6: "n \<noteq> 0 \<Longrightarrow> P n (n * m)" 
  by (rule t5[OF n_zero_nonempty])
*)

end
