(*  Author:     Tobias Nipkow
    Copyright   1998 TUM

To generate a regular expression, the alphabet must be finite.
regexp needs to be supplied with an 'a list for a unique order

add_Atom d i j r a = (if d a i = j then Union r (Atom a) else r)
atoms d i j as = foldl (add_Atom d i j) Empty as

regexp as d i j 0 = (if i=j then Union (Star Empty) (atoms d i j as)
                        else atoms d i j as
*)

section "From deterministic automata to regular sets"

theory RegSet_of_nat_DA
imports "Regular-Sets.Regular_Set" DA
begin

type_synonym 'a nat_next = "'a \<Rightarrow> nat \<Rightarrow> nat"

abbreviation
  deltas :: "'a nat_next \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "deltas \<equiv> foldl2"

primrec trace :: "'a nat_next \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat list"  where
"trace d i [] = []" |
"trace d i (x#xs) = d x i # trace d (d x i) xs"

(* conversion a la Warshall *)

primrec regset :: "'a nat_next \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list set" where
"regset d i j 0 = (if i=j then insert [] {[a] | a. d a i = j}
                          else {[a] | a. d a i = j})" |
"regset d i j (Suc k) =
  regset d i j k \<union>
  (regset d i k k) @@ (star(regset d k k k)) @@ (regset d k j k)"

definition
 regset_of_DA :: "('a,nat)da \<Rightarrow> nat \<Rightarrow> 'a list set" where
"regset_of_DA A k = (\<Union>j\<in>{j. j<k \<and> fin A j}. regset (next A) (start A) j k)"

definition
 bounded :: "'a nat_next \<Rightarrow> nat \<Rightarrow> bool" where
"bounded d k = (\<forall>n. n < k \<longrightarrow> (\<forall>x. d x n < k))"

declare
  in_set_butlast_appendI[simp,intro] less_SucI[simp] image_eqI[simp]

(* Lists *)

lemma butlast_empty[iff]:
  "(butlast xs = []) = (case xs of [] \<Rightarrow> True | y#ys \<Rightarrow> ys=[])"
by (cases xs) simp_all

lemma in_set_butlast_concatI:
 "x:set(butlast xs) \<Longrightarrow> xs:set xss \<Longrightarrow> x:set(butlast(concat xss))"
apply (induct "xss")
 apply simp
apply (simp add: butlast_append del: ball_simps)
apply (rule conjI)
 apply (clarify)
 apply (erule disjE)
  apply (blast)
 apply (subgoal_tac "xs=[]")
  apply simp
 apply (blast)
apply (blast dest: in_set_butlastD)
done

(* Regular sets *)

(* The main lemma:
   how to decompose a trace into a prefix, a list of loops and a suffix.
*)
lemma decompose[rule_format]:
 "\<forall>i. k \<in> set(trace d i xs) \<longrightarrow> (\<exists>pref mids suf.
  xs = pref @ concat mids @ suf \<and>
  deltas d pref i = k \<and> (\<forall>n\<in>set(butlast(trace d i pref)). n \<noteq> k) \<and>
  (\<forall>mid\<in>set mids. (deltas d mid k = k) \<and>
                  (\<forall>n\<in>set(butlast(trace d k mid)). n \<noteq> k)) \<and>
  (\<forall>n\<in>set(butlast(trace d k suf)). n \<noteq> k))"
apply (induct "xs")
 apply (simp)
apply (rename_tac a as)
apply (intro strip)
apply (case_tac "d a i = k")
 apply (rule_tac x = "[a]" in exI)
 apply simp
 apply (case_tac "k : set(trace d (d a i) as)")
  apply (erule allE)
  apply (erule impE)
   apply (assumption)
  apply (erule exE)+
  apply (rule_tac x = "pref#mids" in exI)
  apply (rule_tac x = "suf" in exI)
  apply simp
 apply (rule_tac x = "[]" in exI)
 apply (rule_tac x = "as" in exI)
 apply simp
 apply (blast dest: in_set_butlastD)
apply simp
apply (erule allE)
apply (erule impE)
 apply (assumption)
apply (erule exE)+
apply (rule_tac x = "a#pref" in exI)
apply (rule_tac x = "mids" in exI)
apply (rule_tac x = "suf" in exI)
apply simp
done

lemma length_trace[simp]: "\<And>i. length(trace d i xs) = length xs"
by (induct "xs") simp_all

lemma deltas_append[simp]:
  "\<And>i. deltas d (xs@ys) i = deltas d ys (deltas d xs i)"
by (induct "xs") simp_all

lemma trace_append[simp]:
  "\<And>i. trace d i (xs@ys) = trace d i xs @ trace d (deltas d xs i) ys"
by (induct "xs") simp_all

lemma trace_concat[simp]:
 "(\<forall>xs \<in> set xss. deltas d xs i = i) \<Longrightarrow>
  trace d i (concat xss) = concat (map (trace d i) xss)"
by (induct "xss") simp_all

lemma trace_is_Nil[simp]: "\<And>i. (trace d i xs = []) = (xs = [])"
by (case_tac "xs") simp_all

lemma trace_is_Cons_conv[simp]:
 "(trace d i xs = n#ns) =
  (case xs of [] \<Rightarrow> False | y#ys \<Rightarrow> n = d y i \<and> ns = trace d n ys)"
apply (case_tac "xs")
apply simp_all
apply (blast)
done

lemma set_trace_conv:
 "\<And>i. set(trace d i xs) =
  (if xs=[] then {} else insert(deltas d xs i)(set(butlast(trace d i xs))))"
apply (induct "xs")
 apply (simp)
apply (simp add: insert_commute)
done

lemma deltas_concat[simp]:
 "(\<forall>mid\<in>set mids. deltas d mid k = k) \<Longrightarrow> deltas d (concat mids) k = k"
by (induct mids) simp_all

lemma lem: "[| n < Suc k; n \<noteq> k |] ==> n < k"
by arith

lemma regset_spec:
 "\<And>i j xs. xs \<in> regset d i j k =
        ((\<forall>n\<in>set(butlast(trace d i xs)). n < k) \<and> deltas d xs i = j)"
apply (induct k)
 apply(simp split: list.split)
 apply(fastforce)
apply (simp add: conc_def)
apply (rule iffI)
 apply (erule disjE)
  apply simp
 apply (erule exE conjE)+
 apply simp
 apply (subgoal_tac
      "(\<forall>m\<in>set(butlast(trace d k xsb)). m < Suc k) \<and> deltas d xsb k = k")
  apply (simp add: set_trace_conv butlast_append ball_Un)
 apply (erule star_induct)
  apply (simp)
 apply (simp add: set_trace_conv butlast_append ball_Un)
apply (case_tac "k : set(butlast(trace d i xs))")
 prefer 2 apply (rule disjI1)
 apply (blast intro:lem)
apply (rule disjI2)
apply (drule in_set_butlastD[THEN decompose])
apply (clarify)
apply (rule_tac x = "pref" in exI)
apply simp
apply (rule conjI)
 apply (rule ballI)
 apply (rule lem)
  prefer 2 apply simp
 apply (drule bspec) prefer 2 apply assumption
 apply simp
apply (rule_tac x = "concat mids" in exI)
apply (simp)
apply (rule conjI)
 apply (rule concat_in_star)
 apply (clarsimp simp: subset_iff)
 apply (rule lem)
  prefer 2 apply simp
 apply (drule bspec) prefer 2 apply assumption
 apply (simp add: image_eqI in_set_butlast_concatI)
apply (rule ballI)
apply (rule lem)
 apply auto
done

lemma trace_below:
 "bounded d k \<Longrightarrow> \<forall>i. i < k \<longrightarrow> (\<forall>n\<in>set(trace d i xs). n < k)"
apply (unfold bounded_def)
apply (induct "xs")
 apply simp
apply (simp (no_asm))
apply (blast)
done

lemma regset_below:
 "[| bounded d k; i < k; j < k |] ==>
  regset d i j k = {xs. deltas d xs i = j}"
apply (rule set_eqI)
apply (simp add: regset_spec)
apply (blast dest: trace_below in_set_butlastD)
done

lemma deltas_below:
 "\<And>i. bounded d k \<Longrightarrow> i < k \<Longrightarrow> deltas d w i < k"
apply (unfold bounded_def)
apply (induct "w")
 apply simp_all
done

lemma regset_DA_equiv:
 "[| bounded (next A) k; start A < k; j < k |] ==>
  w : regset_of_DA A k = accepts A w"
apply(unfold regset_of_DA_def)
apply (simp cong: conj_cong
            add: regset_below deltas_below accepts_def delta_def)
done

end
