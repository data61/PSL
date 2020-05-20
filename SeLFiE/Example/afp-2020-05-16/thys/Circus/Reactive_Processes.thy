section\<open>Reactive processes\<close>

theory Reactive_Processes
imports Designs "HOL-Library.Sublist"
(* isabelle2012 "HOL-Library.List_Prefix" *)
begin


text \<open>Following the way of UTP to describe reactive processes, more observational
variables are needed to record the interaction with the environment. Three observational 
variables are defined for this subset of relations: $wait$, $tr$ and $ref$.
The boolean variable $wait$ records if the process is waiting for an interaction
or has terminated. $tr$ records the list (trace) of interactions the process has
performed so far. The variable $ref$ contains the set of interactions (events) the
process may refuse to perform.\<close>

text \<open>In this section, we introduce first some preliminary notions, useful for 
 trace manipulations. The definitions of reactive process alphabets and healthiness 
conditions are also given. Finally, proved lemmas and theorems are listed.\<close>

subsection \<open>Preliminaries\<close>

type_synonym '\<alpha> trace = "'\<alpha> list"

fun list_diff::"'\<alpha> list \<Rightarrow> '\<alpha> list \<Rightarrow> '\<alpha> list option" where
   "list_diff l [] = Some l"
  | "list_diff [] l = None"
  | "list_diff (x#xs) (y#ys) = (if (x = y) then (list_diff xs ys) else None)"

instantiation  list :: (type) minus
begin
definition list_minus : "l1 - l2 \<equiv> the (list_diff l1 l2)"
instance ..
end

lemma list_diff_empty [simp]: "the (list_diff l []) = l"
by (cases l) auto

lemma prefix_diff_empty [simp]: "l  - [] = l"
by (induct l) (auto simp: list_minus)

lemma prefix_diff_eq [simp]: "l - l = []"
by (induct l) (auto simp: list_minus)

lemma prefix_diff [simp]: "(l @ t) - l = t"
by (induct l) (auto simp: list_minus)

lemma prefix_subst [simp]: "l @ t = m \<Longrightarrow> m - l = t"
by (auto)

lemma prefix_subst1 [simp]: "m = l @ t \<Longrightarrow> m - l = t"
by (auto)

lemma prefix_diff1 [simp]: "((l @ m) @ t) - (l @ m) = t"
by (rule prefix_diff)

lemma prefix_diff2 [simp]: "(l @ (m @ t)) - (l @ m) = t"
apply (simp only: append_assoc [symmetric])
apply (rule prefix_diff1)
done

lemma prefix_diff3 [simp]: "(l @ m) - (l @ t) = (m - t)"
by (induct l, auto simp: list_minus)

lemma prefix_diff4 [simp]: "(a # m) - (a # t) = (m - t)"
by (auto simp: list_minus)


class ev_eq = 
  fixes ev_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes refl: "ev_eq a a"
  assumes comm: "ev_eq a b = ev_eq b a"

definition "filter_chan_set a cs = (\<not> (\<exists> e\<in>cs. ev_eq a e))"

lemma in_imp_not_fcs:
"x\<in>S \<Longrightarrow> \<not> filter_chan_set x S"
apply (auto simp: filter_chan_set_def)
apply (rule_tac bexI, auto simp: refl)
done

fun tr_filter::"'a::ev_eq list \<Rightarrow> 'a set \<Rightarrow> 'a list" where
    "tr_filter [] cs = []"
  | "tr_filter (x#xs) cs = (if (filter_chan_set x cs) then (x#(tr_filter xs cs))
                                                                  else (tr_filter xs cs))"


lemma tr_filter_conc: "(tr_filter (a@b) cs) = ((tr_filter a cs) @ (tr_filter b cs))"
by (induct a, auto)

lemma filter_chan_set_hd_tr_filter:
"tr_filter l cs \<noteq> [] --> filter_chan_set (hd (tr_filter l cs)) cs"
by (induct l, auto)

lemma tr_filter_conc_eq1: 
"(a@b = (tr_filter (a@c) cs)) \<longrightarrow> (b = (tr_filter c cs))"
apply (induct a, auto)
apply (case_tac "tr_filter (a2 @ c) cs = []", simp_all)
apply (drule filter_chan_set_hd_tr_filter[rule_format])
apply (case_tac "tr_filter (a2 @ c) cs", simp_all)
done

lemma tr_filter_conc_eq2: 
"(a@b = (tr_filter (a@c) cs)) \<longrightarrow> (a = (tr_filter a cs))"
apply (induct a, auto)
apply (case_tac "tr_filter (a2 @ c) cs = []", simp_all)
apply (drule filter_chan_set_hd_tr_filter[rule_format])
apply (case_tac "tr_filter (a2 @ c) cs", simp_all)
apply (case_tac "tr_filter (a2 @ c) cs = []", simp_all)
apply (drule filter_chan_set_hd_tr_filter[rule_format])
apply (case_tac "tr_filter (a2 @ c) cs", simp_all)
done

lemma tr_filter_conc_eq:
"(a@b = (tr_filter (a@c) cs)) = (b = (tr_filter c cs) & a = (tr_filter a cs))"
apply (rule, rule)
apply (rule tr_filter_conc_eq1[rule_format, of a], clarsimp)
apply (rule tr_filter_conc_eq2[rule_format, of a b c], clarsimp)
apply (clarsimp simp: tr_filter_conc)
done

lemma tr_filter_conc_eq3:
"(b = (tr_filter (a@c) cs)) = (\<exists> b1 b2. b=b1@b2 & b2 = (tr_filter c cs) & b1 = (tr_filter a cs))"
by (rule, auto simp: tr_filter_conc)

lemma tr_filter_un:
"tr_filter l (s1 \<union> s2) = tr_filter (tr_filter l s1) s2"
by (induct l, auto simp: filter_chan_set_def)


instantiation list :: (ev_eq) ev_eq
begin
fun ev_eq_list where
    "ev_eq_list [] [] = True"
  | "ev_eq_list l [] = False"
  | "ev_eq_list [] l = False"
  | "ev_eq_list (x#xs) (y#ys) = (if (ev_eq x y) then (ev_eq_list xs ys) else False)"
instance 
  proof
  fix a::"'a::ev_eq list" show "ev_eq a a"
  by (induct a, auto simp: ev_eq_class.refl)
  next
  fix a b::"'a::ev_eq list" show "ev_eq a b = ev_eq b a"
  apply (cases a)
  apply (cases b, simp_all add: ev_eq_class.comm)
  apply (hypsubst_thin)
  apply (induct b, simp_all add: ev_eq_class.comm)
  apply (case_tac "ev_eq aa a", simp_all add: ev_eq_class.comm)
  apply (case_tac "list = []", simp_all)
  apply (case_tac "b", simp_all)
  apply (atomize)
  apply (erule_tac x="hd list" in allE)
  apply (erule_tac x="tl list" in allE)
  apply (subst (asm) hd_Cons_tl, simp_all)
done
qed
end

subsection \<open>Definitions\<close>

(* isabelle 2013 *)

abbreviation subl::"'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<le> _") 
where "l1 \<le> l2 == Sublist.prefix l1 l2"

lemma list_diff_empty_eq: "l1 - l2 = [] \<Longrightarrow> l2 \<le> l1 \<Longrightarrow> l1 = l2"
by (auto simp: prefix_def)


(* end isabelle 2013 *)

text \<open>The definitions of reactive process alphabets and healthiness conditions are given
in the following. The healthiness conditions of reactive processes are defined by 
$R1$, $R2$, $R3$ and their composition $R$.\<close>

type_synonym '\<theta> refusal = "'\<theta> set"
  
record '\<theta> alpha_rp  = alpha_d + 
                         wait:: bool
                         tr  :: "'\<theta> trace"
                         ref :: "'\<theta> refusal"

text\<open>Note that we define here the class of UTP alphabets that contain
$wait$, $tr$ and $ref$, or, in other words, we define here the class of reactive process
alphabets.\<close>

type_synonym ('\<theta>,'\<sigma>) alphabet_rp  = "('\<theta>,'\<sigma>) alpha_rp_scheme alphabet"
type_synonym ('\<theta>,'\<sigma>) relation_rp  = "('\<theta>,'\<sigma>) alphabet_rp relation"

definition "diff_tr s1 s2 = ((tr s1) - (tr s2))"

definition spec :: "[bool, bool, ('\<theta>,'\<sigma>) relation_rp] \<Rightarrow> ('\<theta>,'\<sigma>) relation_rp"
where "spec b b' P \<equiv> \<lambda> (A, A'). P (A\<lparr>wait := b'\<rparr>, A'\<lparr>ok := b\<rparr>)"

abbreviation Speciftt ("_\<^sup>t\<^sub>t") where "(P)\<^sup>t\<^sub>t \<equiv> spec True True P"

abbreviation Specifff ("_\<^sup>f\<^sub>f") where "(P)\<^sup>f\<^sub>f \<equiv> spec False False P"

abbreviation Speciftf ("_\<^sup>t\<^sub>f") where "(P)\<^sup>t\<^sub>f \<equiv> spec True False P"

abbreviation Specifft ("_\<^sup>f\<^sub>t") where "(P)\<^sup>f\<^sub>t \<equiv> spec False True P"

definition R1::"(('\<theta>,'\<sigma>) alphabet_rp) Healthiness_condition"
where "R1 (P)  \<equiv>  \<lambda>(A, A'). (P (A, A')) \<and> (tr A \<le> tr A')"

definition R2::"(('\<theta>,'\<sigma>) alphabet_rp) Healthiness_condition"
where "R2 (P)  \<equiv> \<lambda>(A, A'). (P (A\<lparr>tr:=[]\<rparr>,A'\<lparr>tr:= tr A' - tr A\<rparr>) \<and> tr A \<le> tr A')"

definition \<Pi>rea   
where "\<Pi>rea  \<equiv> \<lambda>(A, A'). (\<not>ok A \<and> tr A \<le> tr A') \<or> (ok A' \<and> tr A = tr A' 
                            \<and> (wait A = wait A') \<and> ref A = ref A' \<and> more A = more A')"

definition R3::"(('\<theta>,'\<sigma>) alphabet_rp) Healthiness_condition"
where "R3 (P)  \<equiv> (\<Pi>rea \<triangleleft> wait o fst \<triangleright> P)"

definition R::"(('\<theta>,'\<sigma>) alphabet_rp) Healthiness_condition" 
where "R  \<equiv> R3 o R2 o R1"

lemmas rp_defs = R1_def R2_def \<Pi>rea_def R3_def R_def spec_def

subsection \<open>Proofs\<close>

lemma tr_filter_empty [simp]: "tr_filter l {} = l"
by (induct l) (auto simp: filter_chan_set_def)

lemma trf_imp_filtercs: "\<lbrakk>xs = tr_filter ys cs; xs \<noteq> []\<rbrakk> \<Longrightarrow> filter_chan_set (hd xs) cs"
apply (induct xs, auto)
apply (induct ys, auto)
apply (case_tac "filter_chan_set a cs", auto)
done

lemma filtercs_imp_trf: 
"\<lbrakk>filter_chan_set x cs; xs = tr_filter ys cs\<rbrakk> \<Longrightarrow> x#xs = tr_filter (x#ys) cs"
by (induct xs) auto

lemma alpha_d_more_eqI:
  assumes "tr r = tr r'" "wait r = wait r'" "ref r = ref r'" "more r = more r'"
  shows "alpha_d.more r = alpha_d.more r'"
  using assms by (cases r, cases r') auto

lemma alpha_d_more_eqE:
  assumes "alpha_d.more r = alpha_d.more r'"
  obtains "tr r = tr r'" "wait r = wait r'" "ref r = ref r'" "more r = more r'"
  using assms by (cases r, cases r') auto

lemma alpha_rp_eqE:
  assumes "r = r'"
  obtains "ok r = ok r'" "tr r = tr r'" "wait r = wait r'" "ref r = ref r'" "more r = more r'"
  using assms by (cases r, cases r') auto

lemma R_idem: "R o R = R"
by (auto simp: rp_defs design_defs fun_eq_iff split: cond_splits)

lemma R_idem2: "R (R P) = R P"
by (auto simp: rp_defs design_defs fun_eq_iff split: cond_splits)

lemma R1_idem: "R1 o R1 = R1"
by (auto simp: rp_defs design_defs)

lemma R1_idem2: "R1 (R1 x) = R1 x"
by (auto simp: rp_defs design_defs)

lemma R2_idem: "R2 o R2 = R2"
by (auto simp: rp_defs design_defs fun_eq_iff prefix_def)

lemma R2_idem2: "R2 (R2 x) = R2 x"
by (auto simp: rp_defs design_defs fun_eq_iff prefix_def)

lemma R3_idem: "R3 o R3 = R3"
by (auto simp: rp_defs design_defs fun_eq_iff split: cond_splits)

lemma R3_idem2: "R3 (R3 x) = R3 x"
by (auto simp: R3_idem[simplified Fun.comp_def fun_eq_iff] fun_eq_iff)

lemma R1_R2_commute: "(R1 o R2) = (R2 o R1)"
by (auto simp: rp_defs design_defs fun_eq_iff prefix_def)

lemma R1_R3_commute: "(R1 o R3) = (R3 o R1)"
by (auto simp: rp_defs design_defs fun_eq_iff split: cond_splits)

lemma R2_R3_commute: "R2 o R3 = R3 o R2"
by (auto simp: rp_defs design_defs fun_eq_iff prefix_def split: cond_splits)

lemma R_abs_R1: "R o R1 = R"
apply (auto simp: R_def)
apply (subst (3) R1_idem[symmetric])
apply (auto)
done

lemma R_abs_R2: "R o R2 = R"
by (auto simp: rp_defs design_defs fun_eq_iff)

lemma R_abs_R3: "R o R3 = R"
by (auto simp: rp_defs design_defs fun_eq_iff split: cond_splits)

lemma R_is_R1:
  assumes A: "P is R healthy"
  shows  "P is R1 healthy"
proof -
  have "R P = P"
    using assms by (simp_all only: Healthy_def)
  moreover
  have "(R P) is R1 healthy"
    by (auto simp add: design_defs rp_defs fun_eq_iff split: cond_splits)
  ultimately show ?thesis by simp
qed

lemma R_is_R2:
  assumes A: "P is R healthy"
  shows  "P is R2 healthy"
proof -
  have "R P = P"
    using assms by (simp_all only: Healthy_def)
  moreover
  have "(R P) is R2 healthy"
    by (auto simp add: design_defs rp_defs fun_eq_iff prefix_def split: cond_splits)
  ultimately show ?thesis by simp
qed

lemma R_is_R3:
  assumes A: "P is R healthy"
  shows  "P is R3 healthy"
proof -
  have "R P = P"
    using assms by (simp_all only: Healthy_def)
  moreover
  have "(R P) is R3 healthy"
    by (auto simp add: design_defs rp_defs fun_eq_iff split: cond_splits)
  ultimately show ?thesis by simp
qed

lemma R_disj:
  assumes A: "P is R healthy"
  assumes B: "Q is R healthy"
  shows  "(P \<or> Q) is R healthy"
proof -
  have "R P = P" and "R Q = Q"
    using assms by (simp_all only: Healthy_def)
  moreover
  have "((R P) \<or> (R Q)) is R healthy"
    by (auto simp add: design_defs rp_defs fun_eq_iff split: cond_splits)
  ultimately show ?thesis by simp
qed

lemma R_disj2:  "R (P \<or> Q) = (R P \<or> R Q)"
apply (subst R_disj[simplified Healthy_def, where P="R P"])
apply (simp_all add: R_idem2)
apply (auto simp: fun_eq_iff rp_defs split: cond_splits)
done

lemma R1_comp:
  assumes "P is R1 healthy"
    and "Q is R1 healthy"
  shows "(P;;Q) is R1 healthy"
proof -
  have "R1 P = P" and "R1 Q = Q"
    using assms by (simp_all only: Healthy_def)
  moreover
  have "((R1 P) ;; (R1 Q)) is R1 healthy"
    by (auto simp add: design_defs rp_defs fun_eq_iff split: cond_splits)
  ultimately show ?thesis by simp
qed

lemma R1_comp2:
  assumes A: "P is R1 healthy"
  assumes B: "Q is R1 healthy"
  shows  "R1 (P;;Q) = ((R1 P);;Q)"
using A B
apply (subst R1_comp[simplified Healthy_def, symmetric])
apply (auto simp: fun_eq_iff rp_defs design_defs)
done

lemma J_is_R1: "J is R1 healthy"
  by (auto simp: rp_defs design_defs fun_eq_iff elim: alpha_d_more_eqE)

lemma J_is_R2: "J is R2 healthy"
  by (auto simp: rp_defs design_defs fun_eq_iff prefix_def
    elim!: alpha_d_more_eqE intro!: alpha_d_more_eqI)

lemma R1_H2_commute2: "R1 (H2 P) = H2 (R1 P)"
  by (auto simp add: H2_def R1_def J_def fun_eq_iff
    elim!: alpha_d_more_eqE intro!: alpha_d_more_eqI)

lemma R1_H2_commute: "R1 o H2 = H2 o R1"
by (auto simp: R1_H2_commute2)

lemma R2_H2_commute2: "R2 (H2 P) = H2 (R2 P)"
apply (auto simp add: fun_eq_iff rp_defs design_defs strict_prefix_def)
apply (rule_tac b="ba\<lparr>tr := tr a @ tr ba\<rparr>" in comp_intro)
apply (auto simp: fun_eq_iff prefix_def
  elim!: alpha_d_more_eqE alpha_rp_eqE intro!: alpha_d_more_eqI alpha_rp.equality)
apply (rule_tac b="ba\<lparr>tr := tr a @ tr ba\<rparr>" in comp_intro,
  auto simp: elim: alpha_d_more_eqE alpha_rp_eqE intro: alpha_d_more_eqI alpha_rp.equality)
apply (rule_tac b="ba\<lparr>tr := tr a @ tr ba\<rparr>" in comp_intro,
  auto simp: elim: alpha_d_more_eqE alpha_rp_eqE intro: alpha_d_more_eqI alpha_rp.equality)
apply (rule_tac x=zs in exI, auto)+

done

lemma R2_H2_commute: "R2 o H2 = H2 o R2"
by (auto simp: R2_H2_commute2)

lemma R3_H2_commute2: "R3 (H2 P) = H2 (R3 P)"
apply (auto simp: fun_eq_iff rp_defs design_defs strict_prefix_def 
            elim: alpha_d_more_eqE split: cond_splits)
done

lemma R3_H2_commute: "R3 o H2 = H2 o R3"
by (auto simp: R3_H2_commute2)

lemma R_join: 
  assumes "x is R healthy"
  and "y is R healthy"
  shows "(x \<sqinter> y) is R healthy"
proof -
  have "R x = x" and "R y = y"
    using assms by (simp_all only: Healthy_def)
  moreover
  have "((R x) \<sqinter> (R y)) is R healthy"
    by (auto simp add: design_defs rp_defs fun_eq_iff split: cond_splits)
  ultimately show ?thesis by simp
qed

lemma R_meet:
  assumes A: "x is R healthy"
  and B:"y is R healthy"
  shows "(x \<squnion> y) is R healthy"
proof -
  have "R x = x" and "R y = y"
    using assms by (simp_all only: Healthy_def)
  moreover
  have "((R x) \<squnion> (R y)) is R healthy"
    by (auto simp add: design_defs rp_defs fun_eq_iff split: cond_splits)
  ultimately show ?thesis by simp
qed


lemma R_H2_commute: "R o H2 = H2 o R"
apply (auto simp add: rp_defs design_defs fun_eq_iff split: cond_splits 
                     elim: alpha_d_more_eqE)
apply (rule_tac b="ba\<lparr>tr := tr b\<rparr>" in comp_intro, auto split: cond_splits
  elim!: alpha_d_more_eqE alpha_rp_eqE intro!: alpha_d_more_eqI alpha_rp.equality)
apply (rule_tac s=ba in subst, auto intro!: alpha_d_more_eqI alpha_rp.equality)
apply (rule_tac s=ba in subst, auto intro!: alpha_d_more_eqI alpha_rp.equality)
apply (rule_tac b="ba\<lparr>tr := tr b\<rparr>" in comp_intro, auto split: cond_splits)
apply (rule_tac s=ba in subst,
  auto elim: alpha_d_more_eqE alpha_rp_eqE intro: alpha_d_more_eqI alpha_rp.equality)
apply (rule_tac b="ba\<lparr>tr := tr b\<rparr>" in comp_intro,
  auto elim: alpha_d_more_eqE alpha_rp_eqE intro: alpha_d_more_eqI alpha_rp.equality split: cond_splits)
apply (rule_tac s=ba in subst,
  auto elim: alpha_d_more_eqE alpha_rp_eqE intro: alpha_d_more_eqI alpha_rp.equality)
done

lemma R_H2_commute2: "R (H2 P) = H2 (R P)"
by (auto simp: fun_eq_iff R_H2_commute[simplified fun_eq_iff Fun.comp_def])

end
