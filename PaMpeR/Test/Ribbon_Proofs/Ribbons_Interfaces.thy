section {* Ribbon proof interfaces *}

theory Ribbons_Interfaces imports
  Ribbons_Basic
  Proofchain
  "HOL-Library.FSet"
begin

text {* Interfaces are the top and bottom boundaries through which diagrams 
  can be connected into a surrounding context. For instance, when composing two 
  diagrams vertically, the bottom interface of the upper diagram must match the 
  top interface of the lower diagram. 

  We define a datatype of concrete interfaces. We then quotient by the 
  associativity, commutativity and unity properties of our 
  horizontal-composition operator. *}

subsection {* Syntax of interfaces *}

datatype conc_interface =
  Ribbon_conc "assertion"
| HComp_int_conc "conc_interface" "conc_interface" (infix "\<otimes>\<^sub>c" 50)
| Emp_int_conc ("\<epsilon>\<^sub>c")
| Exists_int_conc "string" "conc_interface"

text {* We define an equivalence on interfaces. The first three rules make this 
  an equivalence relation. The next three make it a congruence. The next two 
  identify interfaces up to associativity and commutativity of @{term "op \<otimes>\<^sub>c"} 
  The final two make @{term "\<epsilon>\<^sub>c"} the left and right unit of @{term "op \<otimes>\<^sub>c"}. 
  *}
inductive
  equiv_int :: "conc_interface \<Rightarrow> conc_interface \<Rightarrow> bool" (infix "\<simeq>" 45)
where
  refl: "P \<simeq> P"
| sym: "P \<simeq> Q \<Longrightarrow> Q \<simeq> P"
| trans: "\<lbrakk>P \<simeq> Q; Q \<simeq> R\<rbrakk> \<Longrightarrow> P \<simeq> R"
| cong_hcomp1: "P \<simeq> Q \<Longrightarrow> P' \<otimes>\<^sub>c P \<simeq> P' \<otimes>\<^sub>c Q"
| cong_hcomp2: "P \<simeq> Q \<Longrightarrow> P \<otimes>\<^sub>c P' \<simeq> Q \<otimes>\<^sub>c P'"
| cong_exists: "P \<simeq> Q \<Longrightarrow> Exists_int_conc x P \<simeq> Exists_int_conc x Q"
| hcomp_conc_assoc: "P \<otimes>\<^sub>c (Q \<otimes>\<^sub>c R) \<simeq> (P \<otimes>\<^sub>c Q) \<otimes>\<^sub>c R"
| hcomp_conc_comm: "P \<otimes>\<^sub>c Q \<simeq> Q \<otimes>\<^sub>c P"
| hcomp_conc_unit1: "\<epsilon>\<^sub>c \<otimes>\<^sub>c P \<simeq> P"
| hcomp_conc_unit2: "P \<otimes>\<^sub>c \<epsilon>\<^sub>c \<simeq> P"

lemma equiv_int_cong_hcomp: 
  "\<lbrakk> P \<simeq> Q ; P' \<simeq> Q' \<rbrakk> \<Longrightarrow> P \<otimes>\<^sub>c P' \<simeq> Q \<otimes>\<^sub>c Q'"
by (metis cong_hcomp1 cong_hcomp2 equiv_int.trans)

quotient_type interface = "conc_interface" / "equiv_int"
apply (intro equivpI)
apply (intro reflpI, simp add: equiv_int.refl)
apply (intro sympI, simp add: equiv_int.sym)
apply (intro transpI, elim equiv_int.trans, simp add: equiv_int.refl)
done

lift_definition 
  Ribbon :: "assertion \<Rightarrow> interface" 
is "Ribbon_conc" .


lift_definition
  Emp_int :: "interface" ("\<epsilon>")
is "\<epsilon>\<^sub>c" .

lift_definition
  Exists_int :: "string \<Rightarrow> interface \<Rightarrow> interface"
is "Exists_int_conc"
by (rule equiv_int.cong_exists)

lift_definition
  HComp_int :: "interface \<Rightarrow> interface \<Rightarrow> interface" (infix "\<otimes>" 50)
is "HComp_int_conc" by (rule equiv_int_cong_hcomp)

lemma hcomp_comm: 
  "(P \<otimes> Q) = (Q \<otimes> P)"
by (rule hcomp_conc_comm[Transfer.transferred])

lemma hcomp_assoc:
  "(P \<otimes> (Q \<otimes> R)) = ((P \<otimes> Q) \<otimes> R)"
by (rule hcomp_conc_assoc[Transfer.transferred])

lemma emp_hcomp:
  "\<epsilon> \<otimes> P = P"
by (rule hcomp_conc_unit1[Transfer.transferred])

lemma hcomp_emp:
  "P \<otimes> \<epsilon> = P"
by (rule hcomp_conc_unit2[Transfer.transferred])

lemma comp_fun_commute_hcomp:
  "comp_fun_commute (op \<otimes>)"
by standard (simp add: hcomp_assoc fun_eq_iff, metis hcomp_comm)

subsection {* An iterated horizontal-composition operator *}

definition iter_hcomp :: "('a fset) \<Rightarrow> ('a \<Rightarrow> interface) \<Rightarrow> interface"
where
  "iter_hcomp X f \<equiv> ffold (op \<otimes> \<circ> f) \<epsilon> X"

syntax "iter_hcomp_syntax" :: 
  "'a \<Rightarrow> ('a fset) \<Rightarrow> ('a \<Rightarrow> interface) \<Rightarrow> interface"
      ("(\<Otimes>_|\<in>|_. _)" [0,0,10] 10)
translations "\<Otimes>x|\<in>|M. e" == "CONST iter_hcomp M (\<lambda>x. e)"

term "\<Otimes>P|\<in>|Ps. f P" -- "this is eta-expanded, so prints in expanded form"
term "\<Otimes>P|\<in>|Ps. f" -- "this isn't eta-expanded, so prints as written"

lemma iter_hcomp_cong:
  assumes "\<forall>v \<in> fset vs. \<phi> v = \<phi>' v"
  shows "(\<Otimes>v|\<in>|vs. \<phi> v) = (\<Otimes>v|\<in>|vs. \<phi>' v)"
using assms unfolding iter_hcomp_def  
by (auto simp add: fmember.rep_eq comp_fun_commute.comp_comp_fun_commute comp_fun_commute_hcomp 
  intro: ffold_cong)

lemma iter_hcomp_empty:
  shows "(\<Otimes>x |\<in>| {||}. p x) = \<epsilon>"
by (metis comp_fun_commute.ffold_empty comp_fun_commute_hcomp iter_hcomp_def)

lemma iter_hcomp_insert:
  assumes "v |\<notin>| ws"
  shows "(\<Otimes>x |\<in>| finsert v ws. p x) = (p v \<otimes> (\<Otimes>x |\<in>| ws. p x))"
proof -
  interpret comp_fun_commute "(op \<otimes> \<circ> p)"
  by (metis comp_fun_commute.comp_comp_fun_commute comp_fun_commute_hcomp)
  from assms show ?thesis unfolding iter_hcomp_def by auto
qed

lemma iter_hcomp_union:
  assumes "vs |\<inter>| ws = {||}"
  shows "(\<Otimes>x |\<in>| vs |\<union>| ws. p x) = ((\<Otimes>x |\<in>| vs. p x) \<otimes> (\<Otimes>x |\<in>| ws. p x))"
using assms
by (induct vs) (auto simp add: emp_hcomp iter_hcomp_empty iter_hcomp_insert hcomp_assoc)


subsection {* Semantics of interfaces *}

text {* The semantics of an interface is an assertion. *}
fun
  conc_asn :: "conc_interface \<Rightarrow> assertion"
where
  "conc_asn (Ribbon_conc p) = p"
| "conc_asn (P \<otimes>\<^sub>c Q) = (conc_asn P) \<star> (conc_asn Q)"
| "conc_asn (\<epsilon>\<^sub>c) = Emp"
| "conc_asn (Exists_int_conc x P) = Exists x (conc_asn P)"

lift_definition 
  asn :: "interface \<Rightarrow> assertion"
is "conc_asn"
by (induct_tac rule:equiv_int.induct) (auto simp add: star_assoc star_comm star_rot emp_star)

lemma asn_simps [simp]:
  "asn (Ribbon p) = p"
  "asn (P \<otimes> Q) = (asn P) \<star> (asn Q)"
  "asn \<epsilon> = Emp"
  "asn (Exists_int x P) = Exists x (asn P)"
by (transfer, simp)+

subsection {* Program variables mentioned in an interface. *}

fun
  rd_conc_int :: "conc_interface \<Rightarrow> string set"
where
  "rd_conc_int (Ribbon_conc p) = rd_ass p"
| "rd_conc_int (P \<otimes>\<^sub>c Q) = rd_conc_int P \<union> rd_conc_int Q"
| "rd_conc_int (\<epsilon>\<^sub>c) = {}"
| "rd_conc_int (Exists_int_conc x P) = rd_conc_int P"

lift_definition
  rd_int :: "interface \<Rightarrow> string set"
is "rd_conc_int"
by (induct_tac rule: equiv_int.induct) auto
  
text {* The program variables read by an interface are the same as those read 
  by its corresponding assertion. *}

lemma rd_int_is_rd_ass:
  "rd_ass (asn P) = rd_int P"
by (transfer, induct_tac P, auto simp add: rd_star rd_exists rd_emp) 

text {* Here is an iterated version of the Hoare logic sequencing rule. *}

lemma seq_fold: 
  "\<And>\<Pi>. \<lbrakk> length cs = chainlen \<Pi> ; p1 = asn (pre \<Pi>) ; p2 = asn (post \<Pi>) ; 
  \<And>i. i < chainlen \<Pi> \<Longrightarrow> prov_triple 
  (asn (fst3 (nthtriple \<Pi> i)), cs ! i, asn (thd3 (nthtriple \<Pi> i))) \<rbrakk>
  \<Longrightarrow> prov_triple (p1, foldr (op ;;) cs Skip, p2)"
proof (induct cs arbitrary: p1 p2)
  case Nil
  thus ?case 
  by (cases \<Pi>, auto simp add: prov_triple.skip)
next
  case (Cons c cs)
  obtain p x \<Pi>' where \<Pi>_def: "\<Pi> = \<lbrace> p \<rbrace> \<cdot> x \<cdot> \<Pi>'" 
  by (metis Cons.prems(1) chain.exhaust chainlen.simps(1) impossible_Cons le0)
  show ?case 
  apply (unfold foldr_Cons o_def)
  apply (rule prov_triple.seq[where q = "asn (pre \<Pi>')"])
  apply (unfold Cons.prems(2) Cons.prems(3) \<Pi>_def pre.simps post.simps)
  apply (subst nth_Cons_0[of c cs, symmetric])
  apply (subst fst3_simp[of p x "pre \<Pi>'", symmetric])
  apply (subst(2) thd3_simp[of p x "pre \<Pi>'", symmetric])
  apply (subst(1 2) nthtriple.simps(1)[of p x "\<Pi>'", symmetric])
  apply (fold \<Pi>_def, intro Cons.prems(4), simp add: \<Pi>_def)
  apply (intro Cons.hyps, insert \<Pi>_def Cons.prems(1), auto)
  apply (fold nth_Cons_Suc[of c cs] nthtriple.simps(2)[of p x "\<Pi>'"])
  apply (fold \<Pi>_def, intro Cons.prems(4), simp add: \<Pi>_def)
  done
qed

end
