section\<open>Names and generic extensions\<close>

theory Names
  imports
    Forcing_Data
    Interface
    Recursion_Thms
    Synthetic_Definition
begin

definition
  SepReplace :: "[i, i\<Rightarrow>i, i\<Rightarrow> o] \<Rightarrow> i" where
  "SepReplace(A,b,Q) \<equiv> {y . x\<in>A, y=b(x) \<and> Q(x)}"

syntax
  "_SepReplace"  :: "[i, pttrn, i, o] \<Rightarrow> i"  ("(1{_ ../ _ \<in> _, _})")
translations
  "{b .. x\<in>A, Q}" => "CONST SepReplace(A, \<lambda>x. b, \<lambda>x. Q)"

lemma Sep_and_Replace: "{b(x) .. x\<in>A, P(x) } = {b(x) . x\<in>{y\<in>A. P(y)}}"
  by (auto simp add:SepReplace_def)

lemma SepReplace_subset : "A\<subseteq>A'\<Longrightarrow> {b .. x\<in>A, Q}\<subseteq>{b .. x\<in>A', Q}"
  by (auto simp add:SepReplace_def)

lemma SepReplace_iff [simp]: "y\<in>{b(x) .. x\<in>A, P(x)} \<longleftrightarrow> (\<exists>x\<in>A. y=b(x) & P(x))"
  by (auto simp add:SepReplace_def)

lemma SepReplace_dom_implies :
  "(\<And> x . x \<in>A \<Longrightarrow> b(x) = b'(x))\<Longrightarrow> {b(x) .. x\<in>A, Q(x)}={b'(x) .. x\<in>A, Q(x)}"
  by  (simp add:SepReplace_def)

lemma SepReplace_pred_implies :
  "\<forall>x. Q(x)\<longrightarrow> b(x) = b'(x)\<Longrightarrow> {b(x) .. x\<in>A, Q(x)}={b'(x) .. x\<in>A, Q(x)}"
  by  (force simp add:SepReplace_def)

subsection\<open>The well-founded relation \<^term>\<open>ed\<close>\<close>

lemma eclose_sing : "x \<in> eclose(a) \<Longrightarrow> x \<in> eclose({a})"
  by(rule subsetD[OF mem_eclose_subset],simp+)

lemma ecloseE :
  assumes  "x \<in> eclose(A)"
  shows  "x \<in> A \<or> (\<exists> B \<in> A . x \<in> eclose(B))"
  using assms
proof (induct rule:eclose_induct_down)
  case (1 y)
  then
  show ?case
    using arg_into_eclose by auto
next
  case (2 y z)
  from \<open>y \<in> A \<or> (\<exists>B\<in>A. y \<in> eclose(B))\<close>
  consider (inA) "y \<in> A" | (exB) "(\<exists>B\<in>A. y \<in> eclose(B))"
    by auto
  then show ?case
  proof (cases)
    case inA
    then
    show ?thesis using 2 arg_into_eclose by auto
  next
    case exB
    then obtain B where "y \<in> eclose(B)" "B\<in>A"
      by auto
    then
    show ?thesis using 2 ecloseD[of y B z] by auto
  qed
qed

lemma eclose_singE : "x \<in> eclose({a}) \<Longrightarrow> x = a \<or> x \<in> eclose(a)"
  by(blast dest: ecloseE)

lemma in_eclose_sing :
  assumes "x \<in> eclose({a})" "a \<in> eclose(z)"
  shows "x \<in> eclose({z})"
proof -
  from \<open>x\<in>eclose({a})\<close>
  consider (eq) "x=a" | (lt) "x\<in>eclose(a)"
    using eclose_singE by auto
  then
  show ?thesis
    using eclose_sing mem_eclose_trans assms
    by (cases, auto)
qed

lemma in_dom_in_eclose :
  assumes "x \<in> domain(z)"
  shows "x \<in> eclose(z)"
proof -
  from assms
  obtain y where "\<langle>x,y\<rangle> \<in> z"
    unfolding domain_def by auto
  then
  show ?thesis
    unfolding Pair_def
    using ecloseD[of "{x,x}"] ecloseD[of "{{x,x},{x,y}}"] arg_into_eclose
    by auto
qed

text\<open>term\<open>ed\<close> is the well-founded relation on which \<^term>\<open>val\<close> is defined.\<close>
definition
  ed :: "[i,i] \<Rightarrow> o" where
  "ed(x,y) \<equiv> x \<in> domain(y)"

definition
  edrel :: "i \<Rightarrow> i" where
  "edrel(A) \<equiv> Rrel(ed,A)"


lemma edI[intro!]: "t\<in>domain(x) \<Longrightarrow> ed(t,x)"
  unfolding ed_def .

lemma edD[dest!]: "ed(t,x) \<Longrightarrow> t\<in>domain(x)"
  unfolding ed_def .


lemma rank_ed:
  assumes "ed(y,x)"
  shows "succ(rank(y)) \<le> rank(x)"
proof
  from assms
  obtain p where "\<langle>y,p\<rangle>\<in>x" by auto
  moreover
  obtain s where "y\<in>s" "s\<in>\<langle>y,p\<rangle>" unfolding Pair_def by auto
  ultimately
  have "rank(y) < rank(s)" "rank(s) < rank(\<langle>y,p\<rangle>)" "rank(\<langle>y,p\<rangle>) < rank(x)"
    using rank_lt by blast+
  then
  show "rank(y) < rank(x)"
    using lt_trans by blast
qed

lemma edrel_dest [dest]: "x \<in> edrel(A) \<Longrightarrow> \<exists> a\<in> A. \<exists> b \<in> A. x =\<langle>a,b\<rangle>"
  by(auto simp add:ed_def edrel_def Rrel_def)

lemma edrelD : "x \<in> edrel(A) \<Longrightarrow> \<exists> a\<in> A. \<exists> b \<in> A. x =\<langle>a,b\<rangle> \<and> a \<in> domain(b)"
  by(auto simp add:ed_def edrel_def Rrel_def)

lemma edrelI [intro!]: "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> \<langle>x,y\<rangle>\<in>edrel(A)"
  by (simp add:ed_def edrel_def Rrel_def)

lemma edrel_trans: "Transset(A) \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> \<langle>x,y\<rangle>\<in>edrel(A)"
  by (rule edrelI, auto simp add:Transset_def domain_def Pair_def)

lemma domain_trans: "Transset(A) \<Longrightarrow> y\<in>A \<Longrightarrow> x \<in> domain(y) \<Longrightarrow> x\<in>A"
  by (auto simp add: Transset_def domain_def Pair_def)

lemma relation_edrel : "relation(edrel(A))"
  by(auto simp add: relation_def)

lemma field_edrel : "field(edrel(A))\<subseteq>A"
  by blast

lemma edrel_sub_memrel: "edrel(A) \<subseteq> trancl(Memrel(eclose(A)))"
proof
  fix z
  assume
    "z\<in>edrel(A)"
  then obtain x y where
    Eq1:   "x\<in>A" "y\<in>A" "z=\<langle>x,y\<rangle>" "x\<in>domain(y)"
    using edrelD
    by blast
  then obtain u v where
    Eq2:   "x\<in>u" "u\<in>v" "v\<in>y"
    unfolding domain_def Pair_def by auto
  with Eq1 have
    Eq3:   "x\<in>eclose(A)" "y\<in>eclose(A)" "u\<in>eclose(A)" "v\<in>eclose(A)"
    by (auto, rule_tac [3-4] ecloseD, rule_tac [3] ecloseD, simp_all add:arg_into_eclose)
  let
    ?r="trancl(Memrel(eclose(A)))"
  from Eq2 and Eq3 have
    "\<langle>x,u\<rangle>\<in>?r" "\<langle>u,v\<rangle>\<in>?r" "\<langle>v,y\<rangle>\<in>?r"
    by (auto simp add: r_into_trancl)
  then  have
    "\<langle>x,y\<rangle>\<in>?r"
    by (rule_tac trancl_trans, rule_tac [2] trancl_trans, simp)
  with Eq1 show "z\<in>?r" by simp
qed

lemma wf_edrel : "wf(edrel(A))"
  using wf_subset [of "trancl(Memrel(eclose(A)))"] edrel_sub_memrel
    wf_trancl wf_Memrel
  by auto

lemma ed_induction:
  assumes "\<And>x. \<lbrakk>\<And>y.  ed(y,x) \<Longrightarrow> Q(y) \<rbrakk> \<Longrightarrow> Q(x)"
  shows "Q(a)"
proof(induct rule: wf_induct2[OF wf_edrel[of "eclose({a})"] ,of a "eclose({a})"])
  case 1
  then show ?case using arg_into_eclose by simp
next
  case 2
  then show ?case using field_edrel .
next
  case (3 x)
  then
  show ?case
    using assms[of x] edrelI domain_trans[OF Transset_eclose 3(1)] by blast
qed

lemma dom_under_edrel_eclose: "edrel(eclose({x})) -`` {x} = domain(x)"
proof
  show "edrel(eclose({x})) -`` {x} \<subseteq> domain(x)"
    unfolding edrel_def Rrel_def ed_def
    by auto
next
  show "domain(x) \<subseteq> edrel(eclose({x})) -`` {x}"
    unfolding edrel_def Rrel_def
    using in_dom_in_eclose eclose_sing arg_into_eclose
    by blast
qed

lemma ed_eclose : "\<langle>y,z\<rangle> \<in> edrel(A) \<Longrightarrow> y \<in> eclose(z)"
  by(drule edrelD,auto simp add:domain_def in_dom_in_eclose)

lemma tr_edrel_eclose : "\<langle>y,z\<rangle> \<in> edrel(eclose({x}))^+ \<Longrightarrow> y \<in> eclose(z)"
  by(rule trancl_induct,(simp add: ed_eclose mem_eclose_trans)+)


lemma restrict_edrel_eq :
  assumes "z \<in> domain(x)"
  shows "edrel(eclose({x})) \<inter> eclose({z})\<times>eclose({z}) = edrel(eclose({z}))"
proof(intro equalityI subsetI)
  let ?ec="\<lambda> y . edrel(eclose({y}))"
  let ?ez="eclose({z})"
  let ?rr="?ec(x) \<inter> ?ez \<times> ?ez"
  fix y
  assume yr:"y \<in> ?rr"
  with yr obtain a b where 1:"\<langle>a,b\<rangle> \<in> ?rr" "a \<in> ?ez" "b \<in> ?ez" "\<langle>a,b\<rangle> \<in> ?ec(x)" "y=\<langle>a,b\<rangle>"
    by blast
  moreover
  from this
  have "a \<in> domain(b)" using edrelD by blast
  ultimately
  show "y \<in> edrel(eclose({z}))" by blast
next
  let ?ec="\<lambda> y . edrel(eclose({y}))"
  let ?ez="eclose({z})"
  let ?rr="?ec(x) \<inter> ?ez \<times> ?ez"
  fix y
  assume yr:"y \<in> edrel(?ez)"
  then obtain a b where "a \<in> ?ez" "b \<in> ?ez" "y=\<langle>a,b\<rangle>" "a \<in> domain(b)"
    using edrelD by blast
  moreover
  from this assms
  have "z \<in> eclose(x)" using in_dom_in_eclose by simp
  moreover
  from assms calculation
  have "a \<in> eclose({x})" "b \<in> eclose({x})" using in_eclose_sing by simp_all
  moreover
  from this \<open>a\<in>domain(b)\<close>
  have "\<langle>a,b\<rangle> \<in> edrel(eclose({x}))" by blast
  ultimately
  show "y \<in> ?rr" by simp
qed

lemma tr_edrel_subset :
  assumes "z \<in> domain(x)"
  shows   "tr_down(edrel(eclose({x})),z) \<subseteq> eclose({z})"
proof(intro subsetI)
  let ?r="\<lambda> x . edrel(eclose({x}))"
  fix y
  assume  "y \<in> tr_down(?r(x),z)"
  then
  have "\<langle>y,z\<rangle> \<in> ?r(x)^+" using tr_downD by simp
  with assms
  show "y \<in> eclose({z})" using tr_edrel_eclose eclose_sing by simp
qed


context M_ctm
begin

lemma upairM : "x \<in> M \<Longrightarrow> y \<in> M \<Longrightarrow> {x,y} \<in> M"
  by (simp flip: setclass_iff)

lemma singletonM : "a \<in> M \<Longrightarrow> {a} \<in> M"
  by (simp flip: setclass_iff)

lemma Rep_simp : "Replace(u,\<lambda> y z . z = f(y)) = { f(y) . y \<in> u}"
  by(auto)

end (* M_ctm *)

subsection\<open>Values and check-names\<close>
context forcing_data
begin

definition
  Hcheck :: "[i,i] \<Rightarrow> i" where
  "Hcheck(z,f)  \<equiv> { \<langle>f`y,one\<rangle> . y \<in> z}"

definition
  check :: "i \<Rightarrow> i" where
  "check(x) \<equiv> transrec(x , Hcheck)"

lemma checkD:
  "check(x) =  wfrec(Memrel(eclose({x})), x, Hcheck)"
  unfolding check_def transrec_def ..

definition
  rcheck :: "i \<Rightarrow> i" where
  "rcheck(x) \<equiv> Memrel(eclose({x}))^+"


lemma Hcheck_trancl:"Hcheck(y, restrict(f,Memrel(eclose({x}))-``{y}))
                   = Hcheck(y, restrict(f,(Memrel(eclose({x}))^+)-``{y}))"
  unfolding Hcheck_def
  using restrict_trans_eq by simp

lemma check_trancl: "check(x) = wfrec(rcheck(x), x, Hcheck)"
  using checkD wf_eq_trancl Hcheck_trancl unfolding rcheck_def by simp

(* relation of check is in M *)
lemma rcheck_in_M :
  "x \<in> M \<Longrightarrow> rcheck(x) \<in> M"
  unfolding rcheck_def by (simp flip: setclass_iff)


lemma  aux_def_check: "x \<in> y \<Longrightarrow>
  wfrec(Memrel(eclose({y})), x, Hcheck) =
  wfrec(Memrel(eclose({x})), x, Hcheck)"
  by (rule wfrec_eclose_eq,auto simp add: arg_into_eclose eclose_sing)

lemma def_check : "check(y) = { \<langle>check(w),one\<rangle> . w \<in> y}"
proof -
  let
    ?r="\<lambda>y. Memrel(eclose({y}))"
  have wfr:   "\<forall>w . wf(?r(w))" 
    using wf_Memrel ..
  then 
  have "check(y)= Hcheck( y, \<lambda>x\<in>?r(y) -`` {y}. wfrec(?r(y), x, Hcheck))"
    using wfrec[of "?r(y)" y "Hcheck"] checkD by simp
  also 
  have " ... = Hcheck( y, \<lambda>x\<in>y. wfrec(?r(y), x, Hcheck))"
    using under_Memrel_eclose arg_into_eclose by simp
  also 
  have " ... = Hcheck( y, \<lambda>x\<in>y. check(x))"
    using aux_def_check checkD by simp
  finally show ?thesis using Hcheck_def by simp
qed


lemma def_checkS :
  fixes n
  assumes "n \<in> nat"
  shows "check(succ(n)) = check(n) \<union> {\<langle>check(n),one\<rangle>}"
proof -
  have "check(succ(n)) = {\<langle>check(i),one\<rangle> . i \<in> succ(n)} "
    using def_check by blast
  also have "... = {\<langle>check(i),one\<rangle> . i \<in> n} \<union> {\<langle>check(n),one\<rangle>}"
    by blast
  also have "... = check(n) \<union> {\<langle>check(n),one\<rangle>}"
    using def_check[of n,symmetric] by simp
  finally show ?thesis .
qed

lemma field_Memrel2 :
  assumes "x \<in> M"
  shows "field(Memrel(eclose({x}))) \<subseteq> M"
proof -
  have "field(Memrel(eclose({x}))) \<subseteq> eclose({x})" "eclose({x}) \<subseteq> M"
    using Ordinal.Memrel_type field_rel_subset assms eclose_least[OF trans_M] by auto
  then
  show ?thesis using subset_trans by simp
qed

definition
  Hv :: "i\<Rightarrow>i\<Rightarrow>i\<Rightarrow>i" where
  "Hv(G,x,f) \<equiv> { f`y .. y\<in> domain(x), \<exists>p\<in>P. \<langle>y,p\<rangle> \<in> x \<and> p \<in> G }"

text\<open>The funcion \<^term>\<open>val\<close> interprets a name in \<^term>\<open>M\<close>
according to a (generic) filter \<^term>\<open>G\<close>. Note the definition
in terms of the well-founded recursor.\<close>

definition
  val :: "i\<Rightarrow>i\<Rightarrow>i" where
  "val(G,\<tau>) \<equiv> wfrec(edrel(eclose({\<tau>})), \<tau> ,Hv(G))"

lemma aux_def_val:
  assumes "z \<in> domain(x)"
  shows "wfrec(edrel(eclose({x})),z,Hv(G)) = wfrec(edrel(eclose({z})),z,Hv(G))"
proof -
  let ?r="\<lambda>x . edrel(eclose({x}))"
  have "z\<in>eclose({z})" using arg_in_eclose_sing .
  moreover
  have "relation(?r(x))" using relation_edrel .
  moreover
  have "wf(?r(x))" using wf_edrel .
  moreover from assms
  have "tr_down(?r(x),z) \<subseteq> eclose({z})" using tr_edrel_subset by simp
  ultimately
  have "wfrec(?r(x),z,Hv(G)) = wfrec[eclose({z})](?r(x),z,Hv(G))"
    using wfrec_restr by simp
  also from \<open>z\<in>domain(x)\<close>
  have "... = wfrec(?r(z),z,Hv(G))"
    using restrict_edrel_eq wfrec_restr_eq by simp
  finally show ?thesis .
qed

text\<open>The next lemma provides the usual recursive expresion for the definition of term\<open>val\<close>.\<close>

lemma def_val:  "val(G,x) = {val(G,t) .. t\<in>domain(x) , \<exists>p\<in>P .  \<langle>t,p\<rangle>\<in>x \<and> p \<in> G }"
proof -
  let
    ?r="\<lambda>\<tau> . edrel(eclose({\<tau>}))"
  let
    ?f="\<lambda>z\<in>?r(x)-``{x}. wfrec(?r(x),z,Hv(G))"
  have "\<forall>\<tau>. wf(?r(\<tau>))" using wf_edrel by simp
  with wfrec [of _ x]
  have "val(G,x) = Hv(G,x,?f)" using val_def by simp
  also
  have " ... = Hv(G,x,\<lambda>z\<in>domain(x). wfrec(?r(x),z,Hv(G)))"
    using dom_under_edrel_eclose by simp
  also
  have " ... = Hv(G,x,\<lambda>z\<in>domain(x). val(G,z))"
    using aux_def_val val_def by simp
  finally
  show ?thesis using Hv_def SepReplace_def by simp
qed

lemma val_mono : "x\<subseteq>y \<Longrightarrow> val(G,x) \<subseteq> val(G,y)"
  by (subst (1 2) def_val, force)

text\<open>Check-names are the canonical names for elements of the
ground model. Here we show that this is the case.\<close>

lemma valcheck : "one \<in> G \<Longrightarrow>  one \<in> P \<Longrightarrow> val(G,check(y))  = y"
proof (induct rule:eps_induct)
  case (1 y)
  then show ?case
  proof -    
    have "check(y) = { \<langle>check(w), one\<rangle> . w \<in> y}"  (is "_ = ?C") 
      using def_check .
    then
    have "val(G,check(y)) = val(G, {\<langle>check(w), one\<rangle> . w \<in> y})"
      by simp
    also
    have " ...  = {val(G,t) .. t\<in>domain(?C) , \<exists>p\<in>P .  \<langle>t, p\<rangle>\<in>?C \<and> p \<in> G }"
      using def_val by blast
    also
    have " ... =  {val(G,t) .. t\<in>domain(?C) , \<exists>w\<in>y. t=check(w) }"
      using 1 by simp
    also
    have " ... = {val(G,check(w)) . w\<in>y }"
      by force
    finally
    show "val(G,check(y)) = y"
      using 1 by simp
  qed
qed

lemma val_of_name :
  "val(G,{x\<in>A\<times>P. Q(x)}) = {val(G,t) .. t\<in>A , \<exists>p\<in>P .  Q(\<langle>t,p\<rangle>) \<and> p \<in> G }"
proof -
  let
    ?n="{x\<in>A\<times>P. Q(x)}" and
    ?r="\<lambda>\<tau> . edrel(eclose({\<tau>}))"
  let
    ?f="\<lambda>z\<in>?r(?n)-``{?n}. val(G,z)"
  have
    wfR : "wf(?r(\<tau>))" for \<tau>
    by (simp add: wf_edrel)
  have "domain(?n) \<subseteq> A" by auto
  { fix t
    assume H:"t \<in> domain({x \<in> A \<times> P . Q(x)})"
    then have "?f ` t = (if t \<in> ?r(?n)-``{?n} then val(G,t) else 0)"
      by simp
    moreover have "... = val(G,t)"
      using dom_under_edrel_eclose H if_P by auto
  }
  then
  have Eq1: "t \<in> domain({x \<in> A \<times> P . Q(x)}) \<Longrightarrow> val(G,t) = ?f` t"  for t
    by simp
  have "val(G,?n) = {val(G,t) .. t\<in>domain(?n), \<exists>p \<in> P . \<langle>t,p\<rangle> \<in> ?n \<and> p \<in> G}"
    by (subst def_val,simp)
  also
  have "... = {?f`t .. t\<in>domain(?n), \<exists>p\<in>P . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G}"
    unfolding Hv_def
    by (subst SepReplace_dom_implies,auto simp add:Eq1)
  also
  have  "... = { (if t\<in>?r(?n)-``{?n} then val(G,t) else 0) .. t\<in>domain(?n), \<exists>p\<in>P . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G}"
    by (simp)
  also
  have Eq2:  "... = { val(G,t) .. t\<in>domain(?n), \<exists>p\<in>P . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G}"
  proof -
    have "domain(?n) \<subseteq> ?r(?n)-``{?n}"
      using dom_under_edrel_eclose by simp
    then
    have "\<forall>t\<in>domain(?n). (if t\<in>?r(?n)-``{?n} then val(G,t) else 0) = val(G,t)"
      by auto
    then
    show "{ (if t\<in>?r(?n)-``{?n} then val(G,t) else 0) .. t\<in>domain(?n), \<exists>p\<in>P . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G} =
          { val(G,t) .. t\<in>domain(?n), \<exists>p\<in>P . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G}"
      by auto
  qed
  also
  have " ... = { val(G,t) .. t\<in>A, \<exists>p\<in>P . \<langle>t,p\<rangle>\<in>?n \<and> p\<in>G}"
    by force
  finally
  show " val(G,?n)  = { val(G,t) .. t\<in>A, \<exists>p\<in>P . Q(\<langle>t,p\<rangle>) \<and> p\<in>G}"
    by auto
qed

lemma val_of_name_alt :
  "val(G,{x\<in>A\<times>P. Q(x)}) = {val(G,t) .. t\<in>A , \<exists>p\<in>P\<inter>G .  Q(\<langle>t,p\<rangle>) }"
  using val_of_name by force

lemma val_only_names: "val(F,\<tau>) = val(F,{x\<in>\<tau>. \<exists>t\<in>domain(\<tau>). \<exists>p\<in>P. x=\<langle>t,p\<rangle>})"
  (is "_ = val(F,?name)")
proof -
  have "val(F,?name) = {val(F, t).. t\<in>domain(?name), \<exists>p\<in>P. \<langle>t, p\<rangle> \<in> ?name \<and> p \<in> F}"
    using def_val by blast
  also
  have " ... = {val(F, t). t\<in>{y\<in>domain(?name). \<exists>p\<in>P. \<langle>y, p\<rangle> \<in> ?name \<and> p \<in> F}}"
    using Sep_and_Replace by simp
  also
  have " ... = {val(F, t). t\<in>{y\<in>domain(\<tau>). \<exists>p\<in>P. \<langle>y, p\<rangle> \<in> \<tau> \<and> p \<in> F}}"
    by blast
  also
  have " ... = {val(F, t).. t\<in>domain(\<tau>), \<exists>p\<in>P. \<langle>t, p\<rangle> \<in> \<tau> \<and> p \<in> F}"
    using Sep_and_Replace by simp
  also
  have " ... = val(F, \<tau>)"
    using def_val[symmetric] by blast
  finally
  show ?thesis ..
qed

lemma val_only_pairs: "val(F,\<tau>) = val(F,{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>})"
proof
  have "val(F,\<tau>) = val(F,{x\<in>\<tau>. \<exists>t\<in>domain(\<tau>). \<exists>p\<in>P. x=\<langle>t,p\<rangle>})"
    (is "_ = val(F,?name)")
    using val_only_names .
  also
  have "... \<subseteq> val(F,{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>})"
    using val_mono[of ?name "{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>}"] by auto
  finally
  show "val(F,\<tau>) \<subseteq> val(F,{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>})" by simp
next
  show "val(F,{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>}) \<subseteq> val(F,\<tau>)"
    using val_mono[of "{x\<in>\<tau>. \<exists>t p. x=\<langle>t,p\<rangle>}"] by auto
qed

lemma val_subset_domain_times_range: "val(F,\<tau>) \<subseteq> val(F,domain(\<tau>)\<times>range(\<tau>))"
  using val_only_pairs[THEN equalityD1]
    val_mono[of "{x \<in> \<tau> . \<exists>t p. x = \<langle>t, p\<rangle>}" "domain(\<tau>)\<times>range(\<tau>)"] by blast

lemma val_subset_domain_times_P: "val(F,\<tau>) \<subseteq> val(F,domain(\<tau>)\<times>P)"
  using val_only_names[of F \<tau>] val_mono[of "{x\<in>\<tau>. \<exists>t\<in>domain(\<tau>). \<exists>p\<in>P. x=\<langle>t,p\<rangle>}" "domain(\<tau>)\<times>P" F]
  by auto

definition
  GenExt :: "i\<Rightarrow>i"     ("M[_]")
  where "GenExt(G)\<equiv> {val(G,\<tau>). \<tau> \<in> M}"


lemma val_of_elem: "\<langle>\<theta>,p\<rangle> \<in> \<pi> \<Longrightarrow> p\<in>G \<Longrightarrow> p\<in>P \<Longrightarrow> val(G,\<theta>) \<in> val(G,\<pi>)"
proof -
  assume
    "\<langle>\<theta>,p\<rangle> \<in> \<pi>"
  then
  have "\<theta>\<in>domain(\<pi>)" by auto
  assume "p\<in>G" "p\<in>P"
  with \<open>\<theta>\<in>domain(\<pi>)\<close> \<open>\<langle>\<theta>,p\<rangle> \<in> \<pi>\<close>
  have "val(G,\<theta>) \<in> {val(G,t) .. t\<in>domain(\<pi>) , \<exists>p\<in>P .  \<langle>t, p\<rangle>\<in>\<pi> \<and> p \<in> G }"
    by auto
  then
  show ?thesis by (subst def_val)
qed

lemma elem_of_val: "x\<in>val(G,\<pi>) \<Longrightarrow> \<exists>\<theta>\<in>domain(\<pi>). val(G,\<theta>) = x"
  by (subst (asm) def_val,auto)

lemma elem_of_val_pair: "x\<in>val(G,\<pi>) \<Longrightarrow> \<exists>\<theta>. \<exists>p\<in>G.  \<langle>\<theta>,p\<rangle>\<in>\<pi> \<and> val(G,\<theta>) = x"
  by (subst (asm) def_val,auto)

lemma elem_of_val_pair':
  assumes "\<pi>\<in>M" "x\<in>val(G,\<pi>)"
  shows "\<exists>\<theta>\<in>M. \<exists>p\<in>G.  \<langle>\<theta>,p\<rangle>\<in>\<pi> \<and> val(G,\<theta>) = x"
proof -
  from assms
  obtain \<theta> p where "p\<in>G" "\<langle>\<theta>,p\<rangle>\<in>\<pi>" "val(G,\<theta>) = x"
    using elem_of_val_pair by blast
  moreover from this \<open>\<pi>\<in>M\<close>
  have "\<theta>\<in>M"
    using pair_in_M_iff[THEN iffD1, THEN conjunct1, simplified]
      transitivity by blast
  ultimately
  show ?thesis by blast
qed


lemma GenExtD:
  "x \<in> M[G] \<Longrightarrow> \<exists>\<tau>\<in>M. x = val(G,\<tau>)"
  by (simp add:GenExt_def)

lemma GenExtI:
  "x \<in> M \<Longrightarrow> val(G,x) \<in> M[G]"
  by (auto simp add: GenExt_def)

lemma Transset_MG : "Transset(M[G])"
proof -
  { fix vc y
    assume "vc \<in> M[G]" and "y \<in> vc"
    then obtain c where "c\<in>M" "val(G,c)\<in>M[G]" "y \<in> val(G,c)"
      using GenExtD by auto
    from \<open>y \<in> val(G,c)\<close>
    obtain \<theta> where "\<theta>\<in>domain(c)" "val(G,\<theta>) = y"
      using elem_of_val by blast
    with trans_M \<open>c\<in>M\<close>
    have "y \<in> M[G]"
      using domain_trans GenExtI by blast
  }
  then
  show ?thesis using Transset_def by auto
qed

lemmas transitivity_MG = Transset_intf[OF Transset_MG]

lemma check_n_M :
  fixes n
  assumes "n \<in> nat"
  shows "check(n) \<in> M"
  using \<open>n\<in>nat\<close>
proof (induct n)
  case 0
  then show ?case using zero_in_M by (subst def_check,simp)
next
  case (succ x)
  have "one \<in> M" using one_in_P P_sub_M subsetD by simp
  with \<open>check(x)\<in>M\<close>
  have "\<langle>check(x),one\<rangle> \<in> M"
    using tuples_in_M by simp
  then
  have "{\<langle>check(x),one\<rangle>} \<in> M"
    using singletonM by simp
  with \<open>check(x)\<in>M\<close>
  have "check(x) \<union> {\<langle>check(x),one\<rangle>} \<in> M"
    using Un_closed by simp
  then show ?case using \<open>x\<in>nat\<close> def_checkS by simp
qed


definition
  PHcheck :: "[i,i,i,i] \<Rightarrow> o" where
  "PHcheck(o,f,y,p) \<equiv> p\<in>M \<and> (\<exists>fy[##M]. fun_apply(##M,f,y,fy) \<and> pair(##M,fy,o,p))"

definition
  is_Hcheck :: "[i,i,i,i] \<Rightarrow> o" where
  "is_Hcheck(o,z,f,hc)  \<equiv> is_Replace(##M,z,PHcheck(o,f),hc)"

lemma one_in_M: "one \<in> M"
  by (insert one_in_P P_in_M, simp add: transitivity)

lemma def_PHcheck:
  assumes
    "z\<in>M" "f\<in>M"
  shows
    "Hcheck(z,f) = Replace(z,PHcheck(one,f))"
proof -
  from assms
  have "\<langle>f`x,one\<rangle> \<in> M" "f`x\<in>M" if "x\<in>z" for x
    using tuples_in_M one_in_M transitivity that apply_closed by simp_all
  then
  have "{y . x \<in> z, y = \<langle>f ` x, one\<rangle>} =  {y . x \<in> z, y = \<langle>f ` x, one\<rangle> \<and> y\<in>M \<and> f`x\<in>M}"
    by simp
  then
  show ?thesis
    using \<open>z\<in>M\<close> \<open>f\<in>M\<close> transitivity
    unfolding Hcheck_def PHcheck_def RepFun_def
    by auto
qed

(*
  "PHcheck(o,f,y,p) \<equiv> \<exists>fy[##M]. fun_apply(##M,f,y,fy) \<and> pair(##M,fy,o,p)"
*)
definition
  PHcheck_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "PHcheck_fm(o,f,y,p) \<equiv> Exists(And(fun_apply_fm(succ(f),succ(y),0)
                                 ,pair_fm(0,succ(o),succ(p))))"

lemma PHcheck_type [TC]:
  "\<lbrakk> x \<in> nat; y \<in> nat; z \<in> nat; u \<in> nat \<rbrakk> \<Longrightarrow> PHcheck_fm(x,y,z,u) \<in> formula"
  by (simp add:PHcheck_fm_def)

lemma sats_PHcheck_fm [simp]:
  "\<lbrakk> x \<in> nat; y \<in> nat; z \<in> nat; u \<in> nat ; env \<in> list(M)\<rbrakk>
    \<Longrightarrow> sats(M,PHcheck_fm(x,y,z,u),env) \<longleftrightarrow>
        PHcheck(nth(x,env),nth(y,env),nth(z,env),nth(u,env))"
  using zero_in_M Internalizations.nth_closed by (simp add: PHcheck_def PHcheck_fm_def)

(*
  "is_Hcheck(o,z,f,hc)  \<equiv> is_Replace(##M,z,PHcheck(o,f),hc)"
*)
definition
  is_Hcheck_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "is_Hcheck_fm(o,z,f,hc) \<equiv> Replace_fm(z,PHcheck_fm(succ(succ(o)),succ(succ(f)),0,1),hc)"

lemma is_Hcheck_type [TC]:
  "\<lbrakk> x \<in> nat; y \<in> nat; z \<in> nat; u \<in> nat \<rbrakk> \<Longrightarrow> is_Hcheck_fm(x,y,z,u) \<in> formula"
  by (simp add:is_Hcheck_fm_def)

lemma sats_is_Hcheck_fm [simp]:
  "\<lbrakk> x \<in> nat; y \<in> nat; z \<in> nat; u \<in> nat ; env \<in> list(M)\<rbrakk>
    \<Longrightarrow> sats(M,is_Hcheck_fm(x,y,z,u),env) \<longleftrightarrow>
        is_Hcheck(nth(x,env),nth(y,env),nth(z,env),nth(u,env))"
  using sats_Replace_fm unfolding is_Hcheck_def is_Hcheck_fm_def
  by simp


(* instance of replacement for hcheck *)
lemma wfrec_Hcheck :
  assumes
    "X\<in>M"
  shows
    "wfrec_replacement(##M,is_Hcheck(one),rcheck(X))"
proof -
  have "is_Hcheck(one,a,b,c) \<longleftrightarrow>
        sats(M,is_Hcheck_fm(8,2,1,0),[c,b,a,d,e,y,x,z,one,rcheck(x)])"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "y\<in>M" "x\<in>M" "z\<in>M"
    for a b c d e y x z
    using that one_in_M \<open>X\<in>M\<close> rcheck_in_M by simp
  then have 1:"sats(M,is_wfrec_fm(is_Hcheck_fm(8,2,1,0),4,1,0),
                    [y,x,z,one,rcheck(X)]) \<longleftrightarrow>
            is_wfrec(##M, is_Hcheck(one),rcheck(X), x, y)"
    if "x\<in>M" "y\<in>M" "z\<in>M" for x y z
    using  that sats_is_wfrec_fm \<open>X\<in>M\<close> rcheck_in_M one_in_M by simp
  let
    ?f="Exists(And(pair_fm(1,0,2),
               is_wfrec_fm(is_Hcheck_fm(8,2,1,0),4,1,0)))"
  have satsf:"sats(M, ?f, [x,z,one,rcheck(X)]) \<longleftrightarrow>
              (\<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hcheck(one),rcheck(X), x, y))"
    if "x\<in>M" "z\<in>M" for x z
    using that 1 \<open>X\<in>M\<close> rcheck_in_M one_in_M by (simp del:pair_abs)
  have artyf:"arity(?f) = 4"
    unfolding is_wfrec_fm_def is_Hcheck_fm_def Replace_fm_def PHcheck_fm_def
      pair_fm_def upair_fm_def is_recfun_fm_def fun_apply_fm_def big_union_fm_def
      pre_image_fm_def restriction_fm_def image_fm_def
    by (simp add:nat_simp_union)
  then
  have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,one,rcheck(X)]))"
    using replacement_ax 1 artyf \<open>X\<in>M\<close> rcheck_in_M one_in_M by simp
  then
  have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hcheck(one),rcheck(X), x, y))"
    using repl_sats[of M ?f "[one,rcheck(X)]"] satsf by (simp del:pair_abs)
  then
  show ?thesis unfolding wfrec_replacement_def by simp
qed

lemma repl_PHcheck :
  assumes
    "f\<in>M"
  shows
    "strong_replacement(##M,PHcheck(one,f))"
proof -
  have "arity(PHcheck_fm(2,3,0,1)) = 4"
    unfolding PHcheck_fm_def fun_apply_fm_def big_union_fm_def pair_fm_def image_fm_def
      upair_fm_def
    by (simp add:nat_simp_union)
  with \<open>f\<in>M\<close>
  have "strong_replacement(##M,\<lambda>x y. sats(M,PHcheck_fm(2,3,0,1),[x,y,one,f]))"
    using replacement_ax one_in_M by simp
  with \<open>f\<in>M\<close>
  show ?thesis using one_in_M unfolding strong_replacement_def univalent_def by simp
qed

lemma univ_PHcheck : "\<lbrakk> z\<in>M ; f\<in>M \<rbrakk> \<Longrightarrow> univalent(##M,z,PHcheck(one,f))"
  unfolding univalent_def PHcheck_def by simp

lemma relation2_Hcheck :
  "relation2(##M,is_Hcheck(one),Hcheck)"
proof -
  have 1:"\<lbrakk>x\<in>z; PHcheck(one,f,x,y) \<rbrakk> \<Longrightarrow> (##M)(y)"
    if "z\<in>M" "f\<in>M" for z f x y
    using that unfolding PHcheck_def by simp
  have "is_Replace(##M,z,PHcheck(one,f),hc) \<longleftrightarrow> hc = Replace(z,PHcheck(one,f))"
    if "z\<in>M" "f\<in>M" "hc\<in>M" for z f hc
    using that Replace_abs[OF _ _ univ_PHcheck 1] by simp
  with def_PHcheck
  show ?thesis
    unfolding relation2_def is_Hcheck_def Hcheck_def by simp
qed

lemma PHcheck_closed :
  "\<lbrakk>z\<in>M ; f\<in>M ; x\<in>z; PHcheck(one,f,x,y) \<rbrakk> \<Longrightarrow> (##M)(y)"
  unfolding PHcheck_def by simp

lemma Hcheck_closed :
  "\<forall>y\<in>M. \<forall>g\<in>M. function(g) \<longrightarrow> Hcheck(y,g)\<in>M"
proof -
  have "Replace(y,PHcheck(one,f))\<in>M" if "f\<in>M" "y\<in>M" for f y
    using that repl_PHcheck  PHcheck_closed[of y f] univ_PHcheck
      strong_replacement_closed
    by (simp flip: setclass_iff)
  then show ?thesis using def_PHcheck by auto
qed

lemma wf_rcheck : "x\<in>M \<Longrightarrow> wf(rcheck(x))"
  unfolding rcheck_def using wf_trancl[OF wf_Memrel] .

lemma trans_rcheck : "x\<in>M \<Longrightarrow> trans(rcheck(x))"
  unfolding rcheck_def using trans_trancl .

lemma relation_rcheck : "x\<in>M \<Longrightarrow> relation(rcheck(x))"
  unfolding rcheck_def using relation_trancl .

lemma check_in_M : "x\<in>M \<Longrightarrow> check(x) \<in> M"
  unfolding transrec_def
  using wfrec_Hcheck[of x] check_trancl wf_rcheck trans_rcheck relation_rcheck rcheck_in_M
    Hcheck_closed relation2_Hcheck trans_wfrec_closed[of "rcheck(x)" x "is_Hcheck(one)" Hcheck]
  by (simp flip: setclass_iff)

end (* forcing_data *)

(* check if this should go to Relative! *)
definition
  is_singleton :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_singleton(A,x,z) \<equiv> \<exists>c[A]. empty(A,c) \<and> is_cons(A,x,c,z)"

lemma (in M_trivial) singleton_abs[simp] : "\<lbrakk> M(x) ; M(s) \<rbrakk> \<Longrightarrow> is_singleton(M,x,s) \<longleftrightarrow> s = {x}"
  unfolding is_singleton_def using nonempty by simp

definition
  singleton_fm :: "[i,i] \<Rightarrow> i" where
  "singleton_fm(i,j) \<equiv> Exists(And(empty_fm(0), cons_fm(succ(i),0,succ(j))))"

lemma singleton_type[TC] : "\<lbrakk> x \<in> nat; y \<in> nat \<rbrakk> \<Longrightarrow> singleton_fm(x,y) \<in> formula"
  unfolding singleton_fm_def by simp

lemma is_singleton_iff_sats:
  "\<lbrakk> nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j\<in>nat ; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_singleton(##A,x,y) \<longleftrightarrow> sats(A, singleton_fm(i,j), env)"
  unfolding is_singleton_def singleton_fm_def by simp

context forcing_data begin

(* Internalization and absoluteness of rcheck *)
definition
  is_rcheck :: "[i,i] \<Rightarrow> o" where
  "is_rcheck(x,z) \<equiv> \<exists>r\<in>M. tran_closure(##M,r,z) \<and> (\<exists>ec\<in>M. membership(##M,ec,r) \<and>
                           (\<exists>s\<in>M. is_singleton(##M,x,s) \<and>  is_eclose(##M,s,ec)))"

lemma rcheck_abs :
  "\<lbrakk> x\<in>M ; r\<in>M \<rbrakk> \<Longrightarrow> is_rcheck(x,r) \<longleftrightarrow> r = rcheck(x)"
  unfolding rcheck_def is_rcheck_def
  using singletonM trancl_closed Memrel_closed eclose_closed by simp

schematic_goal rcheck_fm_auto:
  assumes
    "i \<in> nat" "j \<in> nat" "env \<in> list(M)"
  shows
    "is_rcheck(nth(i,env),nth(j,env)) \<longleftrightarrow> sats(M,?rch(i,j),env)"
  unfolding is_rcheck_def
  by (insert assms ; (rule sep_rules is_singleton_iff_sats is_eclose_iff_sats
        trans_closure_fm_iff_sats | simp)+)

synthesize "rcheck_fm" from_schematic rcheck_fm_auto

definition
  is_check :: "[i,i] \<Rightarrow> o" where
  "is_check(x,z) \<equiv> \<exists>rch\<in>M. is_rcheck(x,rch) \<and> is_wfrec(##M,is_Hcheck(one),rch,x,z)"

lemma check_abs :
  assumes
    "x\<in>M" "z\<in>M"
  shows
    "is_check(x,z) \<longleftrightarrow> z = check(x)"
proof -
  have
    "is_check(x,z) \<longleftrightarrow> is_wfrec(##M,is_Hcheck(one),rcheck(x),x,z)"
    unfolding is_check_def using assms rcheck_abs rcheck_in_M
    unfolding check_trancl is_check_def by simp
  then show ?thesis
    unfolding check_trancl
    using assms wfrec_Hcheck[of x] wf_rcheck trans_rcheck relation_rcheck rcheck_in_M
      Hcheck_closed relation2_Hcheck trans_wfrec_abs[of "rcheck(x)" x z "is_Hcheck(one)" Hcheck]
    by (simp flip: setclass_iff)
qed

(* \<exists>rch\<in>M. is_rcheck(x,rch) \<and> is_wfrec(##M,is_Hcheck(one),rch,x,z) *)
definition
  check_fm :: "[i,i,i] \<Rightarrow> i" where
  "check_fm(x,o,z) \<equiv> Exists(And(rcheck_fm(1#+x,0),
                      is_wfrec_fm(is_Hcheck_fm(6#+o,2,1,0),0,1#+x,1#+z)))"

lemma check_fm_type[TC] :
  "\<lbrakk>x\<in>nat;o\<in>nat;z\<in>nat\<rbrakk> \<Longrightarrow> check_fm(x,o,z)\<in>formula"
  unfolding check_fm_def by simp

lemma sats_check_fm :
  assumes
    "nth(o,env) = one" "x\<in>nat" "z\<in>nat" "o\<in>nat" "env\<in>list(M)" "x < length(env)" "z < length(env)"
  shows
    "sats(M, check_fm(x,o,z), env) \<longleftrightarrow> is_check(nth(x,env),nth(z,env))"
proof -
  have sats_is_Hcheck_fm:
    "\<And>a0 a1 a2 a3 a4. \<lbrakk> a0\<in>M; a1\<in>M; a2\<in>M; a3\<in>M; a4\<in>M \<rbrakk> \<Longrightarrow>
         is_Hcheck(one,a2, a1, a0) \<longleftrightarrow>
         sats(M, is_Hcheck_fm(6#+o,2,1,0), [a0,a1,a2,a3,a4,r]@env)" if "r\<in>M" for r
    using that one_in_M assms  by simp
  then
  have "sats(M, is_wfrec_fm(is_Hcheck_fm(6#+o,2,1,0),0,1#+x,1#+z),Cons(r,env))
        \<longleftrightarrow> is_wfrec(##M,is_Hcheck(one),r,nth(x,env),nth(z,env))" if "r\<in>M" for r
    using that assms one_in_M sats_is_wfrec_fm by simp
  then
  show ?thesis unfolding is_check_def check_fm_def
    using assms rcheck_in_M one_in_M rcheck_fm_iff_sats[symmetric] by simp
qed


lemma check_replacement:
  "{check(x). x\<in>P} \<in> M"
proof -
  have "arity(check_fm(0,2,1)) = 3"
    unfolding check_fm_def rcheck_fm_def trans_closure_fm_def is_eclose_fm_def mem_eclose_fm_def
      is_Hcheck_fm_def Replace_fm_def PHcheck_fm_def finite_ordinal_fm_def is_iterates_fm_def
      is_wfrec_fm_def is_recfun_fm_def restriction_fm_def pre_image_fm_def eclose_n_fm_def
      is_nat_case_fm_def quasinat_fm_def Memrel_fm_def singleton_fm_def fm_defs iterates_MH_fm_def
    by (simp add:nat_simp_union)
  moreover
  have "check(x)\<in>M" if "x\<in>P" for x
    using that Transset_intf[of M x P] trans_M check_in_M P_in_M by simp
  ultimately
  show ?thesis using sats_check_fm check_abs P_in_M check_in_M one_in_M
      Repl_in_M[of "check_fm(0,2,1)" "[one]" is_check check] by simp
qed

lemma pair_check : "\<lbrakk> p\<in>M ; y\<in>M \<rbrakk>  \<Longrightarrow> (\<exists>c\<in>M. is_check(p,c) \<and> pair(##M,c,p,y)) \<longleftrightarrow> y = \<langle>check(p),p\<rangle>"
  using check_abs check_in_M tuples_in_M by simp


lemma M_subset_MG :  "one \<in> G \<Longrightarrow> M \<subseteq> M[G]"
  using check_in_M one_in_P GenExtI
  by (intro subsetI, subst valcheck [of G,symmetric], auto)

text\<open>The name for the generic filter\<close>
definition
  G_dot :: "i" where
  "G_dot \<equiv> {\<langle>check(p),p\<rangle> . p\<in>P}"

lemma G_dot_in_M :
  "G_dot \<in> M"
proof -
  let ?is_pcheck = "\<lambda>x y. \<exists>ch\<in>M. is_check(x,ch) \<and> pair(##M,ch,x,y)"
  let ?pcheck_fm = "Exists(And(check_fm(1,3,0),pair_fm(0,1,2)))"
  have "sats(M,?pcheck_fm,[x,y,one]) \<longleftrightarrow> ?is_pcheck(x,y)" if "x\<in>M" "y\<in>M" for x y
    using sats_check_fm that one_in_M by simp
  moreover
  have "?is_pcheck(x,y) \<longleftrightarrow> y = \<langle>check(x),x\<rangle>" if "x\<in>M" "y\<in>M" for x y
    using that check_abs check_in_M by simp
  moreover
  have "?pcheck_fm\<in>formula" by simp
  moreover
  have "arity(?pcheck_fm)=3"
    unfolding check_fm_def rcheck_fm_def trans_closure_fm_def is_eclose_fm_def mem_eclose_fm_def
      is_Hcheck_fm_def Replace_fm_def PHcheck_fm_def finite_ordinal_fm_def is_iterates_fm_def
      is_wfrec_fm_def is_recfun_fm_def restriction_fm_def pre_image_fm_def eclose_n_fm_def
      is_nat_case_fm_def quasinat_fm_def Memrel_fm_def singleton_fm_def fm_defs iterates_MH_fm_def
    by (simp add:nat_simp_union)
  moreover
  from P_in_M check_in_M tuples_in_M P_sub_M
  have "\<langle>check(p),p\<rangle> \<in> M" if "p\<in>P" for p
    using that by auto
  ultimately
  show ?thesis
    unfolding G_dot_def
    using one_in_M P_in_M Repl_in_M[of ?pcheck_fm "[one]"]
    by simp
qed


lemma val_G_dot :
  assumes "G \<subseteq> P"
    "one \<in> G"
  shows "val(G,G_dot) = G"
proof (intro equalityI subsetI)
  fix x
  assume "x\<in>val(G,G_dot)"
  then obtain \<theta> p where "p\<in>G" "\<langle>\<theta>,p\<rangle> \<in> G_dot" "val(G,\<theta>) = x" "\<theta> = check(p)"
    unfolding G_dot_def using elem_of_val_pair G_dot_in_M
    by force
  with \<open>one\<in>G\<close> \<open>G\<subseteq>P\<close> show
    "x \<in> G"
    using valcheck P_sub_M by auto
next
  fix p
  assume "p\<in>G"
  have "\<langle>check(q),q\<rangle> \<in> G_dot" if "q\<in>P" for q
    unfolding G_dot_def using that by simp
  with \<open>p\<in>G\<close> \<open>G\<subseteq>P\<close>
  have "val(G,check(p)) \<in> val(G,G_dot)"
    using val_of_elem G_dot_in_M by blast
  with \<open>p\<in>G\<close> \<open>G\<subseteq>P\<close> \<open>one\<in>G\<close>
  show "p \<in> val(G,G_dot)"
    using P_sub_M valcheck by auto
qed


lemma G_in_Gen_Ext :
  assumes "G \<subseteq> P" and "one \<in> G"
  shows   "G \<in> M[G]"
  using assms val_G_dot GenExtI[of _ G] G_dot_in_M
  by force

(* Move this to M_trivial *)
lemma fst_snd_closed: "p\<in>M \<Longrightarrow> fst(p) \<in> M \<and> snd(p)\<in> M"
proof (cases "\<exists>a. \<exists>b. p = \<langle>a, b\<rangle>")
  case False
  then
  show "fst(p) \<in> M \<and> snd(p) \<in> M" unfolding fst_def snd_def using zero_in_M by auto
next
  case True
  then
  obtain a b where "p = \<langle>a, b\<rangle>" by blast
  with True
  have "fst(p) = a" "snd(p) = b" unfolding fst_def snd_def by simp_all
  moreover
  assume "p\<in>M"
  moreover from this
  have "a\<in>M"
    unfolding \<open>p = _\<close> Pair_def by (force intro:Transset_M[OF trans_M])
  moreover from  \<open>p\<in>M\<close>
  have "b\<in>M"
    using Transset_M[OF trans_M, of "{a,b}" p] Transset_M[OF trans_M, of "b" "{a,b}"]
    unfolding \<open>p = _\<close> Pair_def by (simp)
  ultimately
  show ?thesis by simp
qed

end (* forcing_data *)

locale G_generic = forcing_data +
  fixes G :: "i"
  assumes generic : "M_generic(G)"
begin

lemma zero_in_MG :
  "0 \<in> M[G]"
proof -
  have "0 = val(G,0)"
    using zero_in_M elem_of_val by auto
  also 
  have "... \<in> M[G]"
    using GenExtI zero_in_M by simp
  finally show ?thesis .
qed

lemma G_nonempty: "G\<noteq>0"
proof -
  have "P\<subseteq>P" ..
  with P_in_M P_dense \<open>P\<subseteq>P\<close>
  show "G \<noteq> 0"
    using generic unfolding M_generic_def by auto
qed

end (* context G_generic *)
end