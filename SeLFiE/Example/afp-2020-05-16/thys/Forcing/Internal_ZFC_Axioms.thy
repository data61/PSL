section\<open>The ZFC axioms, internalized\<close>
theory Internal_ZFC_Axioms
  imports 
  Forcing_Data

begin

schematic_goal ZF_union_auto:
    "Union_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> ?zfunion)"
  unfolding Union_ax_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_union_fm" from_schematic ZF_union_auto

schematic_goal ZF_power_auto:
    "power_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> ?zfpow)"
  unfolding power_ax_def powerset_def subset_def
  by ((rule sep_rules | simp)+)

synthesize "ZF_power_fm" from_schematic ZF_power_auto

schematic_goal ZF_pairing_auto:
    "upair_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> ?zfpair)"
  unfolding upair_ax_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_pairing_fm" from_schematic ZF_pairing_auto

schematic_goal ZF_foundation_auto:
    "foundation_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> ?zfpow)"
  unfolding foundation_ax_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_foundation_fm" from_schematic ZF_foundation_auto

schematic_goal ZF_extensionality_auto:
    "extensionality(##A) \<longleftrightarrow> (A, [] \<Turnstile> ?zfpow)"
  unfolding extensionality_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_extensionality_fm" from_schematic ZF_extensionality_auto

schematic_goal ZF_infinity_auto:
    "infinity_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?\<phi>(i,j,h)))"
  unfolding infinity_ax_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_infinity_fm" from_schematic ZF_infinity_auto

schematic_goal ZF_choice_auto:
    "choice_ax(##A) \<longleftrightarrow> (A, [] \<Turnstile> (?\<phi>(i,j,h)))"
  unfolding choice_ax_def 
  by ((rule sep_rules | simp)+)

synthesize "ZF_choice_fm" from_schematic ZF_choice_auto

syntax
  "_choice" :: "i"  ("AC")
translations
  "AC" \<rightharpoonup> "CONST ZF_choice_fm"

lemmas ZFC_fm_defs = ZF_extensionality_fm_def ZF_foundation_fm_def ZF_pairing_fm_def
              ZF_union_fm_def ZF_infinity_fm_def ZF_power_fm_def ZF_choice_fm_def

lemmas ZFC_fm_sats = ZF_extensionality_auto ZF_foundation_auto ZF_pairing_auto
              ZF_union_auto ZF_infinity_auto ZF_power_auto ZF_choice_auto

definition
  ZF_fin :: "i" where
  "ZF_fin \<equiv> { ZF_extensionality_fm, ZF_foundation_fm, ZF_pairing_fm,
              ZF_union_fm, ZF_infinity_fm, ZF_power_fm }"

definition
  ZFC_fin :: "i" where
  "ZFC_fin \<equiv> ZF_fin \<union> {ZF_choice_fm}"

lemma ZFC_fin_type : "ZFC_fin \<subseteq> formula"
  unfolding ZFC_fin_def ZF_fin_def ZFC_fm_defs by (auto)

subsection\<open>The Axiom of Separation, internalized\<close>
lemma iterates_Forall_type [TC]:
      "\<lbrakk> n \<in> nat; p \<in> formula \<rbrakk> \<Longrightarrow> Forall^n(p) \<in> formula"
  by (induct set:nat, auto)

lemma last_init_eq :
  assumes "l \<in> list(A)" "length(l) = succ(n)"
  shows "\<exists> a\<in>A. \<exists>l'\<in>list(A). l = l'@[a]"
proof-
  from \<open>l\<in>_\<close> \<open>length(_) = _\<close>
  have "rev(l) \<in> list(A)" "length(rev(l)) = succ(n)"
    by simp_all
  then
  obtain a l' where "a\<in>A" "l'\<in>list(A)" "rev(l) = Cons(a,l')"
    by (cases;simp)
  then
  have "l = rev(l') @ [a]" "rev(l') \<in> list(A)"
    using rev_rev_ident[OF \<open>l\<in>_\<close>] by auto
  with \<open>a\<in>_\<close>
  show ?thesis by blast
qed

lemma take_drop_eq :
  assumes "l\<in>list(M)"
  shows "\<And> n . n < succ(length(l)) \<Longrightarrow> l = take(n,l) @ drop(n,l)"
  using \<open>l\<in>list(M)\<close>
proof induct
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case
  proof -
    {
      fix i
      assume "i<succ(succ(length(l)))"
      with \<open>l\<in>list(M)\<close>
      consider (lt) "i = 0" | (eq) "\<exists>k\<in>nat. i = succ(k) \<and> k < succ(length(l))"
        using \<open>l\<in>list(M)\<close>  le_natI nat_imp_quasinat
        by (cases rule:nat_cases[of i];auto)
      then
      have "take(i,Cons(a,l)) @ drop(i,Cons(a,l)) = Cons(a,l)"
        using Cons
        by (cases;auto)
    }
    then show ?thesis using Cons by auto
  qed
qed

lemma list_split :
assumes "n \<le> succ(length(rest))" "rest \<in> list(M)"
shows  "\<exists>re\<in>list(M). \<exists>st\<in>list(M). rest = re @ st \<and> length(re) = pred(n)"
proof -
  from assms
  have "pred(n) \<le> length(rest)"
    using pred_mono[OF _ \<open>n\<le>_\<close>] pred_succ_eq by auto
  with \<open>rest\<in>_\<close>
  have "pred(n)\<in>nat" "rest = take(pred(n),rest) @ drop(pred(n),rest)" (is "_ = ?re @ ?st")
    using take_drop_eq[OF \<open>rest\<in>_\<close>] le_natI by auto
  then
  have "length(?re) = pred(n)" "?re\<in>list(M)" "?st\<in>list(M)"
    using length_take[rule_format,OF _ \<open>pred(n)\<in>_\<close>] \<open>pred(n) \<le> _\<close> \<open>rest\<in>_\<close>
    unfolding min_def
    by auto
  then
  show ?thesis
    using rev_bexI[of _ _ "\<lambda> re. \<exists>st\<in>list(M). rest = re @ st \<and> length(re) = pred(n)"]
      \<open>length(?re) = _\<close> \<open>rest = _\<close>
    by auto
qed

lemma sats_nForall:
  assumes
    "\<phi> \<in> formula"
  shows
    "n\<in>nat \<Longrightarrow> ms \<in> list(M) \<Longrightarrow>
       M, ms \<Turnstile> (Forall^n(\<phi>)) \<longleftrightarrow>
       (\<forall>rest \<in> list(M). length(rest) = n \<longrightarrow> M, rest @ ms \<Turnstile> \<phi>)"
proof (induct n arbitrary:ms set:nat)
  case 0
  with assms
  show ?case by simp
next
  case (succ n)
  have "(\<forall>rest\<in>list(M). length(rest) = succ(n) \<longrightarrow> P(rest,n)) \<longleftrightarrow>
        (\<forall>t\<in>M. \<forall>res\<in>list(M). length(res) = n \<longrightarrow> P(res @ [t],n))"
    if "n\<in>nat" for n P
    using that last_init_eq by force
  from this[of _ "\<lambda>rest _. (M, rest @ ms \<Turnstile> \<phi>)"] \<open>n\<in>nat\<close>
  have "(\<forall>rest\<in>list(M). length(rest) = succ(n) \<longrightarrow> M, rest @ ms \<Turnstile> \<phi>) \<longleftrightarrow>
        (\<forall>t\<in>M. \<forall>res\<in>list(M). length(res) = n \<longrightarrow>  M, (res @ [t]) @ ms \<Turnstile> \<phi>)"
    by simp
    with assms succ(1,3) succ(2)[of "Cons(_,ms)"]
  show ?case
    using arity_sats_iff[of \<phi> _ M "Cons(_, ms @ _)"] app_assoc
    by (simp)
qed

definition
  sep_body_fm :: "i \<Rightarrow> i" where
  "sep_body_fm(p) \<equiv> Forall(Exists(Forall(
                           Iff(Member(0,1),And(Member(0,2),
                                    incr_bv1^2(p))))))"

lemma sep_body_fm_type [TC]: "p \<in> formula \<Longrightarrow> sep_body_fm(p) \<in> formula"
  by (simp add: sep_body_fm_def)

lemma sats_sep_body_fm: 
  assumes
    "\<phi> \<in> formula" "ms\<in>list(M)" "rest\<in>list(M)"
  shows
    "M, rest @ ms \<Turnstile> sep_body_fm(\<phi>) \<longleftrightarrow> 
     separation(##M,\<lambda>x. M, [x] @ rest @ ms \<Turnstile> \<phi>)"
  using assms formula_add_params1[of _ 2 _ _ "[_,_]" ]
  unfolding sep_body_fm_def separation_def by simp

definition
  ZF_separation_fm :: "i \<Rightarrow> i" where
  "ZF_separation_fm(p) \<equiv> Forall^(pred(arity(p)))(sep_body_fm(p))"

lemma ZF_separation_fm_type [TC]: "p \<in> formula \<Longrightarrow> ZF_separation_fm(p) \<in> formula"
  by (simp add: ZF_separation_fm_def)

lemma sats_ZF_separation_fm_iff:
  assumes
    "\<phi>\<in>formula"
  shows
  "(M, [] \<Turnstile> (ZF_separation_fm(\<phi>)))
   \<longleftrightarrow>
   (\<forall>env\<in>list(M). arity(\<phi>) \<le> 1 #+ length(env) \<longrightarrow> 
      separation(##M,\<lambda>x. M, [x] @ env \<Turnstile> \<phi>))"
proof (intro iffI ballI impI)
  let ?n="Arith.pred(arity(\<phi>))"
  fix env
  assume "M, [] \<Turnstile> ZF_separation_fm(\<phi>)" 
  assume "arity(\<phi>) \<le> 1 #+ length(env)" "env\<in>list(M)"
  moreover from this
  have "arity(\<phi>) \<le> succ(length(env))" by simp
  then
  obtain some rest where "some\<in>list(M)" "rest\<in>list(M)" 
    "env = some @ rest" "length(some) = Arith.pred(arity(\<phi>))"
    using list_split[OF \<open>arity(\<phi>) \<le> succ(_)\<close> \<open>env\<in>_\<close>] by force
  moreover from \<open>\<phi>\<in>_\<close>
  have "arity(\<phi>) \<le> succ(Arith.pred(arity(\<phi>)))"
   using succpred_leI by simp
  moreover
  note assms
  moreover 
  assume "M, [] \<Turnstile> ZF_separation_fm(\<phi>)" 
  moreover from calculation
  have "M, some \<Turnstile> sep_body_fm(\<phi>)"
    using sats_nForall[of "sep_body_fm(\<phi>)" ?n]
    unfolding ZF_separation_fm_def by simp
  ultimately
  show "separation(##M, \<lambda>x. M, [x] @ env \<Turnstile> \<phi>)"
    unfolding ZF_separation_fm_def
    using sats_sep_body_fm[of \<phi> "[]" M some]
      arity_sats_iff[of \<phi> rest M "[_] @ some"]
      separation_cong[of "##M" "\<lambda>x. M, Cons(x, some @ rest) \<Turnstile> \<phi>" _ ]
    by simp
next \<comment> \<open>almost equal to the previous implication\<close>
  let ?n="Arith.pred(arity(\<phi>))"
  assume asm:"\<forall>env\<in>list(M). arity(\<phi>) \<le> 1 #+ length(env) \<longrightarrow> 
    separation(##M, \<lambda>x. M, [x] @ env \<Turnstile> \<phi>)"
  {
    fix some
    assume "some\<in>list(M)" "length(some) = Arith.pred(arity(\<phi>))"
    moreover
    note \<open>\<phi>\<in>_\<close>
    moreover from calculation
    have "arity(\<phi>) \<le> 1 #+ length(some)" 
      using le_trans[OF succpred_leI] succpred_leI by simp
    moreover from calculation and asm
    have "separation(##M, \<lambda>x. M, [x] @ some \<Turnstile> \<phi>)" by blast
    ultimately
    have "M, some \<Turnstile> sep_body_fm(\<phi>)" 
    using sats_sep_body_fm[of \<phi> "[]" M some]
      arity_sats_iff[of \<phi> _ M "[_,_] @ some"]
      strong_replacement_cong[of "##M" "\<lambda>x y. M, Cons(x, Cons(y, some @ _)) \<Turnstile> \<phi>" _ ]
    by simp
  }
  with \<open>\<phi>\<in>_\<close>
  show "M, [] \<Turnstile> ZF_separation_fm(\<phi>)"
    using sats_nForall[of "sep_body_fm(\<phi>)" ?n]
    unfolding ZF_separation_fm_def
    by simp
qed

subsection\<open>The Axiom of Replacement, internalized\<close>
schematic_goal sats_univalent_fm_auto:
  assumes 
    (*    Q_iff_sats:"\<And>a b z env aa bb. nth(a,Cons(z,env)) = aa \<Longrightarrow> nth(b,Cons(z,env)) = bb \<Longrightarrow> z\<in>A 
          \<Longrightarrow> aa \<in> A \<Longrightarrow> bb \<in> A \<Longrightarrow> env\<in> list(A) \<Longrightarrow> 
                 Q(aa,bb) \<longleftrightarrow> (A, Cons(z,env) \<Turnstile> (Q_fm(a,b)))" \<comment> \<open>using only one formula\<close> *)
    Q_iff_sats:"\<And>x y z. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z\<in>A \<Longrightarrow> 
                 Q(x,z) \<longleftrightarrow> (A,Cons(z,Cons(y,Cons(x,env))) \<Turnstile> Q1_fm)"
       "\<And>x y z. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z\<in>A \<Longrightarrow> 
                 Q(x,y) \<longleftrightarrow> (A,Cons(z,Cons(y,Cons(x,env))) \<Turnstile> Q2_fm)"
    and 
    asms: "nth(i,env) = B" "i \<in> nat" "env \<in> list(A)"
  shows
    "univalent(##A,B,Q) \<longleftrightarrow> A,env \<Turnstile> ?ufm(i)"
  unfolding univalent_def 
  by (insert asms; (rule sep_rules Q_iff_sats | simp)+)
  
synthesize_notc "univalent_fm" from_schematic sats_univalent_fm_auto

lemma univalent_fm_type [TC]: "q1\<in> formula \<Longrightarrow> q2\<in>formula \<Longrightarrow> i\<in>nat \<Longrightarrow> 
  univalent_fm(q2,q1,i) \<in>formula"
  by (simp add:univalent_fm_def)

lemma sats_univalent_fm :
  assumes
    Q_iff_sats:"\<And>x y z. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z\<in>A \<Longrightarrow> 
                 Q(x,z) \<longleftrightarrow> (A,Cons(z,Cons(y,Cons(x,env))) \<Turnstile> Q1_fm)"
       "\<And>x y z. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z\<in>A \<Longrightarrow> 
                 Q(x,y) \<longleftrightarrow> (A,Cons(z,Cons(y,Cons(x,env))) \<Turnstile> Q2_fm)"
    and 
    asms: "nth(i,env) = B" "i \<in> nat" "env \<in> list(A)"
  shows
    "A,env \<Turnstile> univalent_fm(Q1_fm,Q2_fm,i) \<longleftrightarrow> univalent(##A,B,Q)"
  unfolding univalent_fm_def using asms sats_univalent_fm_auto[OF Q_iff_sats] by simp

definition
  swap_vars :: "i\<Rightarrow>i" where
  "swap_vars(\<phi>) \<equiv> 
      Exists(Exists(And(Equal(0,3),And(Equal(1,2),iterates(\<lambda>p. incr_bv(p)`2 , 2, \<phi>)))))" 

lemma swap_vars_type[TC] :
  "\<phi>\<in>formula \<Longrightarrow> swap_vars(\<phi>) \<in>formula" 
  unfolding swap_vars_def by simp

lemma sats_swap_vars :
  "[x,y] @ env \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow> 
    M, [x,y] @ env \<Turnstile> swap_vars(\<phi>)\<longleftrightarrow> M,[y,x] @ env \<Turnstile> \<phi>"
  unfolding swap_vars_def
  using sats_incr_bv_iff [of _ _ M _ "[y,x]"] by simp

definition
  univalent_Q1 :: "i \<Rightarrow> i" where
  "univalent_Q1(\<phi>) \<equiv> incr_bv1(swap_vars(\<phi>))"

definition
  univalent_Q2 :: "i \<Rightarrow> i" where
  "univalent_Q2(\<phi>) \<equiv> incr_bv(swap_vars(\<phi>))`0"

lemma univalent_Qs_type [TC]: 
  assumes "\<phi>\<in>formula"
  shows "univalent_Q1(\<phi>) \<in> formula" "univalent_Q2(\<phi>) \<in> formula"
  unfolding univalent_Q1_def univalent_Q2_def using assms by simp_all

lemma sats_univalent_fm_assm:
  assumes 
    "x \<in> A" "y \<in> A" "z\<in>A" "env\<in> list(A)" "\<phi> \<in> formula"
  shows 
    "(A, ([x,z] @ env) \<Turnstile> \<phi>) \<longleftrightarrow> (A, Cons(z,Cons(y,Cons(x,env))) \<Turnstile> (univalent_Q1(\<phi>)))"
    "(A, ([x,y] @ env) \<Turnstile> \<phi>) \<longleftrightarrow> (A, Cons(z,Cons(y,Cons(x,env))) \<Turnstile> (univalent_Q2(\<phi>)))"
  unfolding univalent_Q1_def univalent_Q2_def
  using 
    sats_incr_bv_iff[of _ _ A _ "[]"] \<comment> \<open>simplifies iterates of \<^term>\<open>\<lambda>x. incr_bv(x)`0\<close>\<close>
    sats_incr_bv1_iff[of _ "Cons(x,env)" A z y] 
    sats_swap_vars  assms 
   by simp_all

definition
  rep_body_fm :: "i \<Rightarrow> i" where
  "rep_body_fm(p) \<equiv> Forall(Implies(
        univalent_fm(univalent_Q1(incr_bv(p)`2),univalent_Q2(incr_bv(p)`2),0),
        Exists(Forall(
          Iff(Member(0,1),Exists(And(Member(0,3),incr_bv(incr_bv(p)`2)`2)))))))"

lemma rep_body_fm_type [TC]: "p \<in> formula \<Longrightarrow> rep_body_fm(p) \<in> formula"
  by (simp add: rep_body_fm_def)

lemmas ZF_replacement_simps = formula_add_params1[of \<phi> 2 _ M "[_,_]" ]
  sats_incr_bv_iff[of _ _ M _ "[]"] \<comment> \<open>simplifies iterates of \<^term>\<open>\<lambda>x. incr_bv(x)`0\<close>\<close>
  sats_incr_bv_iff[of _ _ M _ "[_,_]"]\<comment> \<open>simplifies \<^term>\<open>\<lambda>x. incr_bv(x)`2\<close>\<close>
  sats_incr_bv1_iff[of _ _ M] sats_swap_vars for \<phi> M

lemma sats_rep_body_fm:
  assumes
    "\<phi> \<in> formula" "ms\<in>list(M)" "rest\<in>list(M)"
  shows
    "M, rest @ ms \<Turnstile> rep_body_fm(\<phi>) \<longleftrightarrow> 
     strong_replacement(##M,\<lambda>x y. M, [x,y] @ rest @ ms \<Turnstile> \<phi>)"
  using assms ZF_replacement_simps 
  unfolding rep_body_fm_def strong_replacement_def univalent_def
  unfolding univalent_fm_def univalent_Q1_def univalent_Q2_def
  by simp

definition
  ZF_replacement_fm :: "i \<Rightarrow> i" where
  "ZF_replacement_fm(p) \<equiv> Forall^(pred(pred(arity(p))))(rep_body_fm(p))"

lemma ZF_replacement_fm_type [TC]: "p \<in> formula \<Longrightarrow> ZF_replacement_fm(p) \<in> formula"
  by (simp add: ZF_replacement_fm_def)

lemma sats_ZF_replacement_fm_iff:
  assumes
    "\<phi>\<in>formula"
  shows
  "(M, [] \<Turnstile> (ZF_replacement_fm(\<phi>)))
   \<longleftrightarrow>
   (\<forall>env\<in>list(M). arity(\<phi>) \<le> 2 #+ length(env) \<longrightarrow> 
      strong_replacement(##M,\<lambda>x y. M,[x,y] @ env \<Turnstile> \<phi>))"
proof (intro iffI ballI impI)
  let ?n="Arith.pred(Arith.pred(arity(\<phi>)))"
  fix env
  assume "M, [] \<Turnstile> ZF_replacement_fm(\<phi>)" "arity(\<phi>) \<le> 2 #+ length(env)" "env\<in>list(M)"
  moreover from this
  have "arity(\<phi>) \<le> succ(succ(length(env)))" by (simp)
  moreover from calculation 
  have "pred(arity(\<phi>)) \<le> succ(length(env))"
    using pred_mono[OF _ \<open>arity(\<phi>)\<le>succ(_)\<close>] pred_succ_eq by simp
  moreover from calculation
  obtain some rest where "some\<in>list(M)" "rest\<in>list(M)" 
    "env = some @ rest" "length(some) = Arith.pred(Arith.pred(arity(\<phi>)))" 
    using list_split[OF \<open>pred(_) \<le> _\<close> \<open>env\<in>_\<close>] by auto
  moreover
  note \<open>\<phi>\<in>_\<close>
  moreover from this
  have "arity(\<phi>) \<le> succ(succ(Arith.pred(Arith.pred(arity(\<phi>)))))"
    using le_trans[OF succpred_leI] succpred_leI by simp
  moreover from calculation
  have "M, some \<Turnstile> rep_body_fm(\<phi>)"
    using sats_nForall[of "rep_body_fm(\<phi>)" ?n]
    unfolding ZF_replacement_fm_def
    by simp
  ultimately
  show "strong_replacement(##M, \<lambda>x y. M, [x, y] @ env \<Turnstile> \<phi>)"
    using sats_rep_body_fm[of \<phi> "[]" M some]
      arity_sats_iff[of \<phi> rest M "[_,_] @ some"]
      strong_replacement_cong[of "##M" "\<lambda>x y. M, Cons(x, Cons(y, some @ rest)) \<Turnstile> \<phi>" _ ]
    by simp
next \<comment> \<open>almost equal to the previous implication\<close>
  let ?n="Arith.pred(Arith.pred(arity(\<phi>)))"
  assume asm:"\<forall>env\<in>list(M). arity(\<phi>) \<le> 2 #+ length(env) \<longrightarrow> 
    strong_replacement(##M, \<lambda>x y. M, [x, y] @ env \<Turnstile> \<phi>)"
  {
    fix some
    assume "some\<in>list(M)" "length(some) = Arith.pred(Arith.pred(arity(\<phi>)))"
    moreover
    note \<open>\<phi>\<in>_\<close>
    moreover from calculation
    have "arity(\<phi>) \<le> 2 #+ length(some)" 
      using le_trans[OF succpred_leI] succpred_leI by simp
    moreover from calculation and asm
    have "strong_replacement(##M, \<lambda>x y. M, [x, y] @ some \<Turnstile> \<phi>)" by blast
    ultimately
    have "M, some \<Turnstile> rep_body_fm(\<phi>)" 
    using sats_rep_body_fm[of \<phi> "[]" M some]
      arity_sats_iff[of \<phi> _ M "[_,_] @ some"]
      strong_replacement_cong[of "##M" "\<lambda>x y. M, Cons(x, Cons(y, some @ _)) \<Turnstile> \<phi>" _ ]
    by simp
  }
  with \<open>\<phi>\<in>_\<close>
  show "M, [] \<Turnstile> ZF_replacement_fm(\<phi>)"
    using sats_nForall[of "rep_body_fm(\<phi>)" ?n]
    unfolding ZF_replacement_fm_def
    by simp
qed

definition
  ZF_inf :: "i" where
  "ZF_inf \<equiv> {ZF_separation_fm(p) . p \<in> formula } \<union> {ZF_replacement_fm(p) . p \<in> formula }"
              
lemma Un_subset_formula: "A\<subseteq>formula \<and> B\<subseteq>formula \<Longrightarrow> A\<union>B \<subseteq> formula"
  by auto
  
lemma ZF_inf_subset_formula : "ZF_inf \<subseteq> formula"
  unfolding ZF_inf_def by auto
    
definition
  ZFC :: "i" where
  "ZFC \<equiv> ZF_inf \<union> ZFC_fin"

definition
  ZF :: "i" where
  "ZF \<equiv> ZF_inf \<union> ZF_fin"

definition 
  ZF_minus_P :: "i" where
  "ZF_minus_P \<equiv> ZF - { ZF_power_fm }"

lemma ZFC_subset_formula: "ZFC \<subseteq> formula"
  by (simp add:ZFC_def Un_subset_formula ZF_inf_subset_formula ZFC_fin_type)
  
txt\<open>Satisfaction of a set of sentences\<close>
definition
  satT :: "[i,i] \<Rightarrow> o"  ("_ \<Turnstile> _" [36,36] 60) where
  "A \<Turnstile> \<Phi>  \<equiv>  \<forall>\<phi>\<in>\<Phi>. (A,[] \<Turnstile> \<phi>)"

lemma satTI [intro!]: 
  assumes "\<And>\<phi>. \<phi>\<in>\<Phi> \<Longrightarrow> A,[] \<Turnstile> \<phi>"
  shows "A \<Turnstile> \<Phi>"
  using assms unfolding satT_def by simp

lemma satTD [dest] :"A \<Turnstile> \<Phi> \<Longrightarrow>  \<phi>\<in>\<Phi> \<Longrightarrow> A,[] \<Turnstile> \<phi>"
  unfolding satT_def by simp

lemma sats_ZFC_iff_sats_ZF_AC: 
  "(N \<Turnstile> ZFC) \<longleftrightarrow> (N \<Turnstile> ZF) \<and> (N, [] \<Turnstile> AC)"
    unfolding ZFC_def ZFC_fin_def ZF_def by auto

lemma M_ZF_iff_M_satT: "M_ZF(M) \<longleftrightarrow> (M \<Turnstile> ZF)"
proof
  assume "M \<Turnstile> ZF"
  then
  have fin: "upair_ax(##M)" "Union_ax(##M)" "power_ax(##M)"
    "extensionality(##M)" "foundation_ax(##M)" "infinity_ax(##M)"
    unfolding ZF_def ZF_fin_def ZFC_fm_defs satT_def
    using ZFC_fm_sats[of M] by simp_all
  {
    fix \<phi> env
    assume "\<phi> \<in> formula" "env\<in>list(M)" 
    moreover from \<open>M \<Turnstile> ZF\<close>
    have "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))" 
         "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_replacement_fm(p)))"
      unfolding ZF_def ZF_inf_def by auto
    moreover from calculation
    have "arity(\<phi>) \<le> succ(length(env)) \<Longrightarrow> separation(##M, \<lambda>x. (M, Cons(x, env) \<Turnstile> \<phi>))"
      "arity(\<phi>) \<le> succ(succ(length(env))) \<Longrightarrow> strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,Cons(x,Cons(y, env))))"
      using sats_ZF_separation_fm_iff sats_ZF_replacement_fm_iff by simp_all  
  }
  with fin
  show "M_ZF(M)"
    unfolding M_ZF_def by simp
next
  assume \<open>M_ZF(M)\<close>
  then
  have "M \<Turnstile> ZF_fin" 
    unfolding M_ZF_def ZF_fin_def ZFC_fm_defs satT_def
    using ZFC_fm_sats[of M] by blast
  moreover from \<open>M_ZF(M)\<close>
  have "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_separation_fm(p)))" 
       "\<forall>p\<in>formula. (M, [] \<Turnstile> (ZF_replacement_fm(p)))"
    unfolding M_ZF_def using sats_ZF_separation_fm_iff 
      sats_ZF_replacement_fm_iff by simp_all
  ultimately
  show "M \<Turnstile> ZF"
    unfolding ZF_def ZF_inf_def by blast
qed

end
