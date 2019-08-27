section \<open>Auxiliary Lemma Library\<close>  
theory IMP2_Aux_Lemmas
imports "HOL-Library.Multiset" "HOL-Library.Rewrite"
begin

text \<open>This library contains auxiliary lemmas, which are useful for proving 
  various VCs.
\<close>
 



subsection \<open>Termination Proofs\<close>

\<comment> \<open>Useful lemma to show well-foundedness of some process approaching a finite upper bound\<close>
lemma wf_bounded_supset: "finite S \<Longrightarrow> wf {(Q',Q). Q'\<supset>Q \<and> Q'\<subseteq> S}"
proof -
  assume [simp]: "finite S"
  hence [simp]: "!!x. finite (S-x)" by auto
  have "{(Q',Q). Q\<subset>Q' \<and> Q'\<subseteq> S} \<subseteq> inv_image ({(s'::nat,s). s'<s}) (\<lambda>Q. card (S-Q))"
  proof (intro subsetI, case_tac x, simp)
    fix a b
    assume A: "b\<subset>a \<and> a\<subseteq>S"
    hence "S-a \<subset> S-b" by blast
    thus "card (S-a) < card (S-b)" by (auto simp add: psubset_card_mono)
  qed
  moreover have "wf ({(s'::nat,s). s'<s})" by (rule wf_less)
  ultimately show ?thesis by (blast intro: wf_subset)
qed

text \<open>Well-founded relation to approximate a finite set from below\<close>
definition "finite_psupset S \<equiv> { (Q',Q). Q\<subset>Q' \<and> Q' \<subseteq> S }"
lemma finite_psupset_wf[simp, intro]: "finite S \<Longrightarrow> wf (finite_psupset S)"
  unfolding finite_psupset_def by (blast intro: wf_bounded_supset)




 
subsection \<open>Conversion between \<open>nat\<close> and \<open>int\<close>\<close>

lemmas nat_distribs = nat_add_distrib nat_diff_distrib Suc_diff_le nat_mult_distrib nat_div_distrib


subsection \<open>Interval Sets\<close>

lemma intvs_singleton[simp]: 
  "{i::int..<i + 1} = {i}" 
  "{i-1..<i::int} = {i-1}" 
  by auto

lemma intvs_incr_h:
  "l\<le>h \<Longrightarrow> {l::int..<h + 1} = insert h {l..<h}"
  by auto

lemma intvs_decr_h:
  "{l::int..<h - 1} = {l..<h} - {h-1}"
  by auto
  
lemma intvs_incr_l:
  "{l+1..<h::int} = {l..<h} - {l}"
  by auto

lemma intvs_decr_l:
  "l\<le>h \<Longrightarrow> {l-1..<h::int} = insert (l-1) {l..<h}"
  by auto
  
lemma intvs_ii_incdec:
  fixes l h :: int
  shows "l\<le>h+1 \<Longrightarrow> {l..h+1} = insert (h+1) {l..h}"  
    and "l-1\<le>h \<Longrightarrow> {l-1..h} = insert (l-1) {l..h}"  
    and "{l+1..h} = {l..h} - {l}"
    and "{l..h-1} = {l..h} - {h}"
  by auto
  
lemmas intvs_ie_incdec = intvs_incr_h intvs_incr_l intvs_decr_h intvs_decr_l
(* TODO: Add lemmas for ei, ee *)
lemmas intvs_incdec = intvs_ie_incdec intvs_ii_incdec

lemma intvs_lower_incr: "l<h \<Longrightarrow> {l::int..<h} = insert l ({l+1..<h})" by auto
lemma intvs_upper_decr: "l<h \<Longrightarrow> {l::int..<h} = insert (h-1) ({l..<h-1})" by auto

subsubsection \<open>Induction on Intervals\<close>

function intv_fwd_induct_scheme :: "int \<Rightarrow> int \<Rightarrow> unit" where
  "intv_fwd_induct_scheme l h = (if l<h then intv_fwd_induct_scheme (l+1) h else ())"
  by pat_completeness auto
termination apply (relation "measure (\<lambda>(l,h). nat (h-l))") by auto 
lemmas intv_induct = intv_fwd_induct_scheme.induct[case_names incr]

function intv_bwd_induct_scheme :: "int \<Rightarrow> int \<Rightarrow> unit" where
  "intv_bwd_induct_scheme l h = (if l<h then intv_bwd_induct_scheme l (h-1) else ())"
  by pat_completeness auto
termination apply (relation "measure (\<lambda>(l,h). nat (h-l))") by auto 
lemmas intv_bwd_induct = intv_bwd_induct_scheme.induct[case_names decr]
  


subsection \<open>Multiset Lemmas\<close>

lemma image_mset_subst_outside: "x\<notin>#s \<Longrightarrow> image_mset (f(x:=y)) s = image_mset f s"
  by (induction s) auto
  
lemma image_mset_set_subst_inside:
  assumes "finite S"
  assumes "i\<in>S"
  shows "image_mset (f(i:=x)) (mset_set S) = image_mset f (mset_set S) + {#x#} - {#f i#} "
  using assms  
  by (induction rule: finite_induct) (auto simp: image_mset_subst_outside)

lemma image_mset_eq_imp_set_eq: 
  assumes "image_mset f s = image_mset g s"  
  shows "f`(set_mset s) = g`set_mset s"
  using assms
  by (metis set_image_mset)
  
  
subsection \<open>Equal on Set\<close>
definition eq_on :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool" ("_ = _ on _" [50,50,50] 50)
  where "s=t on X \<longleftrightarrow> (\<forall>x\<in>X. s x = t x)"
  
lemma eq_on_subst_same: 
  "x\<in>X \<Longrightarrow> s(x:=v) = t on X \<longleftrightarrow> t x = v \<and> s=t on (X-{x})"  
  "x\<in>X \<Longrightarrow> s = t(x:=v) on X \<longleftrightarrow> s x = v \<and> s=t on (X-{x})"  
  by (auto simp: eq_on_def)
  
lemma eq_on_subst_other[simp]: 
  "x\<notin>X \<Longrightarrow> s(x:=v) = t on X \<longleftrightarrow> s=t on X"
  "x\<notin>X \<Longrightarrow> s = t(x:=v) on X \<longleftrightarrow> s=t on X"
  by (auto simp: eq_on_def)
  
lemma eq_on_refl[simp]: "s = s on X"  
  by (auto simp: eq_on_def)

lemma eq_on_sym[sym]: "s=t on X \<Longrightarrow> t=s on X"  
  by (auto simp: eq_on_def)

lemma eq_on_trans[trans]: "r=s on X \<Longrightarrow> s=t on X \<Longrightarrow> r=t on X"  
  by (auto simp: eq_on_def)

lemma eq_on_trans'[trans]: "r=s on X \<Longrightarrow> s=t on X' \<Longrightarrow> r=t on (X\<inter>X')"  
  by (auto simp: eq_on_def)
  
lemma eq_onD: "r = s on X \<Longrightarrow> x\<in>X \<Longrightarrow> r x = s x"  
  by (auto simp: eq_on_def)
  
      
lemma eq_on_xfer_pointwise: "\<lbrakk>a=a' on r'; r\<subseteq>r'\<rbrakk> \<Longrightarrow> (\<forall>i\<in>r. P (a i)) \<longleftrightarrow> (\<forall>i\<in>r. P (a' i))"  
  by (auto simp: eq_on_def subset_iff)
  
  
subsection \<open>Arrays\<close>  
  
  
subsubsection \<open>Sortedness\<close>
text \<open>Sortedness as monotonicity property\<close>
definition ran_sorted :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "ran_sorted a l h \<equiv> \<forall>i\<in>{l..<h}. \<forall>j\<in>{l..<h}. i\<le>j \<longrightarrow> a i \<le> a j"

text \<open>Alternative definition\<close>  
lemma ran_sorted_alt: "ran_sorted a l h = ( \<forall>i j. l\<le>i \<and> i<j \<and> j<h \<longrightarrow> a i \<le> a j)" 
  unfolding ran_sorted_def 
  by auto (metis dual_order.order_iff_strict)
  
lemma ran_sorted_empty[simp]: "ran_sorted a l l"  
  by (auto simp: ran_sorted_def)
  
lemma ran_sorted_singleton[simp]: "ran_sorted a l (l+1)"  
  by (auto simp: ran_sorted_def)

lemma eq_on_xfer_ran_sorted: "\<lbrakk> a=a' on r'; {l..<h} \<subseteq> r' \<rbrakk> \<Longrightarrow> ran_sorted a l h \<longleftrightarrow> ran_sorted a' l h"
  unfolding ran_sorted_alt eq_on_def by (auto simp: subset_iff)
  
lemma combine_sorted_pivot:
  assumes "l\<le>i" "i<h"
  assumes "ran_sorted a l i"
  assumes "ran_sorted a (i+1) h"
  assumes "\<forall>k\<in>{l..<i}. a k < a i"
  assumes "\<forall>k\<in>{i+1..<h}. a k \<ge> a i"
  shows "ran_sorted a l h"
  using assms unfolding ran_sorted_def Ball_def
  by clarsimp smt
  
  
  
subsubsection \<open>Multiset of Ranges in Arrays\<close>  
definition mset_ran :: "(int \<Rightarrow> 'a) \<Rightarrow> int set \<Rightarrow> 'a multiset"
  where "mset_ran a r \<equiv> image_mset a (mset_set r)"

lemma mset_ran_infinite[simp]: "infinite r \<Longrightarrow> mset_ran a r = {#}"  
  by (auto simp: mset_ran_def)
  
lemma mset_ran_by_sum: "mset_ran a r = (\<Sum>i\<in>r. {#a i#})"
proof (cases "finite r")
  case True thus ?thesis
    apply (induction r)
     apply (auto simp: mset_ran_def)
    done
qed simp    

lemma mset_ran_mem[simp, intro]: "finite r \<Longrightarrow> i\<in>r \<Longrightarrow> a i \<in># mset_ran a r"
  by (auto simp: mset_ran_def)

lemma mset_ran_empty[simp]: 
  "mset_ran a {} = {#}"  
  by (auto simp: mset_ran_def)
  
lemma mset_ran_empty_iff[simp]: 
  "finite r \<Longrightarrow> mset_ran a r = {#} \<longleftrightarrow> r={}"
  by (auto simp: mset_ran_def mset_set_empty_iff)

lemma mset_ran_single[simp]: "mset_ran a {i} = {#a i#}"  
  by (auto simp: mset_ran_def)
  
lemma mset_ran_eq_single_conv: "mset_ran a r = {#x#} \<longleftrightarrow> (\<exists>i. r={i} \<and> x= a i)"  
  apply (cases "finite r")
   apply (auto simp: mset_ran_def)
  using finite_set_mset_mset_set msed_map_invR by force
  
lemma mset_ran_insert: "\<lbrakk>finite r; i\<notin>r\<rbrakk> \<Longrightarrow> mset_ran a (insert i r) = add_mset (a i) (mset_ran a r)"  
  by (auto simp: mset_ran_def) 
  
  
lemma mset_ran_subst_outside: "i\<notin>r \<Longrightarrow> mset_ran (a(i:=x)) r = mset_ran a r"  
  unfolding mset_ran_def by (cases "finite r") (auto simp: image_mset_subst_outside)

lemma mset_ran_subst_inside: "finite r \<Longrightarrow> i\<in>r \<Longrightarrow> mset_ran (a(i:=x)) r = mset_ran a r + {#x#} - {#a i#}"  
  unfolding mset_ran_def by (auto simp: image_mset_set_subst_inside)
  
lemma mset_ran_combine1: "\<lbrakk>finite r\<^sub>1; finite r\<^sub>2; r\<^sub>1\<inter>r\<^sub>2={}\<rbrakk> \<Longrightarrow> mset_ran a r\<^sub>1 + mset_ran a r\<^sub>2 = mset_ran a (r\<^sub>1\<union>r\<^sub>2)"
  by (auto simp: mset_ran_by_sum sum.union_disjoint[symmetric])

lemma mset_ran_combine2: "\<lbrakk>finite r; i\<notin>r\<rbrakk> \<Longrightarrow> add_mset (a i) (mset_ran a r) = mset_ran a (insert i r)"
  using mset_ran_combine1[of "{i}" r a]
  by auto
  
lemmas mset_ran_combine = mset_ran_combine1 mset_ran_combine2
    
lemma mset_ran_cong:  
  "a = b on r \<Longrightarrow> mset_ran a r = mset_ran b r"
  apply (cases "finite r")
  by (auto simp: mset_ran_by_sum eq_on_def)
  
lemma mset_ran_shift:
  "inj_on f r \<Longrightarrow> mset_ran (a o f) r = mset_ran a (f`r)"
  apply (auto simp: mset_ran_def)
  by (metis image_mset_mset_set multiset.map_comp)
  
lemma mset_ran_combine_eqs:
  assumes "mset_ran a r\<^sub>1 = mset_ran b r\<^sub>1"
  assumes "mset_ran a r\<^sub>2 = mset_ran b r\<^sub>2"
  assumes "r\<^sub>1\<inter>r\<^sub>2 = {}"
  shows "mset_ran a (r\<^sub>1\<union>r\<^sub>2) = mset_ran b (r\<^sub>1\<union>r\<^sub>2)"
  apply (cases "finite r\<^sub>1"; cases "finite r\<^sub>2"; simp?)
  using assms(1,2)
  apply (simp add: mset_ran_combine1[OF _ _ assms(3), symmetric])
  done
  
lemma mset_ran_combine_eq_diff:
  assumes "mset_ran a (r-I) = mset_ran a' (r-I)" 
  assumes "a=a' on I"  
  shows "mset_ran a r = mset_ran a' r"  
proof -
  have [simp]: "(r - I) \<inter> (r \<inter> I) = {}" by auto
  have [simp]: "r - I \<union> r \<inter> I = r" by auto

  from assms(2) have "mset_ran a (r \<inter> I) = mset_ran a' (r \<inter> I)"
    by (auto simp: mset_ran_by_sum eq_on_def)
  from mset_ran_combine_eqs[OF assms(1) this] show ?thesis by auto
qed    

lemma mset_ran_eq_extend:
  assumes "mset_ran a r' = mset_ran a' r'"
  assumes "a = a' on r2"
  assumes "r-r' \<subseteq> r2"
  assumes "r'\<subseteq>r"
  shows "mset_ran a r = mset_ran a' r"
proof -
  have [simp]: "r' \<inter> (r - r') = {}" "r' \<union> r = r" using assms(4) by auto

  from assms(2,3) have "a=a' on r-r'" by (auto simp: eq_on_def)
  then have "mset_ran a (r-r') = mset_ran a' (r-r')"
    by (auto simp: mset_ran_by_sum eq_on_def)
  from mset_ran_combine_eqs[OF assms(1) this] show ?thesis by auto 
qed    
  
lemma mset_ran_xfer_pointwise:
  assumes "mset_ran a r = mset_ran a' r"
  assumes "finite r"
  shows "(\<forall>i\<in>r. P (a i)) \<longleftrightarrow> (\<forall>i\<in>r. P (a' i))"
  using assms unfolding mset_ran_def 
  by (auto;force dest: image_mset_eq_imp_set_eq)
  

  
  
subsection \<open>Swap\<close>
definition "swap a i j \<equiv> a(i:=a j, j:=a i)"

lemma mset_ran_swap: "\<lbrakk> i\<in>r; j\<in>r \<rbrakk> 
  \<Longrightarrow> mset_ran (swap a i j) r = mset_ran a r"
  by (cases "finite r") (auto simp: swap_def mset_ran_subst_inside)
  

subsection \<open>Range of an Array as List\<close>  
function (sequential) lran :: "(int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a list" where
  "lran a l h = (if l<h then a l # lran a (l+1) h else [])"
  by pat_completeness auto
termination 
  by (relation "measure (\<lambda>(_,l,h). nat (h-l))") auto
  
declare lran.simps[simp del]  
  
text \<open>
  \<open>lran a l h\<close> is the list \<open>[a\<^sub>l,a\<^sub>l\<^sub>+\<^sub>1,...,a\<^sub>h\<^sub>-\<^sub>1]\<close>
\<close>

subsubsection \<open>Auxiliary Lemmas\<close>

lemma lran_empty[simp]: 
  "lran a l l = []"
  "lran a l h = [] \<longleftrightarrow> h\<le>l"
  by (subst lran.simps; auto)+

lemma lran_bwd_simp: "lran a l h = (if l<h then lran a l (h-1)@[a (h-1)] else [])"
  apply (induction a l h rule: lran.induct)
  apply (rewrite in "\<hole> = _" lran.simps)
  apply (rewrite in "_ = \<hole>" lran.simps)
  by (auto simp: less_le)
    
lemma length_lran[simp]: "length (lran a l h) = nat (h-l)"
  apply (induction a l h rule: lran.induct)
  apply (subst lran.simps)
  apply (auto)
  done

lemma nth_lran[simp]: "int i < h-l \<Longrightarrow> lran a l h ! i = a (l + int i)"
  apply (induction a l h arbitrary: i rule: lran.induct)
  apply (subst lran.simps)
  apply (auto simp: nth_Cons nth_tl algebra_simps split: nat.splits)
  done

  
lemma lran_append1[simp]: "l\<le>h \<Longrightarrow> lran a l (h + 1) = lran a l h @ [a h]"
  by (rewrite in "\<hole> = _" lran_bwd_simp) auto

lemma lran_prepend1[simp]: "l\<le>h \<Longrightarrow> lran a (l-1) h = a(l-1) # lran a l h"
  by (rewrite in "\<hole> = _" lran.simps) auto
    
lemma lran_tail[simp]: "lran a (l+1) h = tl (lran a l h)"
  apply (rewrite in "_ = \<hole>" lran.simps)
  apply auto
  done
    
lemma lran_butlast[simp]: "lran a l (h-1) = butlast (lran a l h)"
  apply (rewrite in "_ = \<hole>" lran_bwd_simp)
  apply auto
  done
  
lemma hd_lran[simp]: "l<h \<Longrightarrow> hd (lran a l h) = a l"  
  apply (subst lran.simps) by simp
  
lemma last_lran[simp]: "l<h \<Longrightarrow> last (lran a l h) = a (h-1)"  
  apply (subst lran_bwd_simp) by simp
  

lemma lran_upd_outside[simp]:
  "i<l \<Longrightarrow> lran (a(i:=x)) l h = lran a l h"
  "h\<le>i \<Longrightarrow> lran (a(i:=x)) l h = lran a l h"
  subgoal
    apply (induction a l h rule: lran.induct)
    apply (rewrite in "\<hole> = _" lran.simps)
    apply (rewrite in "_ = \<hole>" lran.simps)
    by (auto)
  subgoal
    apply (induction a l h rule: lran.induct)
    apply (rewrite in "\<hole> = _" lran.simps)
    apply (rewrite in "_ = \<hole>" lran.simps)
    by (auto)
  done  

  
lemma lran_upd_inside: "i\<in>{l..<h} \<Longrightarrow> lran (a(i:=x)) l h = (lran a l h)[nat (i-l) := x]"
  apply (rule nth_equalityI)
   apply (simp_all add: nth_list_update, linarith)
  done


lemma tl_upd_at0[simp]: "tl (xs[0:=x]) = tl xs" by (cases xs) auto 

    
  
  
lemma lran_eq_iff: "lran a l h = lran a' l h \<longleftrightarrow> (\<forall>i. l\<le>i \<and> i<h \<longrightarrow> a i = a' i)"  
  apply (induction a l h rule: lran.induct)
  apply (rewrite in "\<hole> = _" lran.simps)
  apply (rewrite in "_ = \<hole>" lran.simps)
  apply auto
  by (metis antisym_conv not_less zless_imp_add1_zle)
  
lemma set_lran: "set (lran a l h) = a`{l..<h}"  
  apply (induction a l h rule: lran.induct)
  apply (rewrite in "\<hole> = _" lran.simps)
  apply auto
  by (metis atLeastLessThan_iff image_iff not_less not_less_iff_gr_or_eq zless_imp_add1_zle)
  
lemma mset_lran: "mset (lran a l h) = mset_ran a {l..<h}"
  apply (induction a l h rule: lran.induct)
  apply (rewrite in "\<hole> = _" lran.simps)
  by (auto simp: intvs_lower_incr mset_ran_insert)
  

end
