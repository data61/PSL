section "Soundness wrt. contextual equivalence"

subsection "Denotational semantics is a congruence"  

theory DenotCongruenceFSet
  imports ChangeEnv DenotSoundFSet DenotCompleteFSet
begin
  
lemma e_lam_cong[cong]: "E e  = E e' \<Longrightarrow> E (ELam x e) = E (ELam x e')"
  by (rule ext) simp

lemma e_app_cong[cong]: "\<lbrakk> E e1 = E e1'; E e2 = E e2' \<rbrakk> \<Longrightarrow> E (EApp e1 e2) = E (EApp e1' e2')"
  by (rule ext) simp 

lemma e_prim_cong[cong]: "\<lbrakk> E e1 = E e1'; E e2 = E e2' \<rbrakk> \<Longrightarrow> E(EPrim f e1 e2) = E(EPrim f e1' e2')"
  by (rule ext) simp 

lemma e_if_cong[cong]: "\<lbrakk> E e1 = E e1'; E e2 = E e2'; E e3 = E e3' \<rbrakk> 
    \<Longrightarrow> E (EIf e1 e2 e3) = E (EIf e1' e2' e3')"
  by (rule ext) simp 

datatype ctx = CHole | CLam name ctx | CAppL ctx exp | CAppR exp ctx
  | CPrimL "nat \<Rightarrow> nat \<Rightarrow> nat"  ctx exp | CPrimR "nat \<Rightarrow> nat \<Rightarrow> nat"  exp ctx
  | CIf1 ctx exp exp | CIf2 exp ctx exp | CIf3 exp exp ctx

fun plug :: "ctx \<Rightarrow> exp \<Rightarrow> exp" where
  "plug CHole e = e" |
  "plug (CLam x C) e = ELam x (plug C e)" |
  "plug (CAppL C e2) e = EApp (plug C e) e2" |
  "plug (CAppR e1 C) e = EApp e1 (plug C e)" |
  "plug (CPrimL f C e2) e = EPrim f (plug C e) e2" |
  "plug (CPrimR f e1 C) e = EPrim f e1 (plug C e)" |
  "plug (CIf1 C e2 e3) e = EIf (plug C e) e2 e3" |
  "plug (CIf2 e1 C e3) e = EIf e1 (plug C e) e3" |
  "plug (CIf3 e1 e2 C) e = EIf e1 e2 (plug C e)" 
    
lemma congruence: "E e = E e' \<Longrightarrow> E (plug C e) = E (plug C e')"
proof (induction C arbitrary: e e')
  case (CIf1 C e2 e3)
  have "E (EIf (plug C e) e2 e3) = E (EIf (plug C e') e2 e3)"
    apply (rule e_if_cong) using CIf1 apply blast+ done
  then show ?case by simp
next
  case (CIf2 e1 C e3)
  have "E (EIf e1 (plug C e) e3) = E (EIf e1 (plug C e') e3)"
    apply (rule e_if_cong) using CIf2 apply blast+ done
  then show ?case by simp
next
  case (CIf3 e1 e2 C)
  have "E (EIf e1 e2 (plug C e)) = E (EIf e1 e2 (plug C e'))"
    apply (rule e_if_cong) using CIf3 apply blast+ done
  then show ?case by simp
qed force+

subsection "Auxiliary lemmas" 
  
lemma diverge_denot_empty: assumes d: "diverge e" and fve: "FV e = {}" shows "E e [] = {}"
proof (rule classical)
  assume "E e [] \<noteq> {}"
  from this obtain A where wte: "A \<in> E e []" by auto 
  have ge: "good_env [] []" by blast 
  from wte ge obtain v where e_v: "[] \<turnstile> e \<Down> v" and gv: "v \<in> good A" 
    using denot_terminates by blast 
  from e_v fve obtain v' where e_vp: "e \<longrightarrow>* v'" and val_vp: "isval v'" 
    using sound_wrt_small_step by blast 
  from d e_vp have "\<exists> e'. v' \<longrightarrow> e'" by (simp add: diverge_def) 
  with val_vp have "False" using val_stuck by force 
  from this show ?thesis ..
qed

lemma goes_wrong_denot_empty:
  assumes gw: "goes_wrong e" and fv_e: "FV e = {}" shows "E e [] = {}"
proof (rule classical)
  assume "E e [] \<noteq> {}"
  from this obtain A where wte: "A \<in> E e []" by auto 
  have ge: "good_env [] []" by blast 
  from gw obtain e' where e_ep: "e \<longrightarrow>* e'" and s_ep: "stuck e'" and nv_ep: "\<not> isval e'"
    by auto 
  from wte e_ep have wtep: "A \<in> E e' []" using preservation by blast 
  from fv_e e_ep have fv_ep: "FV e' = {}" using reduction_pres_fv by auto 
  from wtep fv_ep have "is_val e' \<or> (\<exists> e''. e' \<longrightarrow> e'')" using progress[of A e' "[]" ] by simp
  from this s_ep nv_ep have "False" by simp 
  from this show ?thesis ..
qed
 
lemma denot_empty_diverge: assumes E_e: "E e [] = {}" and fv_e: "FV e = {}" 
  shows "diverge e \<or> goes_wrong e"
proof (rule classical)
  assume nd_gw: "\<not> (diverge e \<or> goes_wrong e)"
  from this have nd: "\<not> diverge e" by blast 
  from nd_gw have gw: "\<not> goes_wrong e" by blast 
  from nd obtain v::exp where e_v: "e \<longrightarrow>* v" and stuck: "\<not> (\<exists> e'. v \<longrightarrow> e')"
    by (simp only: diverge_def) blast 
  from gw e_v stuck have val_v: "isval v" by (simp only: goes_wrong_def stuck_def) blast 
  from fv_e e_v have fv_v: "FV v = {}" using reduction_pres_fv by auto 
  from val_v fv_v have val_v2: "is_val v" by simp 
  from e_v val_v2 obtain A where wte: "A \<in> E e []" and wtv: "A \<in> E v []" 
     using completeness[of e v] by blast 
  from this E_e have "False" by auto 
  from this show ?thesis ..
qed

lemma val_ty_observe:
  "\<lbrakk> A \<in> E v []; A \<in> E v' [];
    observe v ob; isval v'; isval v \<rbrakk> \<Longrightarrow> observe v' ob"
  apply (cases v) apply auto apply (cases v') apply auto 
  apply (cases v') apply auto 
  apply (cases ob) apply auto 
  done

subsection "Soundness wrt. contextual equivalence"

lemma soundness_wrt_ctx_equiv_aux[rule_format]:
  assumes e12: "E e1 = E e2"
  and fv_e1: "FV (plug C e1) = {}" and fv_e2: "FV (plug C e2) = {}"
  shows "run (plug C e1) ob \<longrightarrow> run (plug C e2) ob"
proof
  assume run_Ce1: "run (plug C e1) ob"
  from e12 have pe12: "E (plug C e1) = E (plug C e2)" by (rule congruence)   
  from run_Ce1 have "((\<exists> v. (plug C e1) \<longrightarrow>* v \<and> observe v ob) 
             \<or> ((diverge (plug C e1) \<or> goes_wrong (plug C e1)) \<and> ob = OBad))"
    by (simp only: run_def)
  from this show "run (plug C e2) ob"
  proof
    assume "\<exists>v. plug C e1 \<longrightarrow>* v \<and> observe v ob"
    from this obtain v where r_v: "plug C e1 \<longrightarrow>* v"
      and ob_v: "observe v ob" by blast
    from r_v fv_e1 have fv_v: "FV v = {}" by (rule reduction_pres_fv)
    from ob_v fv_v have val_v: "is_val v" by (cases v) auto 
    from r_v val_v obtain A  where ce1a: "A \<in> E (plug C e1) []"
      and wt_v_ap: "A \<in> E v []" using completeness[of "plug C e1" v] by auto 
    from ce1a pe12 have ce2a: "A \<in> E (plug C e2) []" by force 
    have ge: "good_env [] []" by blast
    from ce2a ge obtain v' where Ce2_vp: "[] \<turnstile> plug C e2 \<Down> v'" and vpa: "v' \<in> good A"
      using denot_terminates by blast 
    from Ce2_vp fv_e2 obtain v'' ob' where Ce2_vpp: "plug C e2 \<longrightarrow>* v''" and vvpp: "isval v''"
      and ovpp: "observe v'' ob'" and vp_ob: "bs_observe v' ob'"
      using sound_wrt_small_step[of "plug C e2" v'] by blast
    from ovpp have vpp_ob: "observe v'' ob"
    proof -
      from ce2a Ce2_vpp have vpp_app: "A \<in> E v'' []" using preservation by blast 
      from vpp_app wt_v_ap ob_v vvpp val_v
      show ?thesis apply simp apply (rule val_ty_observe) prefer 3 apply assumption apply auto done
    qed 
    from Ce2_vpp vpp_ob show ?thesis by (simp add: run_def) blast
  next
    assume d_e1: "(diverge (plug C e1) \<or> goes_wrong (plug C e1)) \<and> ob = OBad"
    from d_e1 fv_e1 have E_Ce1: "E (plug C e1) [] = {}"
      using diverge_denot_empty goes_wrong_denot_empty by blast 
    from E_Ce1 pe12 have E_Ce2: "E (plug C e2) [] = {}" by simp 
    from E_Ce2 fv_e2 have "diverge (plug C e2) \<or> goes_wrong (plug C e2)" 
      using denot_empty_diverge by blast 
    from this d_e1 show ?thesis  by (simp add: run_def) 
  qed
qed

definition ctx_equiv :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<simeq>" 51) where
"e \<simeq> e' \<equiv> \<forall> C ob. FV (plug C e) = {} \<and> FV (plug C e') = {} \<longrightarrow>
   run (plug C e) ob = run (plug C e') ob" 

theorem denot_sound_wrt_ctx_equiv: assumes e12: "E e1 = E e2" shows "e1 \<simeq> e2"
  using e12
  apply (simp only: ctx_equiv_def) apply clarify apply (rule iffI)
   apply (rule soundness_wrt_ctx_equiv_aux) apply assumption+
  apply (rule soundness_wrt_ctx_equiv_aux) apply auto
  done

end
