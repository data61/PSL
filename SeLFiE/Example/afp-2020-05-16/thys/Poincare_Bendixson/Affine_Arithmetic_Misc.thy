theory Affine_Arithmetic_Misc
  imports "HOL-ODE-Numerics.ODE_Numerics"
begin

section \<open>Branch-And-Bound Arithmetic\<close>

primrec prove_nonneg::"(nat * nat * string) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> slp \<Rightarrow> real aform list list \<Rightarrow> bool" where
  "prove_nonneg prnt 0 p slp X = (let _ = if prnt \<noteq> [] then print (STR ''# depth limit exceeded\<newline>'') else () in False)"
| "prove_nonneg prnt (Suc i) p slp XXS =
    (case XXS of [] \<Rightarrow> True | (X#XS) \<Rightarrow>
      let RS = approx_slp_outer p 1 slp X
      in if RS\<noteq>None \<and> Inf_aform' p (hd (the RS)) \<ge> 0
        then
          let _ = if prnt \<noteq> [] then print (STR ''# Success\<newline>'') else ();
             _ = if prnt \<noteq> [] then print (String.implode ((shows ''# '' o shows_box_of_aforms_hr X) ''\<newline>'')) else ();
             _ = fold (\<lambda>(a, b, c) _. print (String.implode (shows_segments_of_aform a b X c ''\<newline>''))) prnt ()
          in prove_nonneg prnt i p slp XS
        else let _ = if prnt \<noteq> [] then print (STR ''# Split\<newline>'') else () in case split_aforms_largest_uncond X of (a, b) \<Rightarrow>
          prove_nonneg prnt i p slp (a#b#XS))"

lemma prove_nonneg_simps[simp]:
  "prove_nonneg prnt 0 p slp X = False"
  "prove_nonneg prnt (Suc i) p slp XXS =
    (case XXS of [] \<Rightarrow> True | (X#XS) \<Rightarrow>
      let RS = approx_slp_outer p 1 slp X
      in if RS\<noteq>None \<and> Inf_aform' p (hd (the RS)) \<ge> 0
        then prove_nonneg prnt i p slp XS
        else case split_aforms_largest_uncond X of (a, b) \<Rightarrow> prove_nonneg prnt i p slp (a#b#XS))"
  by (auto simp: Let_def split: if_splits option.splits list.splits)

lemmas [simp del] = prove_nonneg.simps

lemma split_aforms_lemma:
  fixes xs::"real list"
  assumes "split_aforms XS i = (YS, ZS)"
  assumes "xs \<in> Joints XS"
  shows "xs \<in> Joints YS \<union> Joints ZS"
  using set_rev_mp[OF assms(2) Joints_map_split_aform[of XS i]] assms(1)
  by (auto simp: split_aforms_def o_def)

lemma prove_nonneg_empty[simp]: "prove_nonneg prnt (Suc i) p slp []"
  by simp

lemma prove_nonneg_fuel_mono:
  "prove_nonneg prnt (Suc i) p (slp_of_fas [fa]) YSS"
  if "prove_nonneg prnt i p (slp_of_fas [fa]) YSS"
  using that
proof (induction i arbitrary: YSS)
  case 0
  then show ?case by simp
next
  case (Suc i)
  from Suc.prems show ?case
    supply [simp del] = prove_nonneg_simps
    apply (subst prove_nonneg_simps)
    apply (auto simp: Let_def split: if_splits option.splits list.splits)
    subgoal apply (rule Suc.IH)
      apply (subst (asm) prove_nonneg_simps)
      by (auto simp: Let_def split: if_splits option.splits list.splits)
    subgoal apply (rule Suc.IH)
      apply (subst (asm) prove_nonneg.simps)
      by (auto simp: Let_def split: if_splits option.splits list.splits)
    subgoal apply (rule Suc.IH)
      apply (subst (asm) prove_nonneg.simps)
      by (auto simp: Let_def split: if_splits option.splits list.splits)
    done
qed

lemma prove_nonneg_mono:
  "prove_nonneg prnt i p (slp_of_fas [fa]) YSS" if "prove_nonneg prnt i p (slp_of_fas [fa]) (YS # YSS)"
  using that
proof (induction i arbitrary: YS YSS)
  case 0
  then show ?case by auto
next
  case (Suc i)
  from Suc.prems show ?case
    supply [simp del] = prove_nonneg_simps
    apply (subst (asm) prove_nonneg_simps)
    apply (auto simp: Let_def split: if_splits option.splits list.splits)
    subgoal by (rule prove_nonneg_fuel_mono)
    subgoal for x y apply (rule prove_nonneg_fuel_mono)
      apply (rule Suc.IH[of y])
      by (rule Suc.IH[of x])
    subgoal for x y apply (rule prove_nonneg_fuel_mono)
      apply (rule Suc.IH[of y])
      by (rule Suc.IH[of x])
    done
qed

lemma prove_nonneg:
  assumes "prove_nonneg prnt i p (slp_of_fas [fa]) XSS"
  shows "\<forall>XS \<in> set XSS. \<forall>xs \<in> Joints XS. interpret_floatarith fa xs \<ge> 0"
  using assms
proof (induction i arbitrary: XSS)
  case 0
  then show ?case
    by (auto )
next
  case (Suc i)
  show ?case
  proof (cases XSS)
    case Nil then show ?thesis by auto
  next
    case (Cons YS YSS)
    show ?thesis
      unfolding Cons
      apply auto
      subgoal for xs using Suc.prems
        apply (auto simp: Cons Let_def split: if_splits option.splits)
        subgoal for ys
          apply (drule approx_slp_outer_plain)
             apply (rule refl)
            apply force
           apply assumption
          apply simp
          apply (frule Joints_imp_length_eq[where XS=ys])
          apply (auto simp: Suc_length_conv)
          by (smt Inf_aform'_Affine_le)
        subgoal
          apply (simp add: split_aforms_largest_uncond_def split: prod.splits)
          apply (drule Suc.IH)
          apply (drule split_aforms_lemma, assumption)
          by auto
        subgoal
          apply (simp add: split_aforms_largest_uncond_def split: prod.splits)
          apply (drule Suc.IH)
          apply (drule split_aforms_lemma, assumption)
          by auto
        done
      subgoal for XS xs using Suc.prems
        apply (auto simp: Cons Let_def split: if_splits option.splits)
        subgoal for ys by (rule Suc.IH[rule_format], assumption, assumption, assumption)
        subgoal for ys
          apply (drule prove_nonneg_mono)
          apply (drule prove_nonneg_mono)
          by (rule Suc.IH[rule_format], assumption, assumption, assumption)
        subgoal for ys
          apply (drule prove_nonneg_mono)
          apply (drule prove_nonneg_mono)
          by (rule Suc.IH[rule_format], assumption, assumption, assumption)
        done
      done
  qed
qed

end