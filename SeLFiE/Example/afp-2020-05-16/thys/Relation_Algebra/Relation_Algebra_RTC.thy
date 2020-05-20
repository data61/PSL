(* Title:      Relation Algebra
   Author:     Alasdair Armstrong, Simon Foster, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Reflexive Transitive Closure\<close>

theory Relation_Algebra_RTC
  imports Relation_Algebra
begin

text \<open>We impose the Kleene algebra axioms for the star on relation algebras.
This gives us a reflexive transitive closure operation.\<close>

class relation_algebra_rtc = relation_algebra + star_op +
  assumes rtc_unfoldl: "1' +  x ; x\<^sup>\<star> \<le> x\<^sup>\<star>"
    and rtc_inductl: "z + x ; y \<le> y \<longrightarrow> x\<^sup>\<star> ; z \<le> y"
    and rtc_inductr: "z + y ; x \<le> y \<longrightarrow> z ; x\<^sup>\<star> \<le> y"

sublocale relation_algebra_rtc \<subseteq> kleene_algebra "(+)" "(;)" "1'" 0 "(\<le>)" "(<)" star
apply (unfold_locales)
  apply (rule rtc_unfoldl)
 apply (simp add: local.rtc_inductl)
apply (simp add: rtc_inductr)
done

context relation_algebra_rtc
begin

text \<open>First, we prove that the obvious interaction between the star and
converse is captured by the axioms.\<close>

lemma star_conv: "(x\<^sup>\<star>)\<^sup>\<smile> = (x\<^sup>\<smile>)\<^sup>\<star>"
proof (rule antisym)
  show "(x\<^sup>\<smile>)\<^sup>\<star> \<le> (x\<^sup>\<star>)\<^sup>\<smile>"
    by (metis local.conv_add local.conv_contrav local.conv_e local.conv_iso local.star_rtc1 local.star_rtc_least)
  show "(x\<^sup>\<star>)\<^sup>\<smile> \<le> (x\<^sup>\<smile>)\<^sup>\<star>"
    by (metis boffa_var conv_add conv_contrav conv_e conv_invol conv_iso star_denest star_ext star_iso star_plus_one sup.idem)
qed

text \<open>Next we provide an example to show how facts from Kleene algebra are
picked up in relation algebra.\<close>

lemma rel_church_rosser: "(x\<^sup>\<smile>)\<^sup>\<star> ; x\<^sup>\<star> \<le> x\<^sup>\<star> ; (x\<^sup>\<smile>)\<^sup>\<star> \<Longrightarrow> (x + x\<^sup>\<smile>)\<^sup>\<star> = x\<^sup>\<star> ; (x\<^sup>\<smile>)\<^sup>\<star>"
by (fact church_rosser)

end (* relation_algebra_rtc *)

end
