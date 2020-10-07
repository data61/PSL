section \<open>Security\<close>

theory Constructive_Cryptography imports
  Wiring
begin

definition "advantage \<A> res1 res2 = \<bar>spmf (connect \<A> res1) True - spmf (connect \<A> res2) True\<bar>"

locale constructive_security_aux =
  fixes real_resource :: "security \<Rightarrow> ('a + 'e, 'b + 'f) resource"
    and ideal_resource :: "security \<Rightarrow> ('c + 'e, 'd + 'f) resource"
    and sim :: "security \<Rightarrow> ('a, 'b, 'c, 'd) converter"
    and \<I>_real :: "security \<Rightarrow> ('a, 'b) \<I>"
    and \<I>_ideal :: "security \<Rightarrow> ('c, 'd) \<I>"
    and \<I>_common :: "security \<Rightarrow> ('e, 'f) \<I>"
    and bound :: "security \<Rightarrow> enat"
    and lossless :: "bool"
  assumes WT_real [WT_intro]: "\<And>\<eta>. \<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res real_resource \<eta> \<surd>"
    and WT_ideal [WT_intro]: "\<And>\<eta>. \<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res ideal_resource \<eta> \<surd>"
    and WT_sim [WT_intro]: "\<And>\<eta>. \<I>_real \<eta>, \<I>_ideal \<eta> \<turnstile>\<^sub>C sim \<eta> \<surd>"
    and adv: "\<And>\<A> :: security \<Rightarrow> ('a + 'e, 'b + 'f) distinguisher. 
    \<lbrakk> \<And>\<eta>. \<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<A> \<eta> \<surd>; 
      \<And>\<eta>. interaction_bounded_by (\<lambda>_. True) (\<A> \<eta>) (bound \<eta>);
      \<And>\<eta>. lossless \<Longrightarrow> plossless_gpv (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<A> \<eta>) \<rbrakk>
    \<Longrightarrow> negligible (\<lambda>\<eta>. advantage (\<A> \<eta>) (sim \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal_resource \<eta>) (real_resource \<eta>))"


locale constructive_security =
  constructive_security_aux real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common bound lossless
  for real_resource :: "security \<Rightarrow> ('a + 'e, 'b + 'f) resource"
    and ideal_resource :: "security \<Rightarrow> ('c + 'e, 'd + 'f) resource"
    and sim :: "security \<Rightarrow> ('a, 'b, 'c, 'd) converter"
    and \<I>_real :: "security \<Rightarrow> ('a, 'b) \<I>"
    and \<I>_ideal :: "security \<Rightarrow> ('c, 'd) \<I>"
    and \<I>_common :: "security \<Rightarrow> ('e, 'f) \<I>"
    and bound :: "security \<Rightarrow> enat"
    and lossless :: "bool"
    and w :: "security \<Rightarrow> ('c, 'd, 'a, 'b) wiring"
  +
  assumes correct: "\<exists>cnv. \<forall>\<D> :: security \<Rightarrow> ('c + 'e, 'd + 'f) distinguisher.
    (\<forall>\<eta>. \<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<D> \<eta> \<surd>) 
  \<longrightarrow> (\<forall>\<eta>. interaction_bounded_by (\<lambda>_. True) (\<D> \<eta>) (bound \<eta>))
  \<longrightarrow> (\<forall>\<eta>. lossless \<longrightarrow> plossless_gpv (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<D> \<eta>))
  \<longrightarrow> (\<forall>\<eta>. wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w \<eta>)) \<and>
       negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (ideal_resource \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real_resource \<eta>))"

locale constructive_security2 =
  constructive_security_aux real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common bound lossless
  for real_resource :: "security \<Rightarrow> ('a + 'e, 'b + 'f) resource"
    and ideal_resource :: "security \<Rightarrow> ('c + 'e, 'd + 'f) resource"
    and sim :: "security \<Rightarrow> ('a, 'b, 'c, 'd) converter"
    and \<I>_real :: "security \<Rightarrow> ('a, 'b) \<I>"
    and \<I>_ideal :: "security \<Rightarrow> ('c, 'd) \<I>"
    and \<I>_common :: "security \<Rightarrow> ('e, 'f) \<I>"
    and bound :: "security \<Rightarrow> enat"
    and lossless :: "bool"
    and w :: "security \<Rightarrow> ('c, 'd, 'a, 'b) wiring"
  +
  assumes sim: "\<exists>cnv. \<forall>\<eta>. wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w \<eta>) \<and> wiring (\<I>_ideal \<eta>) (\<I>_ideal \<eta>) (cnv \<eta> \<odot> sim \<eta>) (id, id)"
begin

lemma constructive_security:
  "constructive_security real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common bound lossless w"
proof
  from sim obtain cnv
    where w: "\<And>\<eta>. wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w \<eta>)"
      and inverse: "\<And>\<eta>. wiring (\<I>_ideal \<eta>) (\<I>_ideal \<eta>) (cnv \<eta> \<odot> sim \<eta>) (id, id)"
    by blast
  show "\<exists>cnv. \<forall>\<D>. (\<forall>\<eta>. \<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<D> \<eta> \<surd>)
    \<longrightarrow> (\<forall>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (bound \<eta>))
    \<longrightarrow> (\<forall>\<eta>. lossless \<longrightarrow> plossless_gpv (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<D> \<eta>))
    \<longrightarrow> (\<forall>\<eta>. wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w \<eta>)) \<and>
        negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (ideal_resource \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real_resource \<eta>))"
  proof(intro strip exI conjI)
    fix \<D> :: "security \<Rightarrow> ('c + 'e, 'd + 'f) distinguisher"
    assume WT_D [rule_format, WT_intro]: "\<forall>\<eta>. \<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<D> \<eta> \<surd>"
      and bound [rule_format, interaction_bound]: "\<forall>\<eta>. interaction_bounded_by (\<lambda>_. True) (\<D> \<eta>) (bound \<eta>)"
      and lossless [rule_format]: "\<forall>\<eta>. lossless \<longrightarrow> plossless_gpv (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<D> \<eta>)"
    
    show "wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w \<eta>)" for \<eta> by fact

    let ?A = "\<lambda>\<eta>. outs_\<I> (\<I>_ideal \<eta>)"
    let ?cnv = "\<lambda>\<eta>. restrict_converter (?A \<eta>) (\<I>_real \<eta>) (cnv \<eta>)"
    let ?\<A> = "\<lambda>\<eta>. absorb (\<D> \<eta>) (?cnv \<eta> |\<^sub>= 1\<^sub>C)"

    have eq: "advantage (\<D> \<eta>) (ideal_resource \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real_resource \<eta>) =
    advantage (?\<A> \<eta>) (sim \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal_resource \<eta>) (real_resource \<eta>)" for \<eta>
    proof -
      from w[of \<eta>] have [WT_intro]: "\<I>_ideal \<eta>, \<I>_real \<eta> \<turnstile>\<^sub>C cnv \<eta> \<surd>" by cases
      have "\<I>_ideal \<eta>, \<I>_ideal \<eta> \<turnstile>\<^sub>C ?cnv \<eta> \<odot> sim \<eta> \<sim> cnv \<eta> \<odot> sim \<eta>"
        by(rule eq_\<I>_comp_cong eq_\<I>_restrict_converter WT_intro order_refl eq_\<I>_converter_reflI)+
      also from inverse[of \<eta>] have "\<I>_ideal \<eta>, \<I>_ideal \<eta> \<turnstile>\<^sub>C cnv \<eta> \<odot> sim \<eta> \<sim> 1\<^sub>C" by cases simp
      finally have inverse': "\<I>_ideal \<eta>, \<I>_ideal \<eta> \<turnstile>\<^sub>C ?cnv \<eta> \<odot> sim \<eta> \<sim> 1\<^sub>C" .
      hence "\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>, \<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>\<^sub>C ?cnv \<eta> \<odot> sim \<eta> |\<^sub>= 1\<^sub>C \<sim> 1\<^sub>C |\<^sub>= 1\<^sub>C"
        by(rule parallel_converter2_eq_\<I>_cong)(intro eq_\<I>_converter_reflI WT_intro)
      also have "\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>, \<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>\<^sub>C 1\<^sub>C |\<^sub>= 1\<^sub>C \<sim> 1\<^sub>C"
        by(rule parallel_converter2_id_id)
      also
      have eq1: "connect (\<D> \<eta>) (?cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> sim \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal_resource \<eta>) = 
        connect (\<D> \<eta>) (1\<^sub>C \<rhd> ideal_resource \<eta>)"
        unfolding attach_compose[symmetric] comp_converter_parallel2 comp_converter_id_right
        by(rule connect_eq_resource_cong WT_intro eq_\<I>_attach_on' calculation)+(fastforce intro: WT_intro)+

      have *: "\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>, \<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>\<^sub>C ?cnv \<eta> |\<^sub>= 1\<^sub>C \<sim> cnv \<eta> |\<^sub>= 1\<^sub>C"
        by(rule parallel_converter2_eq_\<I>_cong eq_\<I>_restrict_converter)+(auto intro: WT_intro eq_\<I>_converter_reflI)
      have eq2: "connect (\<D> \<eta>) (?cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real_resource \<eta>) = connect (\<D> \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real_resource \<eta>)"
        by(rule connect_eq_resource_cong WT_intro eq_\<I>_attach_on' *)+(auto intro: WT_intro)
      show ?thesis unfolding advantage_def by(simp add: distinguish_attach[symmetric] eq1 eq2)
    qed
    have "\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g ?\<A> \<eta> \<surd>" for \<eta>
    proof -
      from w have [WT_intro]: "\<I>_ideal \<eta>, \<I>_real \<eta> \<turnstile>\<^sub>C cnv \<eta> \<surd>" by cases
      show ?thesis by(rule WT_intro)+
    qed
    moreover
    have "interaction_any_bounded_by (absorb (\<D> \<eta>) (?cnv \<eta> |\<^sub>= 1\<^sub>C)) (bound \<eta>)" for \<eta>
    proof -
      from w[of \<eta>] obtain f g where [simp]: "w \<eta> = (f, g)"
        and [WT_intro]: "\<I>_ideal \<eta>, \<I>_real \<eta> \<turnstile>\<^sub>C cnv \<eta> \<surd>"
        and eq: "\<I>_ideal \<eta>, \<I>_real \<eta> \<turnstile>\<^sub>C cnv \<eta> \<sim> map_converter id id f g 1\<^sub>C" by cases
      from eq_\<I>_restrict_converter_cong[OF eq order_refl]
      have *: "restrict_converter (?A \<eta>) (\<I>_real \<eta>) (cnv \<eta>) =
      restrict_converter (?A \<eta>) (\<I>_real \<eta>) (map_converter f g id id 1\<^sub>C)"
        by(subst map_converter_id_move_right) simp
      show ?thesis unfolding * by interaction_bound_converter simp
    qed
    moreover have "plossless_gpv (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (?\<A> \<eta>)"
      if "lossless" for \<eta> 
    proof -
      from w[of \<eta>] obtain f g where [simp]: "w \<eta> = (f, g)"
        and cnv [WT_intro]: "\<I>_ideal \<eta>, \<I>_real \<eta> \<turnstile>\<^sub>C cnv \<eta> \<surd>"
        and eq: "\<I>_ideal \<eta>, \<I>_real \<eta> \<turnstile>\<^sub>C cnv \<eta> \<sim> map_converter id id f g 1\<^sub>C" by cases
      from eq_\<I>_converterD_WT1[OF eq cnv] have \<I>: "\<I>_ideal \<eta> \<le> map_\<I> f g (\<I>_real \<eta>)"
        by(rule WT_map_converter_idD)
      with WT_converter_id have [WT_intro]: "\<I>_ideal \<eta>, map_\<I> f g (\<I>_real \<eta>) \<turnstile>\<^sub>C 1\<^sub>C \<surd>" 
        by(rule WT_converter_mono) simp
      have id: "plossless_converter (\<I>_ideal \<eta>) (map_\<I> f g (\<I>_real \<eta>)) 1\<^sub>C"
        by(rule plossless_converter_mono)(rule plossless_id_converter order_refl \<I> WT_intro)+
      show ?thesis unfolding eq_\<I>_restrict_converter_cong[OF eq order_refl]
        by(rule plossless_gpv_absorb lossless[OF that] plossless_parallel_converter2 plossless_restrict_converter plossless_map_converter)+
          (fastforce intro: WT_intro id WT_converter_map_converter)+
    qed
    ultimately show "negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (ideal_resource \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real_resource \<eta>))"
      unfolding eq by(rule adv)
  qed
qed

sublocale constructive_security real_resource ideal_resource sim \<I>_real \<I>_ideal \<I>_common bound lossless w
  by(rule constructive_security)

end

subsection \<open>Composition theorems\<close>

theorem composability:
  fixes real
  assumes "constructive_security middle ideal sim_inner \<I>_middle \<I>_inner \<I>_common bound_inner lossless_inner w1"
  assumes "constructive_security real middle sim_outer \<I>_real \<I>_middle \<I>_common bound_outer lossless_outer w2"
  and bound [interaction_bound]: "\<And>\<eta>. interaction_any_bounded_converter (sim_outer \<eta>) (bound_sim \<eta>)"
  and bound_le: "\<And>\<eta>. bound_outer \<eta> * max (bound_sim \<eta>) 1 \<le> bound_inner \<eta>"
  and lossless_sim [plossless_intro]: "\<And>\<eta>. lossless_inner \<Longrightarrow> plossless_converter (\<I>_real \<eta>) (\<I>_middle \<eta>) (sim_outer \<eta>)"
  shows "constructive_security real ideal (\<lambda>\<eta>. sim_outer \<eta> \<odot> sim_inner \<eta>) \<I>_real \<I>_inner \<I>_common bound_outer (lossless_outer \<or> lossless_inner) (\<lambda>\<eta>. w1 \<eta> \<circ>\<^sub>w w2 \<eta>)"
proof
  interpret inner: constructive_security middle ideal sim_inner \<I>_middle \<I>_inner \<I>_common bound_inner lossless_inner w1 by fact
  interpret outer: constructive_security real middle sim_outer \<I>_real \<I>_middle \<I>_common bound_outer lossless_outer w2 by fact

  show "\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res real \<eta> \<surd>"
    and "\<I>_inner \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res ideal \<eta> \<surd>"
    and "\<I>_real \<eta>, \<I>_inner \<eta> \<turnstile>\<^sub>C sim_outer \<eta> \<odot> sim_inner \<eta> \<surd>" for \<eta> by(rule WT_intro)+

  { fix \<A> :: "security \<Rightarrow> ('g + 'b, 'h + 'd) distinguisher"
    assume WT [WT_intro]: "\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<A> \<eta> \<surd>" for \<eta>
    assume bound_outer [interaction_bound]: "interaction_bounded_by (\<lambda>_. True) (\<A> \<eta>) (bound_outer \<eta>)" for \<eta>
    assume lossless [plossless_intro]:
      "lossless_outer \<or> lossless_inner \<Longrightarrow> plossless_gpv (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<A> \<eta>)" for \<eta>

    let ?\<A> = "\<lambda>\<eta>. absorb (\<A> \<eta>) (sim_outer \<eta> |\<^sub>= 1\<^sub>C)"
    have "\<I>_middle \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g ?\<A> \<eta> \<surd>" for \<eta> by(rule WT_intro)+
    moreover have "interaction_any_bounded_by (?\<A> \<eta>) (bound_inner \<eta>)" for \<eta>
      by interaction_bound_converter(rule bound_le)
    moreover have "plossless_gpv (\<I>_middle \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (?\<A> \<eta>)" if lossless_inner for \<eta>
      by(rule plossless_intro WT_intro | simp add: that)+
    ultimately have "negligible (\<lambda>\<eta>. advantage (?\<A> \<eta>) (sim_inner \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal \<eta>) (middle \<eta>))"
      by(rule inner.adv)
    also have "negligible (\<lambda>\<eta>. advantage (\<A> \<eta>) (sim_outer \<eta> |\<^sub>= 1\<^sub>C \<rhd> middle \<eta>) (real \<eta>))"
      by(rule outer.adv[OF WT bound_outer lossless]) simp
    finally (negligible_plus)
    show "negligible (\<lambda>\<eta>. advantage (\<A> \<eta>) (sim_outer \<eta> \<odot> sim_inner \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal \<eta>) (real \<eta>))"
      apply(rule negligible_mono)
      apply(simp add: bigo_def)
      apply(rule exI[where x=1])
      apply simp
      apply(rule always_eventually)
      apply(clarsimp simp add: advantage_def)
      apply(rule order_trans)
       apply(rule abs_diff_triangle_ineq2)
      apply(rule add_right_mono)
      apply(clarsimp simp add: advantage_def distinguish_attach[symmetric] attach_compose[symmetric] comp_converter_parallel2 comp_converter_id_left)
      done
  next
    from inner.correct obtain cnv_inner
      where correct_inner: "\<And>\<D>. \<lbrakk> \<And>\<eta>. \<I>_inner \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<D> \<eta> \<surd>;
             \<And>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (bound_inner \<eta>);
             \<And>\<eta>. lossless_inner \<Longrightarrow> plossless_gpv (\<I>_inner \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<D> \<eta>) \<rbrakk>
           \<Longrightarrow> (\<forall>\<eta>. wiring (\<I>_inner \<eta>) (\<I>_middle \<eta>) (cnv_inner \<eta>) (w1 \<eta>)) \<and>
               negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (ideal \<eta>) (cnv_inner \<eta> |\<^sub>= 1\<^sub>C \<rhd> middle \<eta>))"
      by blast
    from outer.correct obtain cnv_outer
      where correct_outer: "\<And>\<D>. \<lbrakk> \<And>\<eta>. \<I>_middle \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<D> \<eta> \<surd>;
             \<And>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (bound_outer \<eta>);
             \<And>\<eta>. lossless_outer \<Longrightarrow> plossless_gpv (\<I>_middle \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<D> \<eta>) \<rbrakk>
           \<Longrightarrow> (\<forall>\<eta>. wiring (\<I>_middle \<eta>) (\<I>_real \<eta>) (cnv_outer \<eta>) (w2 \<eta>)) \<and>
               negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (middle \<eta>) (cnv_outer \<eta> |\<^sub>= 1\<^sub>C \<rhd> real \<eta>))"
      by blast
    show "\<exists>cnv. \<forall>\<D>. (\<forall>\<eta>. \<I>_inner \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<D> \<eta> \<surd>) \<longrightarrow>
               (\<forall>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (bound_outer \<eta>)) \<longrightarrow>
               (\<forall>\<eta>. lossless_outer \<or> lossless_inner \<longrightarrow> plossless_gpv (\<I>_inner \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<D> \<eta>)) \<longrightarrow>
               (\<forall>\<eta>. wiring (\<I>_inner \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w1 \<eta> \<circ>\<^sub>w w2 \<eta>)) \<and>
               negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (ideal \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real \<eta>))"
    proof(intro exI strip conjI)
      fix \<D> :: "security \<Rightarrow> ('e + 'b, 'f + 'd) distinguisher"
      assume WT_D [rule_format, WT_intro]: "\<forall>\<eta>. \<I>_inner \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<D> \<eta> \<surd>"
        and bound [rule_format, interaction_bound]: "\<forall>\<eta>. interaction_bounded_by (\<lambda>_. True) (\<D> \<eta>) (bound_outer \<eta>)"
        and lossless [rule_format]: "\<forall>\<eta>. lossless_outer \<or> lossless_inner \<longrightarrow> plossless_gpv (\<I>_inner \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<D> \<eta>)"

      let ?cnv = "\<lambda>\<eta>. cnv_inner \<eta> \<odot> cnv_outer \<eta>"

      have bound': "interaction_any_bounded_by (\<D> \<eta>) (bound_inner \<eta>)" for \<eta> using bound[of \<eta>] bound_le[of \<eta>]
        by(clarsimp elim!: interaction_bounded_by_mono order_trans[rotated] simp add: max_def)
          (metis (full_types) linorder_linear more_arith_simps(6) mult_left_mono zero_le)
      from correct_inner[OF WT_D bound' lossless]
      have w1: "\<And>\<eta>. wiring (\<I>_inner \<eta>) (\<I>_middle \<eta>) (cnv_inner \<eta>) (w1 \<eta>)"
        and adv1: "negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (ideal \<eta>) (cnv_inner \<eta> |\<^sub>= 1\<^sub>C \<rhd> middle \<eta>))"
        by auto

      obtain f g where WT_inner [WT_intro]: "\<And>\<eta>. \<I>_inner \<eta>, \<I>_middle \<eta> \<turnstile>\<^sub>C cnv_inner \<eta> \<surd>"
        and fg [simp]: "\<And>\<eta>. w1 \<eta> = (f \<eta>, g \<eta>)"
        and eq1: "\<And>\<eta>. \<I>_inner \<eta>, \<I>_middle \<eta> \<turnstile>\<^sub>C cnv_inner \<eta> \<sim> map_converter id id (f \<eta>) (g \<eta>) 1\<^sub>C"
        using w1
        apply(atomize_elim)
        apply(fold all_conj_distrib)
        apply(subst choice_iff[symmetric])+
        apply(fastforce elim!: wiring.cases)
        done

      from w1 have [WT_intro]: "\<I>_inner \<eta>, \<I>_middle \<eta> \<turnstile>\<^sub>C cnv_inner \<eta> \<surd>" for \<eta> by cases

      let ?\<D> = "\<lambda>\<eta>. absorb (\<D> \<eta>) (map_converter id id (f \<eta>) (g \<eta>) 1\<^sub>C |\<^sub>= 1\<^sub>C)"
      have \<I>: "\<I>_inner \<eta> \<le> map_\<I> (f \<eta>) (g \<eta>) (\<I>_middle \<eta>)" for \<eta>
        using eq_\<I>_converterD_WT1[OF eq1 WT_inner, of \<eta>] by(rule WT_map_converter_idD)
      with WT_converter_id have [WT_intro]: "\<I>_inner \<eta>, map_\<I> (f \<eta>) (g \<eta>) (\<I>_middle \<eta>) \<turnstile>\<^sub>C 1\<^sub>C \<surd>" 
        for \<eta> by(rule WT_converter_mono) simp

      have WT_D': "\<I>_middle \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g ?\<D> \<eta> \<surd>" for \<eta> by(rule WT_intro | simp)+
      have bound': "interaction_any_bounded_by (?\<D> \<eta>) (bound_outer \<eta>)" for \<eta>
        by(subst map_converter_id_move_left)(interaction_bound; simp)
      have [simp]: "plossless_converter (\<I>_inner \<eta>) (map_\<I> (f \<eta>) (g \<eta>) (\<I>_middle \<eta>)) 1\<^sub>C " for \<eta>
        using plossless_id_converter _ \<I>[of \<eta>] by(rule plossless_converter_mono) auto
      from lossless
      have "plossless_gpv (\<I>_middle \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (?\<D> \<eta>)" if lossless_outer for \<eta>
        by(rule plossless_gpv_absorb)(auto simp add: that intro!: WT_intro plossless_parallel_converter2 plossless_map_converter)
      from correct_outer[OF WT_D' bound' this]
      have w2: "\<And>\<eta>. wiring (\<I>_middle \<eta>) (\<I>_real \<eta>) (cnv_outer \<eta>) (w2 \<eta>)"
        and adv2: "negligible (\<lambda>\<eta>. advantage (?\<D> \<eta>) (middle \<eta>) (cnv_outer \<eta> |\<^sub>= 1\<^sub>C \<rhd> real \<eta>))"
        by auto
      from w2 have [WT_intro]: "\<I>_middle \<eta>, \<I>_real \<eta> \<turnstile>\<^sub>C cnv_outer \<eta> \<surd>" for \<eta> by cases

      show "wiring (\<I>_inner \<eta>) (\<I>_real \<eta>) (?cnv \<eta>) (w1 \<eta> \<circ>\<^sub>w w2 \<eta>)" for \<eta>
        using w1 w2 by(rule wiring_comp_converterI)

      have eq1': "connect (\<D> \<eta>) (cnv_inner \<eta> |\<^sub>= 1\<^sub>C \<rhd> middle \<eta>) = connect (?\<D> \<eta>) (middle \<eta>)" for \<eta>
        unfolding distinguish_attach[symmetric]
        by(rule connect_eq_resource_cong WT_intro eq_\<I>_attach_on' parallel_converter2_eq_\<I>_cong eq1 eq_\<I>_converter_reflI order_refl)+
      have eq2': "connect (?\<D> \<eta>) (cnv_outer \<eta> |\<^sub>= 1\<^sub>C \<rhd> real \<eta>) = connect (\<D> \<eta>) (?cnv \<eta> |\<^sub>= 1\<^sub>C \<odot> 1\<^sub>C \<rhd> real \<eta>)" for \<eta>
        unfolding distinguish_attach[symmetric] attach_compose comp_converter_parallel2[symmetric]
        by(rule connect_eq_resource_cong WT_intro eq_\<I>_attach_on' parallel_converter2_eq_\<I>_cong eq1[symmetric] eq_\<I>_converter_reflI order_refl|simp)+

      show "negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (ideal \<eta>) (?cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real \<eta>))"
        using negligible_plus[OF adv1 adv2] unfolding advantage_def eq1' eq2' comp_converter_id_right
        by(rule negligible_le) simp
    qed
  }
qed

theorem (in constructive_security) lifting:
  assumes WT_conv [WT_intro]: "\<And>\<eta>. \<I>_common' \<eta>, \<I>_common \<eta> \<turnstile>\<^sub>C conv \<eta> \<surd>"
    and bound [interaction_bound]: "\<And>\<eta>. interaction_any_bounded_converter (conv \<eta>) (bound_conv \<eta>)"
    and bound_le: "\<And>\<eta>. bound' \<eta> * max (bound_conv \<eta>) 1 \<le> bound \<eta>"
    and lossless [plossless_intro]: "\<And>\<eta>. lossless \<Longrightarrow> plossless_converter (\<I>_common' \<eta>) (\<I>_common \<eta>) (conv \<eta>)"
  shows "constructive_security
     (\<lambda>\<eta>. 1\<^sub>C |\<^sub>= conv \<eta> \<rhd> real_resource \<eta>) (\<lambda>\<eta>. 1\<^sub>C |\<^sub>= conv \<eta> \<rhd> ideal_resource \<eta>) sim
     \<I>_real \<I>_ideal \<I>_common' bound' lossless w"
proof
  fix \<A> :: "security \<Rightarrow> ('a + 'g, 'b + 'h) distinguisher"
  assume WT_\<A> [WT_intro]: "\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common' \<eta> \<turnstile>g \<A> \<eta> \<surd>" for \<eta>
  assume bound_\<A> [interaction_bound]: "interaction_any_bounded_by (\<A> \<eta>) (bound' \<eta>)" for \<eta>
  assume lossless_\<A> [plossless_intro]: "lossless \<Longrightarrow> plossless_gpv (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common' \<eta>) (\<A> \<eta>)" for \<eta>

  let ?\<A> = "\<lambda>\<eta>. absorb (\<A> \<eta>) (1\<^sub>C |\<^sub>= conv \<eta>)"

  have ideal: "connect (\<A> \<eta>) (sim \<eta> |\<^sub>= 1\<^sub>C \<rhd> 1\<^sub>C |\<^sub>= conv \<eta> \<rhd> ideal_resource \<eta>) = connect (?\<A> \<eta>) (sim \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal_resource \<eta>)" for \<eta>
    by(simp add: distinguish_attach[symmetric] attach_compose[symmetric] comp_converter_parallel2 comp_converter_id_left comp_converter_id_right)
  have real: "connect (\<A> \<eta>) (1\<^sub>C |\<^sub>= conv \<eta> \<rhd> real_resource \<eta>) = connect (?\<A> \<eta>) (real_resource \<eta>)" for \<eta>
    by(simp add: distinguish_attach[symmetric])
  have "\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g ?\<A> \<eta> \<surd>" for \<eta> by(rule WT_intro)+
  moreover have "interaction_any_bounded_by (?\<A> \<eta>) (bound \<eta>)" for \<eta>
    by interaction_bound_converter(use bound_le[of \<eta>] in \<open>simp add: max.commute\<close>)
  moreover have " plossless_gpv (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (absorb (\<A> \<eta>) (1\<^sub>C |\<^sub>= conv \<eta>))" if lossless for \<eta>
    by(rule plossless_intro WT_intro | simp add: that)+
  ultimately show "negligible (\<lambda>\<eta>. advantage (\<A> \<eta>) (sim \<eta> |\<^sub>= 1\<^sub>C \<rhd> 1\<^sub>C |\<^sub>= conv \<eta> \<rhd> ideal_resource \<eta>) (1\<^sub>C |\<^sub>= conv \<eta> \<rhd> real_resource \<eta>))"
    unfolding advantage_def ideal real by(rule adv[unfolded advantage_def])
next
  from correct obtain cnv 
    where correct': "\<And>\<D>. \<lbrakk> \<And>\<eta>. \<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<D> \<eta> \<surd>;
          \<And>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (bound \<eta>);
          \<And>\<eta>. lossless \<Longrightarrow> plossless_gpv (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<D> \<eta>) \<rbrakk>
          \<Longrightarrow> (\<forall>\<eta>. wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w \<eta>)) \<and>
              negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (ideal_resource \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real_resource \<eta>))"
    by blast
  show "\<exists>cnv. \<forall>\<D>. (\<forall>\<eta>. \<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common' \<eta> \<turnstile>g \<D> \<eta> \<surd>) \<longrightarrow>
         (\<forall>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (bound' \<eta>)) \<longrightarrow>
         (\<forall>\<eta>. lossless \<longrightarrow> plossless_gpv (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common' \<eta>) (\<D> \<eta>)) \<longrightarrow>
         (\<forall>\<eta>. wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w \<eta>)) \<and>
         negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (1\<^sub>C |\<^sub>= conv \<eta> \<rhd> ideal_resource \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> 1\<^sub>C |\<^sub>= conv \<eta> \<rhd> real_resource \<eta>))"
  proof(intro exI conjI strip)
    fix \<D> :: "security \<Rightarrow> ('c + 'g, 'd + 'h) distinguisher"
    assume WT_D [rule_format, WT_intro]: "\<forall>\<eta>. \<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common' \<eta> \<turnstile>g \<D> \<eta> \<surd>"
      and bound [rule_format, interaction_bound]: "\<forall>\<eta>. interaction_bounded_by (\<lambda>_. True) (\<D> \<eta>) (bound' \<eta>)"
      and lossless [rule_format]: "\<forall>\<eta>. lossless \<longrightarrow> plossless_gpv (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common' \<eta>) (\<D> \<eta>)"

    let ?\<D> = "\<lambda>\<eta>. absorb (\<D> \<eta>) (1\<^sub>C |\<^sub>= conv \<eta>)"
    have WT_D' [WT_intro]: "\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g ?\<D> \<eta> \<surd>" for \<eta> by(rule WT_intro)+
    have bound': "interaction_any_bounded_by (?\<D> \<eta>) (bound \<eta>)" for \<eta>
      by interaction_bound(use bound_le[of \<eta>] in \<open>auto simp add: max_def split: if_split_asm\<close>)
    have "plossless_gpv (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (?\<D> \<eta>)" if lossless for \<eta>
      by(rule lossless that WT_intro plossless_intro)+
    from correct'[OF WT_D' bound' this]
    have w1: "wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w \<eta>)" 
      and adv': "negligible (\<lambda>\<eta>. advantage (?\<D> \<eta>) (ideal_resource \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real_resource \<eta>))" for \<eta>
      by auto
    show "wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w \<eta>)" for \<eta> by(rule w1)
    have "cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> 1\<^sub>C |\<^sub>= conv \<eta> \<rhd> real_resource \<eta> = 1\<^sub>C |\<^sub>= conv \<eta> \<rhd> cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real_resource \<eta>" for \<eta>
      by(simp add: attach_compose[symmetric] comp_converter_parallel2 comp_converter_id_left comp_converter_id_right)
    with adv'
    show "negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (1\<^sub>C |\<^sub>= conv \<eta> \<rhd> ideal_resource \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> 1\<^sub>C |\<^sub>= conv \<eta> \<rhd> real_resource \<eta>))"
      by(simp add: advantage_def distinguish_attach[symmetric])
  qed
qed(rule WT_intro)+

theorem constructive_security_trivial:
  fixes res
  assumes [WT_intro]: "\<And>\<eta>. \<I> \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res res \<eta> \<surd>"
  shows "constructive_security res res (\<lambda>_. 1\<^sub>C) \<I> \<I> \<I>_common bound lossless (\<lambda>_. (id, id))"
proof
  show "\<I> \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res res \<eta> \<surd>" and "\<I> \<eta>, \<I> \<eta> \<turnstile>\<^sub>C 1\<^sub>C \<surd>" for \<eta> by(rule WT_intro)+

  fix \<A> :: "security \<Rightarrow> ('a + 'b, 'c + 'd) distinguisher"
  assume WT [WT_intro]: "\<I> \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<A> \<eta> \<surd>" for \<eta>
  have "connect (\<A> \<eta>) (1\<^sub>C |\<^sub>= 1\<^sub>C \<rhd> res \<eta>) = connect (\<A> \<eta>) (1\<^sub>C \<rhd> res \<eta>)" for \<eta>
    by(rule connect_eq_resource_cong[OF WT])(fastforce intro: WT_intro eq_\<I>_attach_on' parallel_converter2_id_id)+
  then show "negligible (\<lambda>\<eta>. advantage (\<A> \<eta>) (1\<^sub>C |\<^sub>= 1\<^sub>C \<rhd> res \<eta>) (res \<eta>))"
    unfolding advantage_def by simp
next
  show "\<exists>cnv. \<forall>\<D>. (\<forall>\<eta>. \<I> \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<D> \<eta> \<surd>) \<longrightarrow>
         (\<forall>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (bound \<eta>)) \<longrightarrow>
         (\<forall>\<eta>. lossless \<longrightarrow> plossless_gpv (\<I> \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<D> \<eta>)) \<longrightarrow>
         (\<forall>\<eta>. wiring (\<I> \<eta>) (\<I> \<eta>) (cnv \<eta>) (id, id)) \<and>
         negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (res \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> res \<eta>))"
  proof(intro exI strip conjI)
    fix \<D> :: "security \<Rightarrow> ('a + 'b, 'c + 'd) distinguisher"
    assume WT_D [rule_format, WT_intro]: "\<forall>\<eta>. \<I> \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<D> \<eta> \<surd>"
      and bound [rule_format, interaction_bound]: "\<forall>\<eta>. interaction_bounded_by (\<lambda>_. True) (\<D> \<eta>) (bound \<eta>)"
      and lossless [rule_format]: "\<forall>\<eta>. lossless \<longrightarrow> plossless_gpv (\<I> \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<D> \<eta>)"
    show "wiring (\<I> \<eta>) (\<I> \<eta>) 1\<^sub>C (id, id)" for \<eta> by simp
    have "connect (\<D> \<eta>) (1\<^sub>C |\<^sub>= 1\<^sub>C \<rhd> res \<eta>) = connect (\<D> \<eta>) (1\<^sub>C \<rhd> res \<eta>)" for \<eta>
      by(rule connect_eq_resource_cong)(rule WT_intro eq_\<I>_attach_on' parallel_converter2_id_id order_refl)+
    then show "negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (res \<eta>) (1\<^sub>C |\<^sub>= 1\<^sub>C \<rhd> res \<eta>))"
      by(auto simp add: advantage_def)
  qed
qed

theorem parallel_constructive_security:
  assumes "constructive_security real1 ideal1 sim1 \<I>_real1 \<I>_inner1 \<I>_common1 bound1 lossless1 w1"
  assumes "constructive_security real2 ideal2 sim2 \<I>_real2 \<I>_inner2 \<I>_common2 bound2 lossless2 w2"
    (* TODO: add symmetric case for lossless1/2 *)
    and lossless_real1 [plossless_intro]: "\<And>\<eta>. lossless2 \<Longrightarrow> lossless_resource (\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_common1 \<eta>) (real1 \<eta>)"
    and lossless_sim2 [plossless_intro]: "\<And>\<eta>. lossless1 \<Longrightarrow> plossless_converter (\<I>_real2 \<eta>) (\<I>_inner2 \<eta>) (sim2 \<eta>)"
    and lossless_ideal2 [plossless_intro]: "\<And>\<eta>. lossless1 \<Longrightarrow> lossless_resource (\<I>_inner2 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>) (ideal2 \<eta>)"
  shows "constructive_security (\<lambda>\<eta>. parallel_wiring \<rhd> real1 \<eta> \<parallel> real2 \<eta>) (\<lambda>\<eta>. parallel_wiring \<rhd> ideal1 \<eta> \<parallel> ideal2 \<eta>) (\<lambda>\<eta>. sim1 \<eta> |\<^sub>= sim2 \<eta>) 
    (\<lambda>\<eta>. \<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_real2 \<eta>) (\<lambda>\<eta>. \<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_inner2 \<eta>) (\<lambda>\<eta>. \<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>)
    (\<lambda>\<eta>. min (bound1 \<eta>) (bound2 \<eta>)) (lossless1 \<or> lossless2) (\<lambda>\<eta>. w1 \<eta> |\<^sub>w w2 \<eta>)"
proof
  interpret sec1: constructive_security real1 ideal1 sim1 \<I>_real1 \<I>_inner1 \<I>_common1 bound1 lossless1 w1 by fact
  interpret sec2: constructive_security real2 ideal2 sim2 \<I>_real2 \<I>_inner2 \<I>_common2 bound2 lossless2 w2 by fact

  show "(\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_real2 \<eta>) \<oplus>\<^sub>\<I> (\<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>) \<turnstile>res parallel_wiring \<rhd> real1 \<eta> \<parallel> real2 \<eta> \<surd>"
    and "(\<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_inner2 \<eta>) \<oplus>\<^sub>\<I> (\<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>) \<turnstile>res parallel_wiring \<rhd> ideal1 \<eta> \<parallel> ideal2 \<eta> \<surd>"
    and "\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_real2 \<eta>, \<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_inner2 \<eta> \<turnstile>\<^sub>C sim1 \<eta> |\<^sub>= sim2 \<eta> \<surd>" for \<eta> by(rule WT_intro)+

  fix \<A> :: "security \<Rightarrow> (('a + 'g) + 'b + 'h, ('c + 'i) + 'd + 'j) distinguisher"
  assume WT [WT_intro]: "(\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_real2 \<eta>) \<oplus>\<^sub>\<I> (\<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>) \<turnstile>g \<A> \<eta> \<surd>" for \<eta>
  assume bound [interaction_bound]: "interaction_any_bounded_by (\<A> \<eta>) (min (bound1 \<eta>) (bound2 \<eta>))" for \<eta>
  assume lossless [plossless_intro]: "lossless1 \<or> lossless2 \<Longrightarrow> plossless_gpv ((\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_real2 \<eta>) \<oplus>\<^sub>\<I> (\<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>)) (\<A> \<eta>)" for \<eta>

  let ?\<A> = "\<lambda>\<eta>. absorb (\<A> \<eta>) (parallel_wiring \<odot> parallel_converter (converter_of_resource (real1 \<eta>)) 1\<^sub>C)"

  have *:"\<I>_uniform (outs_\<I> ((\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_real2 \<eta>) \<oplus>\<^sub>\<I> (\<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>)))
     UNIV,(\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_common1 \<eta>) \<oplus>\<^sub>\<I> (\<I>_inner2 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>) \<turnstile>\<^sub>C
    ((1\<^sub>C |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C) \<odot> parallel_wiring \<sim> ((1\<^sub>C |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C) \<odot> parallel_wiring" for \<eta>
    by(rule eq_\<I>_comp_cong, rule eq_\<I>_converter_mono)
      (auto simp add: le_\<I>_def intro: parallel_converter2_eq_\<I>_cong eq_\<I>_converter_reflI WT_converter_parallel_converter2
        WT_converter_id sec2.WT_sim parallel_converter2_id_id[symmetric] eq_\<I>_converter_reflI WT_parallel_wiring)

  have **: "outs_\<I> ((\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_real2 \<eta>) \<oplus>\<^sub>\<I> (\<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>)) \<turnstile>\<^sub>R
    ((1\<^sub>C |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C) \<odot> parallel_wiring \<rhd> real1 \<eta> \<parallel> ideal2 \<eta> \<sim>
    parallel_wiring \<odot> (converter_of_resource (real1 \<eta>) |\<^sub>\<propto> 1\<^sub>C) \<rhd> sim2 \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal2 \<eta>" for \<eta>
    unfolding comp_parallel_wiring
    by(rule eq_resource_on_trans, rule eq_\<I>_attach_on[where conv'="parallel_wiring \<odot> (1\<^sub>C |\<^sub>= sim2 \<eta> |\<^sub>= 1\<^sub>C)"]
        , (rule WT_intro)+, rule eq_\<I>_comp_cong, rule eq_\<I>_converter_mono)
      (auto simp add: le_\<I>_def attach_compose attach_parallel2 attach_converter_of_resource_conv_parallel_resource
        intro: WT_intro parallel_converter2_eq_\<I>_cong parallel_converter2_id_id eq_\<I>_converter_reflI)

  have ideal2:
    "connect (\<A> \<eta>) ((1\<^sub>C |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C \<rhd> parallel_wiring \<rhd> real1 \<eta> \<parallel> ideal2 \<eta>) =
     connect (?\<A> \<eta>) (sim2 \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal2 \<eta>)" for \<eta>
    unfolding distinguish_attach[symmetric]
  proof (rule connect_eq_resource_cong[OF WT, rotated], goal_cases)
    case 2
    then show ?case 
      by(subst attach_compose[symmetric], rule eq_resource_on_trans
          , rule eq_\<I>_attach_on[where conv'="((1\<^sub>C |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C) \<odot> parallel_wiring"])
        ((rule WT_intro)+ | intro * | intro ** )+
  qed (rule WT_intro)+
  have real2: "connect (\<A> \<eta>) (parallel_wiring \<rhd> real1 \<eta> \<parallel> real2 \<eta>) = connect (?\<A> \<eta>) (real2 \<eta>)" for \<eta>
    unfolding distinguish_attach[symmetric]
    by(simp add: attach_compose attach_converter_of_resource_conv_parallel_resource)
  have "\<I>_real2 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta> \<turnstile>g ?\<A> \<eta> \<surd>" for \<eta> by(rule WT_intro)+
  moreover have "interaction_any_bounded_by (?\<A> \<eta>) (bound2 \<eta>)" for \<eta>
    by interaction_bound_converter simp
  moreover have "plossless_gpv (\<I>_real2 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>) (?\<A> \<eta>)" if "lossless2" for \<eta> 
    by(rule plossless_intro WT_intro | simp add: that)+
  ultimately
  have negl2: "negligible (\<lambda>\<eta>. advantage (\<A> \<eta>)
     ((1\<^sub>C |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C \<rhd> parallel_wiring \<rhd> real1 \<eta> \<parallel> ideal2 \<eta>)
     (parallel_wiring \<rhd> real1 \<eta> \<parallel> real2 \<eta>))"
    unfolding advantage_def ideal2 real2 by(rule sec2.adv[unfolded advantage_def])

  let ?\<A> = "\<lambda>\<eta>. absorb (\<A> \<eta>) (parallel_wiring \<odot> parallel_converter 1\<^sub>C (converter_of_resource (sim2 \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal2 \<eta>)))"
  have ideal1: 
    "connect (\<A> \<eta>) ((sim1 \<eta> |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C \<rhd> parallel_wiring \<rhd> ideal1 \<eta> \<parallel> ideal2 \<eta>) =
     connect (?\<A> \<eta>) (sim1 \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal1 \<eta>)" for \<eta>
  proof -
    have *: "\<I>_uniform ((outs_\<I> (\<I>_real1 \<eta>) <+> outs_\<I> (\<I>_real2 \<eta>)) <+>  outs_\<I> (\<I>_common1 \<eta>) <+> 
      outs_\<I> (\<I>_common2 \<eta>)) UNIV,(\<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_common1 \<eta>) \<oplus>\<^sub>\<I> (\<I>_inner2 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>) \<turnstile>\<^sub>C
    ((sim1 \<eta> |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C) \<odot> parallel_wiring \<sim> ((sim1 \<eta> |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C) \<odot> parallel_wiring"
      by(rule eq_\<I>_comp_cong, rule eq_\<I>_converter_mono)
        (auto simp add: le_\<I>_def comp_parallel_wiring' attach_compose attach_parallel2 attach_converter_of_resource_conv_parallel_resource2
          intro: WT_intro parallel_converter2_id_id[symmetric] eq_\<I>_converter_reflI parallel_converter2_eq_\<I>_cong eq_\<I>_converter_mono)

    have **:"((outs_\<I> (\<I>_real1 \<eta>) <+> outs_\<I> (\<I>_real2 \<eta>)) <+> outs_\<I> (\<I>_common1 \<eta>) <+> outs_\<I> (\<I>_common2 \<eta>)) \<turnstile>\<^sub>R
    (sim1 \<eta> |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C \<rhd> parallel_wiring \<rhd> ideal1 \<eta> \<parallel> ideal2 \<eta> \<sim>
    parallel_wiring \<odot> (1\<^sub>C |\<^sub>\<propto> converter_of_resource (sim2 \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal2 \<eta>)) \<rhd>  sim1 \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal1 \<eta>"
      unfolding attach_compose[symmetric]
      by(rule eq_resource_on_trans, rule eq_\<I>_attach_on[where conv'="((sim1 \<eta> |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C) \<odot> parallel_wiring"])
        ((rule WT_intro)+ | intro * | auto simp add: le_\<I>_def comp_parallel_wiring' attach_compose 
          attach_parallel2 attach_converter_of_resource_conv_parallel_resource2 intro: WT_intro *)+

    show ?thesis
      unfolding distinguish_attach[symmetric] using WT
      by(rule connect_eq_resource_cong) (simp add: **, (rule WT_intro)+)
  qed

  have real1:
    "connect (\<A> \<eta>) ((1\<^sub>C |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C \<rhd> parallel_wiring \<rhd> real1 \<eta> \<parallel> ideal2 \<eta>) =
     connect (?\<A> \<eta>) (real1 \<eta>)" for \<eta>
  proof -
    have **: "\<I>_uniform (outs_\<I> ((\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_real2 \<eta>) \<oplus>\<^sub>\<I> (\<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>)))
     UNIV,(\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_common1 \<eta>) \<oplus>\<^sub>\<I> (\<I>_inner2 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>) \<turnstile>\<^sub>C
      ((1\<^sub>C |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C) \<odot> parallel_wiring \<sim> ((1\<^sub>C |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C) \<odot> parallel_wiring" 
      by(rule eq_\<I>_comp_cong, rule eq_\<I>_converter_mono)
        (auto simp add: le_\<I>_def intro: WT_intro parallel_converter2_eq_\<I>_cong WT_converter_parallel_converter2
          parallel_converter2_id_id[symmetric] eq_\<I>_converter_reflI WT_parallel_wiring)

    have *: "outs_\<I> ((\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_real2 \<eta>) \<oplus>\<^sub>\<I> (\<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>)) \<turnstile>\<^sub>R
    parallel_wiring \<odot> ((1\<^sub>C |\<^sub>= 1\<^sub>C) |\<^sub>= sim2 \<eta> |\<^sub>= 1\<^sub>C) \<rhd> real1 \<eta> \<parallel> ideal2 \<eta> \<sim>
    parallel_wiring \<odot> (1\<^sub>C |\<^sub>\<propto> converter_of_resource (sim2 \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal2 \<eta>)) \<rhd> real1 \<eta>"
      by(rule eq_resource_on_trans, rule eq_\<I>_attach_on[where conv'="parallel_wiring \<odot> (1\<^sub>C |\<^sub>= sim2 \<eta> |\<^sub>= 1\<^sub>C)"]
          , (rule WT_intro)+, rule eq_\<I>_comp_cong, rule eq_\<I>_converter_mono)
        (auto simp add: le_\<I>_def attach_compose attach_converter_of_resource_conv_parallel_resource2 attach_parallel2 
          intro: WT_intro parallel_converter2_eq_\<I>_cong parallel_converter2_id_id eq_\<I>_converter_reflI)

    show ?thesis
      unfolding distinguish_attach[symmetric] using WT
      by(rule connect_eq_resource_cong, fold attach_compose)
        (rule eq_resource_on_trans[where res'="((1\<^sub>C |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C) \<odot> parallel_wiring \<rhd> real1 \<eta> \<parallel> ideal2 \<eta>"]
          , (rule eq_\<I>_attach_on, (intro * ** | subst comp_parallel_wiring | rule eq_\<I>_attach_on | (rule WT_intro eq_\<I>_attach_on)+ )+))
  qed

  have "\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_common1 \<eta> \<turnstile>g ?\<A> \<eta> \<surd>" for \<eta> by(rule WT_intro)+
  moreover have "interaction_any_bounded_by (?\<A> \<eta>) (bound1 \<eta>)" for \<eta>
    by interaction_bound_converter simp
  moreover have "plossless_gpv (\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_common1 \<eta>) (?\<A> \<eta>)" if "lossless1" for \<eta> 
    by(rule plossless_intro WT_intro | simp add: that)+
  ultimately
  have negl1: "negligible (\<lambda>\<eta>. advantage (\<A> \<eta>) 
     ((sim1 \<eta> |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C \<rhd> parallel_wiring \<rhd> ideal1 \<eta> \<parallel> ideal2 \<eta>)
     ((1\<^sub>C |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C \<rhd> parallel_wiring \<rhd> real1 \<eta> \<parallel> ideal2 \<eta>))"
    unfolding advantage_def ideal1 real1 by(rule sec1.adv[unfolded advantage_def])

  from negligible_plus[OF negl1 negl2]
  show "negligible (\<lambda>\<eta>. advantage (\<A> \<eta>) ((sim1 \<eta> |\<^sub>= sim2 \<eta>) |\<^sub>= 1\<^sub>C \<rhd> parallel_wiring \<rhd> ideal1 \<eta> \<parallel> ideal2 \<eta>)
         (parallel_wiring \<rhd> real1 \<eta> \<parallel> real2 \<eta>))"
    by(rule negligible_mono) (auto simp add: advantage_def intro!: eventuallyI landau_o.big_mono )
next
  interpret sec1: constructive_security real1 ideal1 sim1 \<I>_real1 \<I>_inner1 \<I>_common1 bound1 lossless1 w1 by fact
  interpret sec2: constructive_security real2 ideal2 sim2 \<I>_real2 \<I>_inner2 \<I>_common2 bound2 lossless2 w2 by fact
  from sec1.correct obtain cnv1
    where correct1: "\<And>\<D>. \<lbrakk> \<And>\<eta>. \<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_common1 \<eta> \<turnstile>g \<D> \<eta> \<surd>;
      \<And>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (bound1 \<eta>);
      \<And>\<eta>. lossless1 \<Longrightarrow> plossless_gpv (\<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_common1 \<eta>) (\<D> \<eta>) \<rbrakk>
     \<Longrightarrow> (\<forall>\<eta>. wiring (\<I>_inner1 \<eta>) (\<I>_real1 \<eta>) (cnv1 \<eta>) (w1 \<eta>)) \<and>
         negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (ideal1 \<eta>) (cnv1 \<eta> |\<^sub>= 1\<^sub>C \<rhd> real1 \<eta>))"
    by blast
  from sec2.correct obtain cnv2
    where correct2: "\<And>\<D>. \<lbrakk> \<And>\<eta>. \<I>_inner2 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta> \<turnstile>g \<D> \<eta> \<surd>;
      \<And>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (bound2 \<eta>);
      \<And>\<eta>. lossless2 \<Longrightarrow> plossless_gpv (\<I>_inner2 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>) (\<D> \<eta>) \<rbrakk>
     \<Longrightarrow> (\<forall>\<eta>. wiring (\<I>_inner2 \<eta>) (\<I>_real2 \<eta>) (cnv2 \<eta>) (w2 \<eta>)) \<and>
         negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (ideal2 \<eta>) (cnv2 \<eta> |\<^sub>= 1\<^sub>C \<rhd> real2 \<eta>))"
    by blast
  show "\<exists>cnv. \<forall>\<D>. (\<forall>\<eta>. (\<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_inner2 \<eta>) \<oplus>\<^sub>\<I> (\<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>) \<turnstile>g \<D> \<eta> \<surd>) \<longrightarrow>
       (\<forall>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (min (bound1 \<eta>) (bound2 \<eta>))) \<longrightarrow>
       (\<forall>\<eta>. lossless1 \<or> lossless2 \<longrightarrow> plossless_gpv ((\<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_inner2 \<eta>) \<oplus>\<^sub>\<I> (\<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>)) (\<D> \<eta>)) \<longrightarrow>
       (\<forall>\<eta>. wiring (\<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_inner2 \<eta>) (\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_real2 \<eta>) (cnv \<eta>) (w1 \<eta> |\<^sub>w w2 \<eta>)) \<and>
       negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (parallel_wiring \<rhd> ideal1 \<eta> \<parallel> ideal2 \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> parallel_wiring \<rhd> real1 \<eta> \<parallel> real2 \<eta>))"
  proof(intro exI strip conjI)
    fix \<D> :: "security \<Rightarrow> (('e + 'k) + 'b + 'h, ('f + 'l) + 'd + 'j) distinguisher"
    assume WT_D [rule_format, WT_intro]: "\<forall>\<eta>. (\<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_inner2 \<eta>) \<oplus>\<^sub>\<I> (\<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>) \<turnstile>g \<D> \<eta> \<surd>"
      and bound [rule_format, interaction_bound]: "\<forall>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (min (bound1 \<eta>) (bound2 \<eta>))"
      and lossless [rule_format, plossless_intro]: "\<forall>\<eta>. lossless1 \<or> lossless2 \<longrightarrow> plossless_gpv ((\<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_inner2 \<eta>) \<oplus>\<^sub>\<I> (\<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>)) (\<D> \<eta>)"

    let ?cnv = "\<lambda>\<eta>. cnv1 \<eta> |\<^sub>= cnv2 \<eta>"

    let ?\<D>1 = "\<lambda>\<eta>. absorb (\<D> \<eta>) (parallel_wiring \<odot> parallel_converter 1\<^sub>C (converter_of_resource (ideal2 \<eta>)))"
    have WT1: "\<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_common1 \<eta> \<turnstile>g ?\<D>1 \<eta> \<surd>" for \<eta> by(rule WT_intro)+
    have bound1: "interaction_any_bounded_by (?\<D>1 \<eta>) (bound1 \<eta>)" for \<eta> by interaction_bound simp
    have "plossless_gpv (\<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_common1 \<eta>) (?\<D>1 \<eta>)" if lossless1 for \<eta>
      by(rule plossless_intro WT_intro | simp add: that)+
    from correct1[OF WT1 bound1 this]
    have w1: "wiring (\<I>_inner1 \<eta>) (\<I>_real1 \<eta>) (cnv1 \<eta>) (w1 \<eta>)" 
      and adv1: "negligible (\<lambda>\<eta>. advantage (?\<D>1 \<eta>) (ideal1 \<eta>) (cnv1 \<eta> |\<^sub>= 1\<^sub>C \<rhd> real1 \<eta>))" for \<eta>
      by auto

    from w1 obtain f g where fg: "\<And>\<eta>. w1 \<eta> = (f \<eta>, g \<eta>)"
      and [WT_intro]: "\<And>\<eta>. \<I>_inner1 \<eta>, \<I>_real1 \<eta> \<turnstile>\<^sub>C cnv1 \<eta> \<surd>" 
      and eq1: "\<And>\<eta>. \<I>_inner1 \<eta>, \<I>_real1 \<eta> \<turnstile>\<^sub>C cnv1 \<eta> \<sim> map_converter id id (f \<eta>) (g \<eta>) 1\<^sub>C"
      apply atomize_elim
      apply(fold all_conj_distrib)
      apply(subst choice_iff[symmetric])+
      apply(fastforce elim!: wiring.cases)
      done
    have \<I>1: "\<I>_inner1 \<eta> \<le> map_\<I> (f \<eta>) (g \<eta>) (\<I>_real1 \<eta>)" for \<eta>
      using eq_\<I>_converterD_WT1[OF eq1] by(rule WT_map_converter_idD)(rule WT_intro)
    with WT_converter_id order_refl have [WT_intro]: "\<I>_inner1 \<eta>, map_\<I> (f \<eta>) (g \<eta>) (\<I>_real1 \<eta>) \<turnstile>\<^sub>C 1\<^sub>C \<surd>" for \<eta>
      by(rule WT_converter_mono)
    have lossless1 [plossless_intro]: "plossless_converter (\<I>_inner1 \<eta>) (\<I>_real1 \<eta>) (map_converter id id (f \<eta>) (g \<eta>) 1\<^sub>C)" for \<eta>
      by(rule plossless_map_converter)(rule plossless_intro order_refl \<I>1 WT_intro plossless_converter_mono | simp)+

    let ?\<D>2 = "\<lambda>\<eta>. absorb (\<D> \<eta>) (parallel_wiring \<odot> parallel_converter (converter_of_resource (map_converter id id (f \<eta>) (g \<eta>) 1\<^sub>C |\<^sub>= 1\<^sub>C \<rhd> real1 \<eta>)) 1\<^sub>C)"
    have WT2: "\<I>_inner2 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta> \<turnstile>g ?\<D>2 \<eta> \<surd>" for \<eta> by(rule WT_intro | simp)+
    have bound2: "interaction_any_bounded_by (?\<D>2 \<eta>) (bound2 \<eta>)" for \<eta> by interaction_bound simp
    have "plossless_gpv (\<I>_inner2 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>) (?\<D>2 \<eta>)" if lossless2 for \<eta>
      by(rule plossless_intro WT_intro | simp add: that)+
    from correct2[OF WT2 bound2 this]
    have w2: "wiring (\<I>_inner2 \<eta>) (\<I>_real2 \<eta>) (cnv2 \<eta>) (w2 \<eta>)" 
      and adv2: "negligible (\<lambda>\<eta>. advantage (?\<D>2 \<eta>) (ideal2 \<eta>) (cnv2 \<eta> |\<^sub>= 1\<^sub>C \<rhd> real2 \<eta>))" for \<eta>
      by auto

    from w2 have [WT_intro]: "\<I>_inner2 \<eta>, \<I>_real2 \<eta> \<turnstile>\<^sub>C cnv2 \<eta> \<surd>" for \<eta> by cases

    have *: "connect (\<D> \<eta>) (?cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> parallel_wiring \<rhd> real1 \<eta> \<parallel> real2 \<eta>) =
      connect (?\<D>2 \<eta>) (cnv2 \<eta> |\<^sub>= 1\<^sub>C \<rhd> real2 \<eta>)" for \<eta>
    proof -
      have "outs_\<I> ((\<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_inner2 \<eta>) \<oplus>\<^sub>\<I> (\<I>_common1 \<eta> \<oplus>\<^sub>\<I> \<I>_common2 \<eta>)) \<turnstile>\<^sub>R
         ?cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> parallel_wiring \<rhd> real1 \<eta> \<parallel> real2 \<eta> \<sim> 
         (map_converter id id (f \<eta>) (g \<eta>) 1\<^sub>C |\<^sub>= cnv2 \<eta>) |\<^sub>= (1\<^sub>C |\<^sub>= 1\<^sub>C) \<rhd> parallel_wiring \<rhd> real1 \<eta> \<parallel> real2 \<eta>"
        by(rule eq_\<I>_attach_on' WT_intro parallel_converter2_eq_\<I>_cong eq1 eq_\<I>_converter_reflI parallel_converter2_id_id[symmetric])+ simp
      also have "(map_converter id id (f \<eta>) (g \<eta>) 1\<^sub>C |\<^sub>= cnv2 \<eta>) |\<^sub>= (1\<^sub>C |\<^sub>= 1\<^sub>C) \<rhd> parallel_wiring \<rhd> real1 \<eta> \<parallel> real2 \<eta> =
        parallel_wiring \<rhd> (map_converter id id (f \<eta>) (g \<eta>) 1\<^sub>C |\<^sub>= 1\<^sub>C \<rhd> real1 \<eta>) \<parallel> (cnv2 \<eta> |\<^sub>= 1\<^sub>C \<rhd> real2 \<eta>)"
        by(simp add: comp_parallel_wiring' attach_compose attach_parallel2)
      finally show ?thesis
        by(auto intro!: connect_eq_resource_cong[OF WT_D] intro: WT_intro simp add: distinguish_attach[symmetric] attach_compose attach_converter_of_resource_conv_parallel_resource)
    qed

    have **: "connect (?\<D>2 \<eta>) (ideal2 \<eta>) = connect (?\<D>1 \<eta>) (cnv1 \<eta> |\<^sub>= 1\<^sub>C \<rhd> real1 \<eta>)" for \<eta>
    proof -
      have "connect (?\<D>2 \<eta>) (ideal2 \<eta>) = 
        connect (\<D> \<eta>) (parallel_wiring \<rhd> ((map_converter id id (f \<eta>) (g \<eta>) 1\<^sub>C |\<^sub>= 1\<^sub>C) |\<^sub>= 1\<^sub>C) \<rhd> (real1 \<eta> \<parallel> ideal2 \<eta>))"
        by(simp add: distinguish_attach[symmetric] attach_converter_of_resource_conv_parallel_resource attach_compose attach_parallel2)
      also have "\<dots> = connect (\<D> \<eta>) (parallel_wiring \<rhd> ((cnv1 \<eta> |\<^sub>= 1\<^sub>C) |\<^sub>= 1\<^sub>C) \<rhd> (real1 \<eta> \<parallel> ideal2 \<eta>))"
        unfolding attach_compose[symmetric] using WT_D
        by(rule connect_eq_resource_cong[symmetric])
          (rule eq_\<I>_attach_on' WT_intro eq_\<I>_comp_cong eq_\<I>_converter_reflI parallel_converter2_eq_\<I>_cong eq1 | simp)+
      also have "\<dots> = connect (?\<D>1 \<eta>) (cnv1 \<eta> |\<^sub>= 1\<^sub>C \<rhd> real1 \<eta>)"
        by(simp add: distinguish_attach[symmetric] attach_converter_of_resource_conv_parallel_resource2 attach_compose attach_parallel2)
      finally show ?thesis .
    qed

    have ***: "connect (?\<D>1 \<eta>) (ideal1 \<eta>) = connect (\<D> \<eta>) (parallel_wiring \<rhd> ideal1 \<eta> \<parallel> ideal2 \<eta>)" for \<eta>
      by(auto intro!: connect_eq_resource_cong[OF WT_D] simp add: attach_converter_of_resource_conv_parallel_resource2 distinguish_attach[symmetric] attach_compose intro: WT_intro)

    show "wiring (\<I>_inner1 \<eta> \<oplus>\<^sub>\<I> \<I>_inner2 \<eta>) (\<I>_real1 \<eta> \<oplus>\<^sub>\<I> \<I>_real2 \<eta>) (?cnv \<eta>) (w1 \<eta> |\<^sub>w w2 \<eta>)" for \<eta>
      using w1 w2 by(rule wiring_parallel_converter2)
    from negligible_plus[OF adv1 adv2]
    show "negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (parallel_wiring \<rhd> ideal1 \<eta> \<parallel> ideal2 \<eta>) (?cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> parallel_wiring \<rhd> real1 \<eta> \<parallel> real2 \<eta>))"
      by(rule negligible_le)(simp add: advantage_def * ** ***)
  qed
qed

theorem (in constructive_security) parallel_realisation1:
  assumes WT_res: "\<And>\<eta>. \<I>_res \<eta> \<oplus>\<^sub>\<I> \<I>_common' \<eta> \<turnstile>res res \<eta> \<surd>"
    and lossless_res: "\<And>\<eta>. lossless \<Longrightarrow> lossless_resource (\<I>_res \<eta> \<oplus>\<^sub>\<I> \<I>_common' \<eta>) (res \<eta>)"
  shows "constructive_security (\<lambda>\<eta>. parallel_wiring \<rhd> res \<eta> \<parallel> real_resource \<eta>)
    (\<lambda>\<eta>. parallel_wiring \<rhd> (res \<eta> \<parallel> ideal_resource \<eta>)) (\<lambda>\<eta>. parallel_converter2 id_converter (sim \<eta>)) 
    (\<lambda>\<eta>. \<I>_res \<eta> \<oplus>\<^sub>\<I> \<I>_real \<eta>) (\<lambda>\<eta>. \<I>_res \<eta> \<oplus>\<^sub>\<I> \<I>_ideal \<eta>) (\<lambda>\<eta>. \<I>_common' \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) bound lossless (\<lambda>\<eta>. (id, id) |\<^sub>w w \<eta>)"
  by(rule parallel_constructive_security[OF constructive_security_trivial[where lossless=False and bound="\<lambda>_. \<infinity>", OF WT_res], simplified, OF _ lossless_res])
    unfold_locales

theorem (in constructive_security) parallel_realisation2:
  assumes WT_res: "\<And>\<eta>. \<I>_res \<eta> \<oplus>\<^sub>\<I> \<I>_common' \<eta> \<turnstile>res res \<eta> \<surd>"
    and lossless_res: "\<And>\<eta>. lossless \<Longrightarrow> lossless_resource (\<I>_res \<eta> \<oplus>\<^sub>\<I> \<I>_common' \<eta>) (res \<eta>)"
  shows "constructive_security (\<lambda>\<eta>. parallel_wiring \<rhd> real_resource \<eta> \<parallel> res \<eta>)
    (\<lambda>\<eta>. parallel_wiring \<rhd> (ideal_resource \<eta> \<parallel> res \<eta>)) (\<lambda>\<eta>. parallel_converter2 (sim \<eta>) id_converter) 
    (\<lambda>\<eta>. \<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_res \<eta>) (\<lambda>\<eta>. \<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_res \<eta>) (\<lambda>\<eta>. \<I>_common \<eta> \<oplus>\<^sub>\<I> \<I>_common' \<eta>) bound lossless (\<lambda>\<eta>. w \<eta> |\<^sub>w (id, id))"
  by(rule parallel_constructive_security[OF _ constructive_security_trivial[where lossless=False and bound="\<lambda>_. \<infinity>", OF WT_res], simplified, OF _ lossless_res])
    unfold_locales

theorem (in constructive_security) parallel_resource1:
  assumes WT_res [WT_intro]: "\<And>\<eta>. \<I>_res \<eta> \<turnstile>res res \<eta> \<surd>"
    and lossless_res [plossless_intro]: "\<And>\<eta>. lossless \<Longrightarrow> lossless_resource (\<I>_res \<eta>) (res \<eta>)"
  shows "constructive_security (\<lambda>\<eta>. parallel_resource1_wiring \<rhd> res \<eta> \<parallel> real_resource \<eta>)
    (\<lambda>\<eta>. parallel_resource1_wiring \<rhd> res \<eta> \<parallel> ideal_resource \<eta>) sim 
    \<I>_real \<I>_ideal (\<lambda>\<eta>. \<I>_res \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) bound lossless w"
proof
  fix \<A> :: "security \<Rightarrow> ('a + 'g + 'e, 'b + 'h + 'f) distinguisher"
  assume WT [WT_intro]: "\<I>_real \<eta> \<oplus>\<^sub>\<I> (\<I>_res \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) \<turnstile>g \<A> \<eta> \<surd>" for \<eta>
  assume bound [interaction_bound]: "interaction_any_bounded_by (\<A> \<eta>) (bound \<eta>)" for \<eta>
  assume lossless [plossless_intro]: "lossless \<Longrightarrow> plossless_gpv (\<I>_real \<eta> \<oplus>\<^sub>\<I> (\<I>_res \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>)) (\<A> \<eta>)" for \<eta>

  let ?\<A> = "\<lambda>\<eta>. absorb (\<A> \<eta>) (swap_lassocr \<odot> parallel_converter (converter_of_resource (res \<eta>)) 1\<^sub>C)"
  have ideal:
    "connect (\<A> \<eta>) (sim \<eta> |\<^sub>= 1\<^sub>C \<rhd> parallel_resource1_wiring \<rhd> res \<eta> \<parallel> ideal_resource \<eta>) =
     connect (?\<A> \<eta>) (sim \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal_resource \<eta>)" for \<eta>
  proof -
    have[intro]: "\<I>_uniform (outs_\<I> (\<I>_real \<eta>) <+> outs_\<I> (\<I>_res \<eta>) <+> outs_\<I> (\<I>_common \<eta>))
     UNIV,\<I>_ideal \<eta> \<oplus>\<^sub>\<I> (\<I>_res \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) \<turnstile>\<^sub>C  sim \<eta> |\<^sub>= 1\<^sub>C \<sim> sim \<eta> |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C " 
      by(rule eq_\<I>_converter_mono) (auto simp add: le_\<I>_def intro!: 
          WT_intro parallel_converter2_id_id[symmetric] parallel_converter2_eq_\<I>_cong eq_\<I>_converter_reflI)

    have *: "outs_\<I> (\<I>_real \<eta> \<oplus>\<^sub>\<I> (\<I>_res \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>)) \<turnstile>\<^sub>R  (sim \<eta> |\<^sub>= 1\<^sub>C) \<odot> parallel_resource1_wiring \<rhd> res \<eta> \<parallel> ideal_resource \<eta> \<sim>
      swap_lassocr \<odot> (converter_of_resource (res \<eta>) |\<^sub>\<propto> 1\<^sub>C) \<rhd> sim \<eta> |\<^sub>= 1\<^sub>C \<rhd> ideal_resource \<eta>" 
      by (rule eq_resource_on_trans[where res'="(sim \<eta> |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C) \<odot> parallel_resource1_wiring \<rhd> res \<eta> \<parallel> ideal_resource \<eta>"], 
          rule eq_\<I>_attach_on, (rule  WT_intro)+, rule eq_\<I>_comp_cong)
        (auto simp add: parallel_resource1_wiring_def comp_swap_lassocr attach_compose attach_parallel2 
          attach_converter_of_resource_conv_parallel_resource intro!: WT_intro eq_\<I>_converter_reflI)  

    show ?thesis
      unfolding distinguish_attach[symmetric] using WT
      by(rule connect_eq_resource_cong, subst attach_compose[symmetric])
        (intro *, (rule WT_intro)+)
  qed
  have real:
    "connect (\<A> \<eta>) (parallel_resource1_wiring \<rhd> res \<eta> \<parallel> real_resource \<eta>) =
     connect (?\<A> \<eta>) (real_resource \<eta>)" for \<eta>
    unfolding distinguish_attach[symmetric]
    by(simp add: attach_compose attach_converter_of_resource_conv_parallel_resource parallel_resource1_wiring_def)
  have "\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g ?\<A> \<eta> \<surd>" for \<eta> by(rule WT_intro)+
  moreover have "interaction_any_bounded_by (?\<A> \<eta>) (bound \<eta>)" for \<eta>
    by interaction_bound_converter simp
  moreover have "plossless_gpv (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (?\<A> \<eta>)" if lossless for \<eta> 
    by(rule plossless_intro WT_intro | simp add: that)+
  ultimately show "negligible (\<lambda>\<eta>. advantage (\<A> \<eta>) (sim \<eta> |\<^sub>= 1\<^sub>C \<rhd>
                        parallel_resource1_wiring \<rhd> res \<eta> \<parallel> ideal_resource \<eta>)
                       (parallel_resource1_wiring \<rhd> res \<eta> \<parallel> real_resource \<eta>))"
    unfolding advantage_def ideal real by(rule adv[unfolded advantage_def])
next
  from correct obtain cnv 
    where correct': "\<And>\<D>. \<lbrakk> \<And>\<eta>. \<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<D> \<eta> \<surd>;
          \<And>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (bound \<eta>);
          \<And>\<eta>. lossless \<Longrightarrow> plossless_gpv (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<D> \<eta>) \<rbrakk>
          \<Longrightarrow> (\<forall>\<eta>. wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w \<eta>)) \<and>
              negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (ideal_resource \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real_resource \<eta>))"
    by blast
  show "\<exists>cnv. \<forall>\<D>. (\<forall>\<eta>. \<I>_ideal \<eta> \<oplus>\<^sub>\<I> (\<I>_res \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) \<turnstile>g \<D> \<eta> \<surd>) \<longrightarrow>
        (\<forall>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (bound \<eta>)) \<longrightarrow>
        (\<forall>\<eta>. lossless \<longrightarrow> plossless_gpv (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> (\<I>_res \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>)) (\<D> \<eta>)) \<longrightarrow>
        (\<forall>\<eta>. wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w \<eta>)) \<and>
        negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (parallel_resource1_wiring \<rhd> res \<eta> \<parallel> ideal_resource \<eta>)
          (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> parallel_resource1_wiring \<rhd> res \<eta> \<parallel> real_resource \<eta>))"
  proof(intro exI conjI strip)
    fix \<D> :: "security \<Rightarrow> ('c + 'g + 'e, 'd + 'h + 'f) distinguisher"
    assume WT_D [rule_format, WT_intro]: "\<forall>\<eta>. \<I>_ideal \<eta> \<oplus>\<^sub>\<I> (\<I>_res \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) \<turnstile>g \<D> \<eta> \<surd>"
      and bound [rule_format, interaction_bound]: "\<forall>\<eta>. interaction_any_bounded_by (\<D> \<eta>) (bound \<eta>)"
      and lossless [rule_format, plossless_intro]: "\<forall>\<eta>. lossless \<longrightarrow> plossless_gpv (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> (\<I>_res \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>)) (\<D> \<eta>)"

    let ?\<D> = "\<lambda>\<eta>. absorb (\<D> \<eta>) (swap_lassocr \<odot> parallel_converter (converter_of_resource (res \<eta>)) 1\<^sub>C)"
    have WT': "\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g ?\<D> \<eta> \<surd>" for \<eta> by(rule WT_intro)+
    have bound': "interaction_any_bounded_by (?\<D> \<eta>) (bound \<eta>)" for \<eta> by interaction_bound simp
    have lossless': "plossless_gpv (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (?\<D> \<eta>)" if lossless for \<eta>
      by(rule plossless_intro WT_intro that)+
    from correct'[OF WT' bound' lossless']
    have w: "wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w \<eta>)" 
      and adv: "negligible (\<lambda>\<eta>. advantage (?\<D> \<eta>) (ideal_resource \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real_resource \<eta>))"
      for \<eta> by auto
    show  "wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (w \<eta>)" for \<eta> by(rule w)
    from w have [WT_intro]: "\<I>_ideal \<eta>, \<I>_real \<eta> \<turnstile>\<^sub>C cnv \<eta> \<surd>" for \<eta> by cases
    have "connect (\<D> \<eta>) (swap_lassocr \<rhd> res \<eta> \<parallel> (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real_resource \<eta>)) =
      connect (\<D> \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> swap_lassocr \<rhd> res \<eta> \<parallel> real_resource \<eta>)" for \<eta>
    proof -
      have "connect (\<D> \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> swap_lassocr \<rhd> res \<eta> \<parallel> real_resource \<eta>) =
        connect (\<D> \<eta>) (cnv \<eta> |\<^sub>= 1\<^sub>C |\<^sub>= 1\<^sub>C \<rhd> swap_lassocr \<rhd> res \<eta> \<parallel> real_resource \<eta>)"
        by(rule connect_eq_resource_cong[OF WT_D])                                                                
          (rule eq_\<I>_attach_on' WT_intro parallel_converter2_eq_\<I>_cong eq_\<I>_converter_reflI parallel_converter2_id_id[symmetric] | simp)+
      also have "\<dots> = connect (\<D> \<eta>) (swap_lassocr \<rhd> res \<eta> \<parallel> (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> real_resource \<eta>))"
        by(simp add: comp_swap_lassocr' attach_compose attach_parallel2)
      finally show ?thesis by simp
    qed
    with adv show "negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) (parallel_resource1_wiring \<rhd> res \<eta> \<parallel> ideal_resource \<eta>)
          (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> parallel_resource1_wiring \<rhd> res \<eta> \<parallel> real_resource \<eta>))"
      by(simp add: advantage_def distinguish_attach[symmetric] attach_compose attach_converter_of_resource_conv_parallel_resource parallel_resource1_wiring_def)
  qed
qed(rule WT_intro)+

end
