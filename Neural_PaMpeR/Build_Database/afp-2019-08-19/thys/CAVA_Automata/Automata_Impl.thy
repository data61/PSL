section \<open>Implementing Automata\<close>
(* Author: Peter Lammich *)
theory Automata_Impl
imports Digraph_Impl Automata
begin

subsection \<open>Indexed Generalized Buchi Graphs\<close>


consts
  i_igbg_eext :: "interface \<Rightarrow> interface \<Rightarrow> interface"

abbreviation "i_igbg Ie Iv \<equiv> \<langle>\<langle>Ie,Iv\<rangle>\<^sub>ii_igbg_eext,Iv\<rangle>\<^sub>ii_g_ext"

context begin interpretation autoref_syn .

lemma igbg_type[autoref_itype]:
  "igbg_num_acc ::\<^sub>i i_igbg Ie Iv \<rightarrow>\<^sub>i i_nat"
  "igbg_acc ::\<^sub>i i_igbg Ie Iv \<rightarrow>\<^sub>i Iv \<rightarrow>\<^sub>i \<langle>i_nat\<rangle>\<^sub>ii_set"
  "igb_graph_rec_ext
    ::\<^sub>i i_nat \<rightarrow>\<^sub>i (Iv \<rightarrow>\<^sub>i \<langle>i_nat\<rangle>\<^sub>ii_set) \<rightarrow>\<^sub>i Ie \<rightarrow>\<^sub>i \<langle>Ie,Iv\<rangle>\<^sub>ii_igbg_eext"
  by simp_all
end


record ('vi,'ei,'v0i,'acci) gen_igbg_impl = "('vi,'ei,'v0i) gen_g_impl" +
  igbgi_num_acc :: nat
  igbgi_acc :: 'acci

definition gen_igbg_impl_rel_eext_def_internal: 
  "gen_igbg_impl_rel_eext Rm Racc \<equiv> { (
  \<lparr> igbgi_num_acc = num_acci, igbgi_acc = acci, \<dots>=mi \<rparr>, 
  \<lparr> igbg_num_acc = num_acc, igbg_acc = acc, \<dots>=m \<rparr>) 
  | num_acci acci mi num_acc acc m. 
    (num_acci,num_acc)\<in>nat_rel 
  \<and> (acci,acc)\<in>Racc
  \<and> (mi,m)\<in>Rm
  }"

lemma gen_igbg_impl_rel_eext_def: 
  "\<langle>Rm,Racc\<rangle>gen_igbg_impl_rel_eext = { (
  \<lparr> igbgi_num_acc = num_acci, igbgi_acc = acci, \<dots>=mi \<rparr>, 
  \<lparr> igbg_num_acc = num_acc, igbg_acc = acc, \<dots>=m \<rparr>) 
  | num_acci acci mi num_acc acc m. 
    (num_acci,num_acc)\<in>nat_rel 
  \<and> (acci,acc)\<in>Racc
  \<and> (mi,m)\<in>Rm
  }"
  unfolding gen_igbg_impl_rel_eext_def_internal relAPP_def by simp

lemma gen_igbg_impl_rel_sv[relator_props]: 
  "\<lbrakk>single_valued Racc; single_valued Rm\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rm,Racc\<rangle>gen_igbg_impl_rel_eext)"
  unfolding gen_igbg_impl_rel_eext_def
  apply (rule single_valuedI)
  apply (clarsimp)
  apply (intro conjI)
  apply (rule single_valuedD[rotated], assumption+)
  apply (rule single_valuedD[rotated], assumption+)
  done

abbreviation gen_igbg_impl_rel_ext 
  :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (_\<times>(_,_)igb_graph_rec_scheme) set"
  where "gen_igbg_impl_rel_ext Rm Racc 
  \<equiv> \<langle>\<langle>Rm,Racc\<rangle>gen_igbg_impl_rel_eext\<rangle>gen_g_impl_rel_ext "

lemma gen_igbg_refine:
  fixes Rv Re Rv0 Racc
  assumes "TERM (Rv,Re,Rv0)"
  assumes "TERM (Racc)"
  shows
  "(igbgi_num_acc,igbg_num_acc) 
    \<in> \<langle>Rv,Re,Rv0\<rangle>gen_igbg_impl_rel_ext Rm Racc \<rightarrow> nat_rel"
  "(igbgi_acc,igbg_acc) 
    \<in> \<langle>Rv,Re,Rv0\<rangle>gen_igbg_impl_rel_ext Rm Racc \<rightarrow> Racc"
  "(gen_igbg_impl_ext, igb_graph_rec_ext) 
    \<in> nat_rel \<rightarrow> Racc \<rightarrow> Rm \<rightarrow> \<langle>Rm,Racc\<rangle>gen_igbg_impl_rel_eext"
  unfolding gen_igbg_impl_rel_eext_def gen_g_impl_rel_ext_def
  by auto

subsubsection \<open>Implementation with bit-set\<close>

definition igbg_impl_rel_eext_internal_def: 
  "igbg_impl_rel_eext Rm Rv \<equiv> \<langle>Rm, Rv \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel\<rangle>gen_igbg_impl_rel_eext"

lemma igbg_impl_rel_eext_def: 
  "\<langle>Rm,Rv\<rangle>igbg_impl_rel_eext \<equiv> \<langle>Rm, Rv \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel\<rangle>gen_igbg_impl_rel_eext"
  unfolding igbg_impl_rel_eext_internal_def relAPP_def by simp

lemmas [autoref_rel_intf] = REL_INTFI[of igbg_impl_rel_eext i_igbg_eext]

lemma [relator_props, simp]: 
  "\<lbrakk>Range Rv = UNIV; single_valued Rm\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rm,Rv\<rangle>igbg_impl_rel_eext)"
  unfolding igbg_impl_rel_eext_def by tagged_solver

lemma g_tag: "TERM (\<langle>Rv\<rangle>fun_set_rel,\<langle>Rv\<rangle>slg_rel,\<langle>Rv\<rangle>list_set_rel)" .
lemma frgv_tag: "TERM (\<langle>Rv\<rangle>list_set_rel,\<langle>Rv\<rangle>slg_rel,\<langle>Rv\<rangle>list_set_rel)" .
lemma igbg_bs_tag: "TERM (Rv \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel)" .

abbreviation "igbgv_impl_rel_ext Rm Rv 
  \<equiv> \<langle>\<langle>Rm, Rv\<rangle>igbg_impl_rel_eext, Rv\<rangle>frgv_impl_rel_ext"

abbreviation "igbg_impl_rel_ext Rm Rv 
  \<equiv> \<langle>\<langle>Rm, Rv\<rangle>igbg_impl_rel_eext, Rv\<rangle>g_impl_rel_ext"

type_synonym ('v,'m) igbgv_impl_scheme = 
  "('v, \<lparr> igbgi_num_acc::nat, igbgi_acc::'v\<Rightarrow>integer, \<dots>::'m  \<rparr>) 
    frgv_impl_scheme"
type_synonym ('v,'m) igbg_impl_scheme = 
  "('v, \<lparr> igbgi_num_acc::nat, igbgi_acc::'v\<Rightarrow>integer, \<dots>::'m  \<rparr>) 
    g_impl_scheme"

context fixes Rv :: "('vi\<times>'v) set" begin
lemmas [autoref_rules] = gen_igbg_refine[
  OF frgv_tag[of Rv] igbg_bs_tag[of Rv], 
  folded frgv_impl_rel_ext_def igbg_impl_rel_eext_def]

lemmas [autoref_rules] = gen_igbg_refine[
  OF g_tag[of Rv] igbg_bs_tag[of Rv], 
  folded g_impl_rel_ext_def igbg_impl_rel_eext_def]
end



schematic_goal "(?c::?'c, 
    \<lambda>G x. if igbg_num_acc G = 0 \<and> 1\<in>igbg_acc G x then (g_E G `` {x}) else {} 
  )\<in>?R"
  apply (autoref (keep_goal))
  done


schematic_goal "(?c, 
  \<lambda>V0 E num_acc acc. 
    \<lparr> g_V = UNIV, g_E = E, g_V0 = V0, igbg_num_acc = num_acc, igbg_acc = acc \<rparr>
  )\<in>\<langle>R\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>slg_rel \<rightarrow> nat_rel \<rightarrow> (R \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel) 
    \<rightarrow> igbg_impl_rel_ext unit_rel R"
  apply (autoref (keep_goal))
  done

schematic_goal "(?c, 
  \<lambda>V0 E num_acc acc. 
    \<lparr> g_V = {}, g_E = E, g_V0 = V0, igbg_num_acc = num_acc, igbg_acc = acc \<rparr>
  )\<in>\<langle>R\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>slg_rel \<rightarrow> nat_rel \<rightarrow> (R \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel) 
    \<rightarrow> igbgv_impl_rel_ext unit_rel R"
  apply (autoref (keep_goal))
  done

subsection \<open>Indexed Generalized Buchi Automata\<close>

consts
  i_igba_eext :: "interface \<Rightarrow> interface \<Rightarrow> interface \<Rightarrow> interface"

abbreviation "i_igba Ie Iv Il 
  \<equiv> \<langle>\<langle>\<langle>Ie,Iv,Il\<rangle>\<^sub>ii_igba_eext,Iv\<rangle>\<^sub>ii_igbg_eext,Iv\<rangle>\<^sub>ii_g_ext"
context begin interpretation autoref_syn .

lemma igba_type[autoref_itype]:
  "igba_L ::\<^sub>i i_igba Ie Iv Il \<rightarrow>\<^sub>i (Iv \<rightarrow>\<^sub>i Il \<rightarrow>\<^sub>i i_bool)"
  "igba_rec_ext ::\<^sub>i (Iv \<rightarrow>\<^sub>i Il \<rightarrow>\<^sub>i i_bool) \<rightarrow>\<^sub>i Ie \<rightarrow>\<^sub>i \<langle>Ie,Iv,Il\<rangle>\<^sub>ii_igba_eext"
  by simp_all
end


record ('vi,'ei,'v0i,'acci,'Li) gen_igba_impl = 
  "('vi,'ei,'v0i,'acci)gen_igbg_impl" +
  igbai_L :: "'Li"

definition gen_igba_impl_rel_eext_def_internal: 
  "gen_igba_impl_rel_eext Rm Rl  \<equiv> { (
  \<lparr> igbai_L = Li, \<dots>=mi \<rparr>, 
  \<lparr> igba_L = L, \<dots>=m \<rparr>) 
  | Li mi L m. 
    (Li,L)\<in>Rl
  \<and> (mi,m)\<in>Rm
  }"

lemma gen_igba_impl_rel_eext_def: 
  "\<langle>Rm,Rl\<rangle>gen_igba_impl_rel_eext = { (
  \<lparr> igbai_L = Li, \<dots>=mi \<rparr>, 
  \<lparr> igba_L = L, \<dots>=m \<rparr>) 
  | Li mi L m. 
    (Li,L)\<in>Rl
  \<and> (mi,m)\<in>Rm
  }"
  unfolding gen_igba_impl_rel_eext_def_internal relAPP_def by simp

lemma gen_igba_impl_rel_sv[relator_props]: 
  "\<lbrakk>single_valued Rl; single_valued Rm\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rm,Rl\<rangle>gen_igba_impl_rel_eext)"
  unfolding gen_igba_impl_rel_eext_def
  apply (rule single_valuedI)
  apply (clarsimp)
  apply (intro conjI)
  apply (rule single_valuedD[rotated], assumption+)
  apply (rule single_valuedD[rotated], assumption+)
  done

abbreviation gen_igba_impl_rel_ext 
  :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (_ \<times> ('a,'b,'c) igba_rec_scheme) set"
  where "gen_igba_impl_rel_ext Rm Rl 
    \<equiv> gen_igbg_impl_rel_ext (\<langle>Rm,Rl\<rangle>gen_igba_impl_rel_eext)"

lemma gen_igba_refine:
  fixes Rv Re Rv0 Racc Rl
  assumes "TERM (Rv,Re,Rv0)"
  assumes "TERM (Racc)"
  assumes "TERM (Rl)"
  shows
  "(igbai_L,igba_L) 
    \<in> \<langle>Rv,Re,Rv0\<rangle>gen_igba_impl_rel_ext Rm Rl Racc \<rightarrow> Rl"
  "(gen_igba_impl_ext, igba_rec_ext) 
    \<in> Rl \<rightarrow> Rm \<rightarrow> \<langle>Rm,Rl\<rangle>gen_igba_impl_rel_eext"
  unfolding gen_igba_impl_rel_eext_def gen_igbg_impl_rel_eext_def
    gen_g_impl_rel_ext_def
  by auto

subsubsection \<open>Implementation as function\<close>
definition igba_impl_rel_eext_internal_def: 
  "igba_impl_rel_eext Rm Rv Rl \<equiv> \<langle>Rm, Rv \<rightarrow> Rl \<rightarrow> bool_rel\<rangle>gen_igba_impl_rel_eext"

lemma igba_impl_rel_eext_def: 
  "\<langle>Rm,Rv,Rl\<rangle>igba_impl_rel_eext \<equiv> \<langle>Rm, Rv \<rightarrow> Rl \<rightarrow> bool_rel\<rangle>gen_igba_impl_rel_eext"
  unfolding igba_impl_rel_eext_internal_def relAPP_def by simp

lemmas [autoref_rel_intf] = REL_INTFI[of igba_impl_rel_eext i_igba_eext]

lemma [relator_props, simp]: 
  "\<lbrakk>Range Rv = UNIV; single_valued Rm; Range Rl = UNIV\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rm,Rv,Rl\<rangle>igba_impl_rel_eext)"
  unfolding igba_impl_rel_eext_def by tagged_solver

lemma igba_f_tag: "TERM (Rv \<rightarrow> Rl \<rightarrow> bool_rel)" .

abbreviation "igbav_impl_rel_ext Rm Rv Rl
  \<equiv> igbgv_impl_rel_ext (\<langle>Rm, Rv, Rl\<rangle>igba_impl_rel_eext) Rv"

abbreviation "igba_impl_rel_ext Rm Rv Rl 
  \<equiv> igbg_impl_rel_ext (\<langle>Rm, Rv, Rl\<rangle>igba_impl_rel_eext) Rv"

type_synonym ('v,'l,'m) igbav_impl_scheme = 
  "('v, \<lparr> igbai_L :: 'v \<Rightarrow> 'l \<Rightarrow> bool , \<dots>::'m  \<rparr>) 
    igbgv_impl_scheme"

type_synonym ('v,'l,'m) igba_impl_scheme = 
  "('v, \<lparr> igbai_L :: 'v \<Rightarrow> 'l \<Rightarrow> bool , \<dots>::'m  \<rparr>) 
    igbg_impl_scheme"

context 
  fixes Rv :: "('vi\<times>'v) set" 
  fixes Rl :: "('Li\<times>'l) set"
begin
lemmas [autoref_rules] = gen_igba_refine[
  OF frgv_tag[of Rv] igbg_bs_tag[of Rv] igba_f_tag[of Rv Rl], 
  folded frgv_impl_rel_ext_def igbg_impl_rel_eext_def igba_impl_rel_eext_def]

lemmas [autoref_rules] = gen_igba_refine[
  OF g_tag[of Rv] igbg_bs_tag[of Rv] igba_f_tag[of Rv Rl], 
  folded g_impl_rel_ext_def igbg_impl_rel_eext_def igba_impl_rel_eext_def]
end

thm autoref_itype

schematic_goal 
  "(?c::?'c, \<lambda>G x l. if igba_L G x l then (g_E G `` {x}) else {} )\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal 
  notes [autoref_tyrel] = TYRELI[of "Id :: ('a\<times>'a) set"]
  shows "(?c::?'c, \<lambda>E (V0::'a set) num_acc acc L. 
  \<lparr> g_V = UNIV, g_E = E, g_V0 = V0, 
    igbg_num_acc = num_acc, igbg_acc = acc, igba_L = L \<rparr>
  )\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal 
  notes [autoref_tyrel] = TYRELI[of "Id :: ('a\<times>'a) set"]
  shows "(?c::?'c, \<lambda>E (V0::'a set) num_acc acc L. 
  \<lparr> g_V = V0, g_E = E, g_V0 = V0, 
    igbg_num_acc = num_acc, igbg_acc = acc, igba_L = L \<rparr>
  )\<in>?R"
  apply (autoref (keep_goal))
  done

subsection \<open>Generalized Buchi Graphs\<close>

consts
  i_gbg_eext :: "interface \<Rightarrow> interface \<Rightarrow> interface"

abbreviation "i_gbg Ie Iv \<equiv> \<langle>\<langle>Ie,Iv\<rangle>\<^sub>ii_gbg_eext,Iv\<rangle>\<^sub>ii_g_ext"

context begin interpretation autoref_syn .

lemma gbg_type[autoref_itype]:
  "gbg_F ::\<^sub>i i_gbg Ie Iv \<rightarrow>\<^sub>i \<langle>\<langle>Iv\<rangle>\<^sub>ii_set\<rangle>\<^sub>ii_set"
  "gb_graph_rec_ext ::\<^sub>i \<langle>\<langle>Iv\<rangle>\<^sub>ii_set\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i Ie \<rightarrow>\<^sub>i \<langle>Ie,Iv\<rangle>\<^sub>ii_gbg_eext"
  by simp_all
end

record ('vi,'ei,'v0i,'fi) gen_gbg_impl = "('vi,'ei,'v0i) gen_g_impl" +
  gbgi_F :: 'fi

definition gen_gbg_impl_rel_eext_def_internal: 
  "gen_gbg_impl_rel_eext Rm Rf \<equiv> { (
  \<lparr> gbgi_F = Fi, \<dots>=mi \<rparr>, 
  \<lparr> gbg_F = F, \<dots>=m \<rparr>) 
  | Fi mi F m. 
    (Fi,F)\<in>Rf
  \<and> (mi,m)\<in>Rm
  }"

lemma gen_gbg_impl_rel_eext_def: 
  "\<langle>Rm,Rf\<rangle>gen_gbg_impl_rel_eext = { (
  \<lparr> gbgi_F = Fi, \<dots>=mi \<rparr>, 
  \<lparr> gbg_F = F, \<dots>=m \<rparr>) 
  | Fi mi F m. 
    (Fi,F)\<in>Rf
  \<and> (mi,m)\<in>Rm
  }"
  unfolding gen_gbg_impl_rel_eext_def_internal relAPP_def by simp

lemma gen_gbg_impl_rel_sv[relator_props]: 
  "\<lbrakk>single_valued Rm; single_valued Rf\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rm,Rf\<rangle>gen_gbg_impl_rel_eext)"
  unfolding gen_gbg_impl_rel_eext_def
  apply (rule single_valuedI)
  apply (clarsimp)
  apply (intro conjI)
  apply (rule single_valuedD[rotated], assumption+)
  apply (rule single_valuedD[rotated], assumption+)
  done

abbreviation gen_gbg_impl_rel_ext 
  :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (_ \<times> ('q,_) gb_graph_rec_scheme) set"
  where "gen_gbg_impl_rel_ext Rm Rf 
  \<equiv> \<langle>\<langle>Rm,Rf\<rangle>gen_gbg_impl_rel_eext\<rangle>gen_g_impl_rel_ext"

lemma gen_gbg_refine:
  fixes Rv Re Rv0 Rf
  assumes "TERM (Rv,Re,Rv0)"
  assumes "TERM (Rf)"
  shows
  "(gbgi_F,gbg_F) 
    \<in> \<langle>Rv,Re,Rv0\<rangle>gen_gbg_impl_rel_ext Rm Rf \<rightarrow> Rf"
  "(gen_gbg_impl_ext, gb_graph_rec_ext) 
    \<in> Rf \<rightarrow> Rm \<rightarrow> \<langle>Rm,Rf\<rangle>gen_gbg_impl_rel_eext"
  unfolding gen_gbg_impl_rel_eext_def gen_g_impl_rel_ext_def
  by auto

subsubsection \<open>Implementation with list of lists\<close>

definition gbg_impl_rel_eext_internal_def: 
  "gbg_impl_rel_eext Rm Rv 
  \<equiv> \<langle>Rm, \<langle>\<langle>Rv\<rangle>list_set_rel\<rangle>list_set_rel\<rangle>gen_gbg_impl_rel_eext"

lemma gbg_impl_rel_eext_def: 
  "\<langle>Rm,Rv\<rangle>gbg_impl_rel_eext 
    \<equiv> \<langle>Rm, \<langle>\<langle>Rv\<rangle>list_set_rel\<rangle>list_set_rel\<rangle>gen_gbg_impl_rel_eext"
  unfolding gbg_impl_rel_eext_internal_def relAPP_def by simp

lemmas [autoref_rel_intf] = REL_INTFI[of gbg_impl_rel_eext i_gbg_eext]

lemma [relator_props, simp]: 
  "\<lbrakk>single_valued Rm; single_valued Rv\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rm,Rv\<rangle>gbg_impl_rel_eext)"
  unfolding gbg_impl_rel_eext_def by tagged_solver

lemma gbg_ls_tag: "TERM (\<langle>\<langle>Rv\<rangle>list_set_rel\<rangle>list_set_rel)" .

abbreviation "gbgv_impl_rel_ext Rm Rv 
  \<equiv> \<langle>\<langle>Rm, Rv\<rangle>gbg_impl_rel_eext, Rv\<rangle>frgv_impl_rel_ext"

abbreviation "gbg_impl_rel_ext Rm Rv 
  \<equiv> \<langle>\<langle>Rm, Rv\<rangle>gbg_impl_rel_eext, Rv\<rangle>g_impl_rel_ext"

context fixes Rv :: "('vi\<times>'v) set" begin
lemmas [autoref_rules] = gen_gbg_refine[
  OF frgv_tag[of Rv] gbg_ls_tag[of Rv], 
  folded frgv_impl_rel_ext_def gbg_impl_rel_eext_def]

lemmas [autoref_rules] = gen_gbg_refine[
  OF g_tag[of Rv] gbg_ls_tag[of Rv], 
  folded g_impl_rel_ext_def gbg_impl_rel_eext_def]
end

schematic_goal "(?c::?'c, 
    \<lambda>G x. if gbg_F G = {} then (g_E G `` {x}) else {} 
  )\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal 
  notes [autoref_tyrel] = TYRELI[of "Id :: ('a\<times>'a) set"]
  shows "(?c::?'c, \<lambda>E (V0::'a set) F. 
    \<lparr> g_V = {}, g_E = E, g_V0 = V0, gbg_F = F \<rparr>)\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal 
  notes [autoref_tyrel] = TYRELI[of "Id :: ('a\<times>'a) set"]
  shows "(?c::?'c, \<lambda>E (V0::'a set) F. 
    \<lparr> g_V = UNIV, g_E = E, g_V0 = V0, gbg_F = insert {} F \<rparr>)\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal "(?c::?'c, it_to_sorted_list (\<lambda>_ _. True) {1,2::nat} )\<in>?R"
  apply (autoref (keep_goal))
  done

subsection \<open>GBAs\<close>

consts
  i_gba_eext :: "interface \<Rightarrow> interface \<Rightarrow> interface \<Rightarrow> interface"

abbreviation "i_gba Ie Iv Il 
  \<equiv> \<langle>\<langle>\<langle>Ie,Iv,Il\<rangle>\<^sub>ii_gba_eext,Iv\<rangle>\<^sub>ii_gbg_eext,Iv\<rangle>\<^sub>ii_g_ext"
context begin interpretation autoref_syn .

lemma gba_type[autoref_itype]:
  "gba_L ::\<^sub>i i_gba Ie Iv Il \<rightarrow>\<^sub>i (Iv \<rightarrow>\<^sub>i Il \<rightarrow>\<^sub>i i_bool)"
  "gba_rec_ext ::\<^sub>i (Iv \<rightarrow>\<^sub>i Il \<rightarrow>\<^sub>i i_bool) \<rightarrow>\<^sub>i Ie \<rightarrow>\<^sub>i \<langle>Ie,Iv,Il\<rangle>\<^sub>ii_gba_eext"
  by simp_all
end

record ('vi,'ei,'v0i,'acci,'Li) gen_gba_impl = 
  "('vi,'ei,'v0i,'acci)gen_gbg_impl" +
  gbai_L :: "'Li"

definition gen_gba_impl_rel_eext_def_internal: 
  "gen_gba_impl_rel_eext Rm Rl  \<equiv> { (
  \<lparr> gbai_L = Li, \<dots>=mi \<rparr>, 
  \<lparr> gba_L = L, \<dots>=m \<rparr>) 
  | Li mi L m. 
    (Li,L)\<in>Rl
  \<and> (mi,m)\<in>Rm
  }"

lemma gen_gba_impl_rel_eext_def: 
  "\<langle>Rm,Rl\<rangle>gen_gba_impl_rel_eext = { (
  \<lparr> gbai_L = Li, \<dots>=mi \<rparr>, 
  \<lparr> gba_L = L, \<dots>=m \<rparr>) 
  | Li mi L m. 
    (Li,L)\<in>Rl
  \<and> (mi,m)\<in>Rm
  }"
  unfolding gen_gba_impl_rel_eext_def_internal relAPP_def by simp

lemma gen_gba_impl_rel_sv[relator_props]: 
  "\<lbrakk>single_valued Rl; single_valued Rm\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rm,Rl\<rangle>gen_gba_impl_rel_eext)"
  unfolding gen_gba_impl_rel_eext_def
  apply (rule single_valuedI)
  apply (clarsimp)
  apply (intro conjI)
  apply (rule single_valuedD[rotated], assumption+)
  apply (rule single_valuedD[rotated], assumption+)
  done

abbreviation gen_gba_impl_rel_ext 
  :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (_ \<times> ('a,'b,'c) gba_rec_scheme) set"
  where "gen_gba_impl_rel_ext Rm Rl 
    \<equiv> gen_gbg_impl_rel_ext (\<langle>Rm,Rl\<rangle>gen_gba_impl_rel_eext)"

lemma gen_gba_refine:
  fixes Rv Re Rv0 Racc Rl
  assumes "TERM (Rv,Re,Rv0)"
  assumes "TERM (Racc)"
  assumes "TERM (Rl)"
  shows
  "(gbai_L,gba_L) 
    \<in> \<langle>Rv,Re,Rv0\<rangle>gen_gba_impl_rel_ext Rm Rl Racc \<rightarrow> Rl"
  "(gen_gba_impl_ext, gba_rec_ext) 
    \<in> Rl \<rightarrow> Rm \<rightarrow> \<langle>Rm,Rl\<rangle>gen_gba_impl_rel_eext"
  unfolding gen_gba_impl_rel_eext_def gen_gbg_impl_rel_eext_def
    gen_g_impl_rel_ext_def
  by auto

subsubsection \<open>Implementation as function\<close>
definition gba_impl_rel_eext_internal_def: 
  "gba_impl_rel_eext Rm Rv Rl \<equiv> \<langle>Rm, Rv \<rightarrow> Rl \<rightarrow> bool_rel\<rangle>gen_gba_impl_rel_eext"

lemma gba_impl_rel_eext_def: 
  "\<langle>Rm,Rv,Rl\<rangle>gba_impl_rel_eext \<equiv> \<langle>Rm, Rv \<rightarrow> Rl \<rightarrow> bool_rel\<rangle>gen_gba_impl_rel_eext"
  unfolding gba_impl_rel_eext_internal_def relAPP_def by simp

lemmas [autoref_rel_intf] = REL_INTFI[of gba_impl_rel_eext i_gba_eext]

lemma [relator_props, simp]: 
  "\<lbrakk>Range Rv = UNIV; single_valued Rm; Range Rl = UNIV\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rm,Rv,Rl\<rangle>gba_impl_rel_eext)"
  unfolding gba_impl_rel_eext_def by tagged_solver

lemma gba_f_tag: "TERM (Rv \<rightarrow> Rl \<rightarrow> bool_rel)" .

abbreviation "gbav_impl_rel_ext Rm Rv Rl
  \<equiv> gbgv_impl_rel_ext (\<langle>Rm, Rv, Rl\<rangle>gba_impl_rel_eext) Rv"

abbreviation "gba_impl_rel_ext Rm Rv Rl 
  \<equiv> gbg_impl_rel_ext (\<langle>Rm, Rv, Rl\<rangle>gba_impl_rel_eext) Rv"

context 
  fixes Rv :: "('vi\<times>'v) set" 
  fixes Rl :: "('Li\<times>'l) set"
begin
lemmas [autoref_rules] = gen_gba_refine[
  OF frgv_tag[of Rv] gbg_ls_tag[of Rv] gba_f_tag[of Rv Rl], 
  folded frgv_impl_rel_ext_def gbg_impl_rel_eext_def gba_impl_rel_eext_def]

lemmas [autoref_rules] = gen_gba_refine[
  OF g_tag[of Rv] gbg_ls_tag[of Rv] gba_f_tag[of Rv Rl], 
  folded g_impl_rel_ext_def gbg_impl_rel_eext_def gba_impl_rel_eext_def]
end

thm autoref_itype

schematic_goal 
  "(?c::?'c, \<lambda>G x l. if gba_L G x l then (g_E G `` {x}) else {} )\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal 
  notes [autoref_tyrel] = TYRELI[of "Id :: ('a\<times>'a) set"]
  shows "(?c::?'c, \<lambda>E (V0::'a set) F L. 
  \<lparr> g_V = UNIV, g_E = E, g_V0 = V0, 
    gbg_F = F, gba_L = L \<rparr>
  )\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal 
  notes [autoref_tyrel] = TYRELI[of "Id :: ('a\<times>'a) set"]
  shows "(?c::?'c, \<lambda>E (V0::'a set) F L. 
  \<lparr> g_V = V0, g_E = E, g_V0 = V0, 
    gbg_F = F, gba_L = L \<rparr>
  )\<in>?R"
  apply (autoref (keep_goal))
  done

subsection \<open>Buchi Graphs\<close>

consts
  i_bg_eext :: "interface \<Rightarrow> interface \<Rightarrow> interface"

abbreviation "i_bg Ie Iv \<equiv> \<langle>\<langle>Ie,Iv\<rangle>\<^sub>ii_bg_eext,Iv\<rangle>\<^sub>ii_g_ext"

context begin interpretation autoref_syn .
lemma bg_type[autoref_itype]:
  "bg_F ::\<^sub>i i_bg Ie Iv \<rightarrow>\<^sub>i \<langle>Iv\<rangle>\<^sub>ii_set"
  "gb_graph_rec_ext ::\<^sub>i \<langle>\<langle>Iv\<rangle>\<^sub>ii_set\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i Ie \<rightarrow>\<^sub>i \<langle>Ie,Iv\<rangle>\<^sub>ii_bg_eext"
  by simp_all
end

record ('vi,'ei,'v0i,'fi) gen_bg_impl = "('vi,'ei,'v0i) gen_g_impl" +
  bgi_F :: 'fi

definition gen_bg_impl_rel_eext_def_internal: 
  "gen_bg_impl_rel_eext Rm Rf \<equiv> { (
  \<lparr> bgi_F = Fi, \<dots>=mi \<rparr>, 
  \<lparr> bg_F = F, \<dots>=m \<rparr>) 
  | Fi mi F m. 
    (Fi,F)\<in>Rf
  \<and> (mi,m)\<in>Rm
  }"

lemma gen_bg_impl_rel_eext_def: 
  "\<langle>Rm,Rf\<rangle>gen_bg_impl_rel_eext = { (
  \<lparr> bgi_F = Fi, \<dots>=mi \<rparr>, 
  \<lparr> bg_F = F, \<dots>=m \<rparr>) 
  | Fi mi F m. 
    (Fi,F)\<in>Rf
  \<and> (mi,m)\<in>Rm
  }"
  unfolding gen_bg_impl_rel_eext_def_internal relAPP_def by simp

lemma gen_bg_impl_rel_sv[relator_props]: 
  "\<lbrakk>single_valued Rm; single_valued Rf\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rm,Rf\<rangle>gen_bg_impl_rel_eext)"
  unfolding gen_bg_impl_rel_eext_def
  apply (rule single_valuedI)
  apply (clarsimp)
  apply (intro conjI)
  apply (rule single_valuedD[rotated], assumption+)
  apply (rule single_valuedD[rotated], assumption+)
  done

abbreviation gen_bg_impl_rel_ext 
  :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (_ \<times> ('q,_) b_graph_rec_scheme) set"
  where "gen_bg_impl_rel_ext Rm Rf 
  \<equiv> \<langle>\<langle>Rm,Rf\<rangle>gen_bg_impl_rel_eext\<rangle>gen_g_impl_rel_ext"

lemma gen_bg_refine:
  fixes Rv Re Rv0 Rf
  assumes "TERM (Rv,Re,Rv0)"
  assumes "TERM (Rf)"
  shows
  "(bgi_F,bg_F) 
    \<in> \<langle>Rv,Re,Rv0\<rangle>gen_bg_impl_rel_ext Rm Rf \<rightarrow> Rf"
  "(gen_bg_impl_ext, b_graph_rec_ext) 
    \<in> Rf \<rightarrow> Rm \<rightarrow> \<langle>Rm,Rf\<rangle>gen_bg_impl_rel_eext"
  unfolding gen_bg_impl_rel_eext_def gen_g_impl_rel_ext_def
  by auto

subsubsection \<open>Implementation with Characteristic Functions\<close>

definition bg_impl_rel_eext_internal_def: 
  "bg_impl_rel_eext Rm Rv 
  \<equiv> \<langle>Rm, \<langle>Rv\<rangle>fun_set_rel\<rangle>gen_bg_impl_rel_eext"

lemma bg_impl_rel_eext_def: 
  "\<langle>Rm,Rv\<rangle>bg_impl_rel_eext 
    \<equiv> \<langle>Rm, \<langle>Rv\<rangle>fun_set_rel\<rangle>gen_bg_impl_rel_eext"
  unfolding bg_impl_rel_eext_internal_def relAPP_def by simp

lemmas [autoref_rel_intf] = REL_INTFI[of bg_impl_rel_eext i_bg_eext]

lemma [relator_props, simp]: 
  "\<lbrakk>single_valued Rm; single_valued Rv; Range Rv = UNIV\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rm,Rv\<rangle>bg_impl_rel_eext)"
  unfolding bg_impl_rel_eext_def by tagged_solver

lemma bg_fs_tag: "TERM (\<langle>Rv\<rangle>fun_set_rel)" .

abbreviation "bgv_impl_rel_ext Rm Rv 
  \<equiv> \<langle>\<langle>Rm, Rv\<rangle>bg_impl_rel_eext, Rv\<rangle>frgv_impl_rel_ext"

abbreviation "bg_impl_rel_ext Rm Rv 
  \<equiv> \<langle>\<langle>Rm, Rv\<rangle>bg_impl_rel_eext, Rv\<rangle>g_impl_rel_ext"

context fixes Rv :: "('vi\<times>'v) set" begin
lemmas [autoref_rules] = gen_bg_refine[
  OF frgv_tag[of Rv] bg_fs_tag[of Rv], 
  folded frgv_impl_rel_ext_def bg_impl_rel_eext_def]

lemmas [autoref_rules] = gen_bg_refine[
  OF g_tag[of Rv] bg_fs_tag[of Rv], 
  folded g_impl_rel_ext_def bg_impl_rel_eext_def]
end

schematic_goal "(?c::?'c, 
    \<lambda>G x. if x \<in> bg_F G then (g_E G `` {x}) else {} 
  )\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal 
  notes [autoref_tyrel] = TYRELI[of "Id :: ('a\<times>'a) set"]
  shows "(?c::?'c, \<lambda>E (V0::'a set) F. 
    \<lparr> g_V = {}, g_E = E, g_V0 = V0, bg_F = F \<rparr>)\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal 
  notes [autoref_tyrel] = TYRELI[of "Id :: ('a\<times>'a) set"]
  shows "(?c::?'c, \<lambda>E (V0::'a set) F. 
    \<lparr> g_V = UNIV, g_E = E, g_V0 = V0, bg_F = F \<rparr>)\<in>?R"
  apply (autoref (keep_goal))
  done

subsection \<open>System Automata\<close>

consts
  i_sa_eext :: "interface \<Rightarrow> interface \<Rightarrow> interface \<Rightarrow> interface"

abbreviation "i_sa Ie Iv Il \<equiv> \<langle>\<langle>Ie,Iv,Il\<rangle>\<^sub>ii_sa_eext,Iv\<rangle>\<^sub>ii_g_ext"

context begin interpretation autoref_syn .
term sa_L
lemma sa_type[autoref_itype]:
  "sa_L ::\<^sub>i i_sa Ie Iv Il \<rightarrow>\<^sub>i Iv \<rightarrow>\<^sub>i Il"
  "sa_rec_ext ::\<^sub>i (Iv \<rightarrow>\<^sub>i Il) \<rightarrow>\<^sub>i Ie \<rightarrow>\<^sub>i \<langle>Ie,Iv,Il\<rangle>\<^sub>ii_sa_eext"
  by simp_all
end

record ('vi,'ei,'v0i,'li) gen_sa_impl = "('vi,'ei,'v0i) gen_g_impl" +
  sai_L :: 'li

definition gen_sa_impl_rel_eext_def_internal: 
  "gen_sa_impl_rel_eext Rm Rl \<equiv> { (
  \<lparr> sai_L = Li, \<dots>=mi \<rparr>, 
  \<lparr> sa_L = L, \<dots>=m \<rparr>) 
  | Li mi L m. 
    (Li,L)\<in>Rl
  \<and> (mi,m)\<in>Rm
  }"

lemma gen_sa_impl_rel_eext_def: 
  "\<langle>Rm,Rl\<rangle>gen_sa_impl_rel_eext = { (
  \<lparr> sai_L = Li, \<dots>=mi \<rparr>, 
  \<lparr> sa_L = L, \<dots>=m \<rparr>) 
  | Li mi L m. 
    (Li,L)\<in>Rl
  \<and> (mi,m)\<in>Rm
  }"
  unfolding gen_sa_impl_rel_eext_def_internal relAPP_def by simp

lemma gen_sa_impl_rel_sv[relator_props]: 
  "\<lbrakk>single_valued Rm; single_valued Rf\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rm,Rf\<rangle>gen_sa_impl_rel_eext)"
  unfolding gen_sa_impl_rel_eext_def
  apply (rule single_valuedI)
  apply (clarsimp)
  apply (intro conjI)
  apply (rule single_valuedD[rotated], assumption+)
  apply (rule single_valuedD[rotated], assumption+)
  done

abbreviation gen_sa_impl_rel_ext 
  :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (_ \<times> ('q,'l,_) sa_rec_scheme) set"
  where "gen_sa_impl_rel_ext Rm Rf 
  \<equiv> \<langle>\<langle>Rm,Rf\<rangle>gen_sa_impl_rel_eext\<rangle>gen_g_impl_rel_ext"

lemma gen_sa_refine:
  fixes Rv Re Rv0
  assumes "TERM (Rv,Re,Rv0)"
  assumes "TERM (Rl)"
  shows
  "(sai_L,sa_L) 
    \<in> \<langle>Rv,Re,Rv0\<rangle>gen_sa_impl_rel_ext Rm Rl \<rightarrow> Rl"
  "(gen_sa_impl_ext, sa_rec_ext) 
    \<in> Rl \<rightarrow> Rm \<rightarrow> \<langle>Rm,Rl\<rangle>gen_sa_impl_rel_eext"
  unfolding gen_sa_impl_rel_eext_def gen_g_impl_rel_ext_def
  by auto

subsubsection \<open>Implementation with Function\<close>

definition sa_impl_rel_eext_internal_def: 
  "sa_impl_rel_eext Rm Rv Rl
  \<equiv> \<langle>Rm, Rv\<rightarrow>Rl\<rangle>gen_sa_impl_rel_eext"

lemma sa_impl_rel_eext_def: 
  "\<langle>Rm,Rv,Rl\<rangle>sa_impl_rel_eext 
    \<equiv> \<langle>Rm, Rv\<rightarrow>Rl\<rangle>gen_sa_impl_rel_eext"
  unfolding sa_impl_rel_eext_internal_def relAPP_def by simp

lemmas [autoref_rel_intf] = REL_INTFI[of sa_impl_rel_eext i_sa_eext]

lemma [relator_props, simp]: 
  "\<lbrakk>single_valued Rm; single_valued Rl; Range Rv = UNIV\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rm,Rv,Rl\<rangle>sa_impl_rel_eext)"
  unfolding sa_impl_rel_eext_def by tagged_solver

lemma sa_f_tag: "TERM (Rv\<rightarrow>Rl)" .

abbreviation "sav_impl_rel_ext Rm Rv Rl 
  \<equiv> \<langle>\<langle>Rm, Rv, Rl\<rangle>sa_impl_rel_eext, Rv\<rangle>frgv_impl_rel_ext"

abbreviation "sa_impl_rel_ext Rm Rv Rl 
  \<equiv> \<langle>\<langle>Rm, Rv, Rl\<rangle>sa_impl_rel_eext, Rv\<rangle>g_impl_rel_ext"

type_synonym ('v,'l,'m) sav_impl_scheme = 
  "('v, \<lparr> sai_L :: 'v \<Rightarrow> 'l , \<dots>::'m  \<rparr>) frgv_impl_scheme"

type_synonym ('v,'l,'m) sa_impl_scheme = 
  "('v, \<lparr> sai_L :: 'v \<Rightarrow> 'l , \<dots>::'m  \<rparr>) g_impl_scheme"

context fixes Rv :: "('vi\<times>'v) set" begin
lemmas [autoref_rules] = gen_sa_refine[
  OF frgv_tag[of Rv] sa_f_tag[of Rv], 
  folded frgv_impl_rel_ext_def sa_impl_rel_eext_def]

lemmas [autoref_rules] = gen_sa_refine[
  OF g_tag[of Rv] sa_f_tag[of Rv], 
  folded g_impl_rel_ext_def sa_impl_rel_eext_def]
end

schematic_goal "(?c::?'c, 
    \<lambda>G x l. if sa_L G x = l then (g_E G `` {x}) else {} 
  )\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal 
  notes [autoref_tyrel] = TYRELI[of "Id :: ('a\<times>'a) set"]
  shows "(?c::?'c, \<lambda>E (V0::'a set) L. 
    \<lparr> g_V = {}, g_E = E, g_V0 = V0, sa_L = L \<rparr>)\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal 
  notes [autoref_tyrel] = TYRELI[of "Id :: ('a\<times>'a) set"]
  shows "(?c::?'c, \<lambda>E (V0::'a set) L. 
    \<lparr> g_V = UNIV, g_E = E, g_V0 = V0, sa_L = L \<rparr>)\<in>?R"
  apply (autoref (keep_goal))
  done

subsection \<open>Index Conversion\<close>

schematic_goal gbg_to_idx_ext_impl_aux:
  fixes Re and Rv :: "('qi \<times> 'q) set"
  assumes [autoref_ga_rules]: "is_bounded_hashcode Rv eq bhc"
  assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('qi) (def_size)"
  shows "(?c, gbg_to_idx_ext :: _ \<Rightarrow> ('q, _) gb_graph_rec_scheme \<Rightarrow> _)
   \<in> (gbgv_impl_rel_ext Re Rv \<rightarrow> Ri) 
    \<rightarrow> gbgv_impl_rel_ext Re Rv 
    \<rightarrow> \<langle>igbgv_impl_rel_ext Ri Rv\<rangle>nres_rel"
  unfolding gbg_to_idx_ext_def[abs_def] F_to_idx_impl_def mk_acc_impl_def
  using [[autoref_trace_failed_id]]
  apply (autoref (keep_goal))
  done
concrete_definition gbg_to_idx_ext_impl 
  for eq bhc def_size uses gbg_to_idx_ext_impl_aux

lemmas [autoref_rules] = 
  gbg_to_idx_ext_impl.refine[ 
  OF SIDE_GEN_ALGO_D SIDE_GEN_ALGO_D]

schematic_goal gbg_to_idx_ext_code_aux: 
  "RETURN ?c \<le> gbg_to_idx_ext_impl eq bhc def_size ecnv G"
  unfolding gbg_to_idx_ext_impl_def
  by (refine_transfer)
concrete_definition gbg_to_idx_ext_code 
  for eq bhc ecnv G uses gbg_to_idx_ext_code_aux
lemmas [refine_transfer] = gbg_to_idx_ext_code.refine

term ahm_rel

context begin interpretation autoref_syn .
  lemma [autoref_op_pat]: "gba_to_idx_ext ecnv \<equiv> OP gba_to_idx_ext $ ecnv" by simp
end

schematic_goal gba_to_idx_ext_impl_aux:
  fixes Re and Rv :: "('qi \<times> 'q) set"
  assumes [autoref_ga_rules]: "is_bounded_hashcode Rv eq bhc"
  assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('qi) (def_size)"
  shows "(?c, gba_to_idx_ext :: _ \<Rightarrow> ('q, 'l, _) gba_rec_scheme \<Rightarrow> _)
   \<in> (gbav_impl_rel_ext Re Rv Rl\<rightarrow>Ri) 
    \<rightarrow> gbav_impl_rel_ext Re Rv Rl 
    \<rightarrow> \<langle>igbav_impl_rel_ext Ri Rv Rl\<rangle>nres_rel"
  using [[autoref_trace_failed_id]] unfolding ti_Lcnv_def[abs_def]
  apply (autoref (keep_goal))
  done
concrete_definition gba_to_idx_ext_impl for eq bhc uses gba_to_idx_ext_impl_aux
lemmas [autoref_rules] = 
  gba_to_idx_ext_impl.refine[OF SIDE_GEN_ALGO_D SIDE_GEN_ALGO_D]

schematic_goal gba_to_idx_ext_code_aux: 
  "RETURN ?c \<le> gba_to_idx_ext_impl eq bhc def_size ecnv G"
  unfolding gba_to_idx_ext_impl_def
  by (refine_transfer)
concrete_definition gba_to_idx_ext_code for ecnv G uses gba_to_idx_ext_code_aux
lemmas [refine_transfer] = gba_to_idx_ext_code.refine

subsection \<open>Degeneralization\<close>

context igb_graph begin

lemma degen_impl_aux_alt: "degeneralize_ext ecnv = (
      if num_acc = 0 then \<lparr>
        g_V = Collect (\<lambda>(q,x). x=0 \<and> q\<in>V),
        g_E= E_of_succ (\<lambda>(q,x). if x=0 then (\<lambda>q'. (q',0))`succ_of_E E q else {}),
        g_V0 = (\<lambda>q'. (q',0))`V0, 
        bg_F = Collect (\<lambda>(q,x). x=0 \<and> q\<in>V),
        \<dots> = ecnv G
      \<rparr>
      else \<lparr>
        g_V = Collect (\<lambda>(q,x). x<num_acc \<and> q\<in>V),
        g_E = E_of_succ (\<lambda>(q,i). 
          if i<num_acc then
            let
              i' = if i \<in> acc q then (i + 1) mod num_acc else i
            in (\<lambda>q'. (q',i'))`succ_of_E E q
          else {}
        ),
        g_V0 = (\<lambda>q'. (q',0))`V0,
        bg_F = Collect (\<lambda>(q,x). x=0 \<and> 0\<in>acc q),
        \<dots> = ecnv G
      \<rparr>)"
  unfolding degeneralize_ext_def
  apply (cases "num_acc = 0")
  apply simp_all
  apply (auto simp: E_of_succ_def succ_of_E_def split: if_split_asm) []
  apply (fastforce simp: E_of_succ_def succ_of_E_def split: if_split_asm) []
  done

schematic_goal degeneralize_ext_impl_aux:
  fixes Re Rv
  assumes [autoref_rules]: "(Gi,G) \<in> igbg_impl_rel_ext Re Rv"
  shows "(?c, degeneralize_ext) 
  \<in> (igbg_impl_rel_ext Re Rv \<rightarrow> Re') \<rightarrow> bg_impl_rel_ext Re' (Rv \<times>\<^sub>r nat_rel)"
  unfolding degen_impl_aux_alt[abs_def]
  using [[autoref_trace_failed_id]]
  apply (autoref (keep_goal))
  done

end

definition [simp]: 
  "op_igb_graph_degeneralize_ext ecnv G \<equiv> igb_graph.degeneralize_ext G ecnv"

lemma [autoref_op_pat]: 
  "igb_graph.degeneralize_ext \<equiv> \<lambda>G ecnv. op_igb_graph_degeneralize_ext ecnv G"
  by simp

thm igb_graph.degeneralize_ext_impl_aux[param_fo]
concrete_definition degeneralize_ext_impl
  uses igb_graph.degeneralize_ext_impl_aux[param_fo]

thm degeneralize_ext_impl.refine

context begin interpretation autoref_syn .
lemma [autoref_rules]:
  fixes Re
  assumes "SIDE_PRECOND (igb_graph G)"
  assumes CNVR: "(ecnvi,ecnv) \<in> (igbg_impl_rel_ext Re Rv \<rightarrow> Re')"
  assumes GR: "(Gi,G)\<in>igbg_impl_rel_ext Re Rv"
  shows "(degeneralize_ext_impl Gi ecnvi, 
    (OP op_igb_graph_degeneralize_ext 
       ::: (igbg_impl_rel_ext Re Rv \<rightarrow> Re') \<rightarrow> igbg_impl_rel_ext Re Rv 
        \<rightarrow> bg_impl_rel_ext Re' (Rv \<times>\<^sub>r nat_rel) )$ecnv$G ) 
  \<in> bg_impl_rel_ext Re' (Rv \<times>\<^sub>r nat_rel)"
proof -
  from assms have A: "igb_graph G" by simp

  show ?thesis
    apply simp
    using degeneralize_ext_impl.refine[OF A GR CNVR]
    .
qed

end
thm autoref_itype(1)

schematic_goal
  assumes [simp]: "igb_graph G"
  assumes [autoref_rules]: "(Gi,G)\<in>igbg_impl_rel_ext unit_rel nat_rel"
  shows "(?c::?'c, igb_graph.degeneralize_ext G (\<lambda>_. ())) \<in> ?R"
  apply (autoref (keep_goal))
  done

subsection \<open>Product Construction\<close>

context igba_sys_prod_precond begin

lemma prod_impl_aux_alt:
  "prod = (\<lparr>
    g_V = Collect (\<lambda>(q,s). q \<in> igba.V \<and> s \<in> sa.V),
    g_E = E_of_succ (\<lambda>(q,s). 
      if igba.L q (sa.L s) then     
        succ_of_E (igba.E) q \<times> succ_of_E sa.E s
      else
        {}
    ),
    g_V0 = igba.V0 \<times> sa.V0,
    igbg_num_acc = igba.num_acc,
    igbg_acc = \<lambda>(q,s). if s\<in>sa.V then igba.acc q else {}
  \<rparr>)"
  unfolding prod_def
  apply (auto simp: succ_of_E_def E_of_succ_def split: if_split_asm)
  done

schematic_goal prod_impl_aux:
  fixes Re
  (*assumes [autoref_rules]: "(eqq,(=)) \<in> Rq \<rightarrow> Rq \<rightarrow> bool_rel"
  assumes [autoref_rules]: "(eqs,(=)) \<in> Rs \<rightarrow> Rs \<rightarrow> bool_rel"*)
  assumes [autoref_rules]: "(Gi,G) \<in> igba_impl_rel_ext Re Rq Rl"
  assumes [autoref_rules]: "(Si,S) \<in> sa_impl_rel_ext Re2 Rs Rl"
  shows "(?c, prod) \<in> igbg_impl_rel_ext unit_rel (Rq \<times>\<^sub>r Rs)"
  unfolding prod_impl_aux_alt[abs_def]
  apply (autoref (keep_goal))
  done

end


definition [simp]: "op_igba_sys_prod \<equiv> igba_sys_prod_precond.prod"

lemma [autoref_op_pat]: 
  "igba_sys_prod_precond.prod \<equiv> op_igba_sys_prod"
  by simp

thm igba_sys_prod_precond.prod_impl_aux[param_fo]
concrete_definition igba_sys_prod_impl
  uses igba_sys_prod_precond.prod_impl_aux[param_fo]

thm igba_sys_prod_impl.refine

context begin interpretation autoref_syn .
lemma [autoref_rules]:
  fixes Re
  assumes "SIDE_PRECOND (igba G)"
  assumes "SIDE_PRECOND (sa S)"
  assumes GR: "(Gi,G)\<in>igba_impl_rel_ext unit_rel Rq Rl"
  assumes SR: "(Si,S)\<in>sa_impl_rel_ext unit_rel Rs Rl"
  shows "(igba_sys_prod_impl Gi Si, 
    (OP op_igba_sys_prod 
       :::  igba_impl_rel_ext unit_rel Rq Rl
        \<rightarrow> sa_impl_rel_ext unit_rel Rs Rl
        \<rightarrow> igbg_impl_rel_ext unit_rel (Rq \<times>\<^sub>r Rs) )$G$S ) 
  \<in> igbg_impl_rel_ext unit_rel (Rq \<times>\<^sub>r Rs)"
proof -
  from assms interpret igba: igba G + sa: sa S by simp_all
  have A: "igba_sys_prod_precond G S" by unfold_locales

  show ?thesis
    apply simp
    using igba_sys_prod_impl.refine[OF A GR SR]
    .
qed

end

schematic_goal
  assumes [simp]: "igba G" "sa S"
  assumes [autoref_rules]: "(Gi,G)\<in>igba_impl_rel_ext unit_rel Rq Rl"
  assumes [autoref_rules]: "(Si,S)\<in>sa_impl_rel_ext unit_rel Rs Rl"
  shows "(?c::?'c,igba_sys_prod_precond.prod G S)\<in>?R"
  apply (autoref (keep_goal))
  done

end
