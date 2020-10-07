section \<open>Refinement to Efficient Code\<close>
(*
  Author: Peter Lammich
  Inspired by previous version of Alexander Schimpf.
*)
theory LTL_to_GBA_impl
imports 
  LTL_to_GBA
  Deriving.Compare_Instances
  CAVA_Automata.Automata_Impl
  CAVA_Base.CAVA_Code_Target
begin

subsection \<open>Parametricity Setup Boilerplate\<close>

subsubsection \<open>LTL Formulas\<close>

derive linorder ltlr

inductive_set ltlr_rel for R where
  "(True_ltlr, True_ltlr) \<in> ltlr_rel R"
| "(False_ltlr, False_ltlr) \<in> ltlr_rel R"
| "(a,a')\<in>R \<Longrightarrow> (Prop_ltlr a,Prop_ltlr a') \<in> ltlr_rel R"
| "(a,a')\<in>R \<Longrightarrow> (Nprop_ltlr a,Nprop_ltlr a') \<in> ltlr_rel R"
| "\<lbrakk>(a,a')\<in>ltlr_rel R; (b,b')\<in>ltlr_rel R\<rbrakk> 
  \<Longrightarrow> (And_ltlr a b,And_ltlr a' b') \<in> ltlr_rel R"
| "\<lbrakk>(a,a')\<in>ltlr_rel R; (b,b')\<in>ltlr_rel R\<rbrakk> 
  \<Longrightarrow> (Or_ltlr a b,Or_ltlr a' b') \<in> ltlr_rel R"
| "\<lbrakk>(a,a')\<in>ltlr_rel R\<rbrakk> \<Longrightarrow> (Next_ltlr a,Next_ltlr a') \<in> ltlr_rel R"
| "\<lbrakk>(a,a')\<in>ltlr_rel R; (b,b')\<in>ltlr_rel R\<rbrakk> 
  \<Longrightarrow> (Until_ltlr a b,Until_ltlr a' b') \<in> ltlr_rel R"
| "\<lbrakk>(a,a')\<in>ltlr_rel R; (b,b')\<in>ltlr_rel R\<rbrakk> 
  \<Longrightarrow> (Release_ltlr a b,Release_ltlr a' b') \<in> ltlr_rel R"

lemmas ltlr_rel_induct[induct set] 
  = ltlr_rel.induct[simplified relAPP_def[of ltlr_rel, symmetric]]
lemmas ltlr_rel_cases[cases set] 
  = ltlr_rel.cases[simplified relAPP_def[of ltlr_rel, symmetric]]
lemmas ltlr_rel_intros 
  = ltlr_rel.intros[simplified relAPP_def[of ltlr_rel, symmetric]]

inductive_simps ltlr_rel_left_simps[simplified relAPP_def[of ltlr_rel, symmetric]]: 
  "(True_ltlr,z) \<in> ltlr_rel R"
  "(False_ltlr,z) \<in> ltlr_rel R"
  "(Prop_ltlr p, z) \<in> ltlr_rel R"
  "(Nprop_ltlr p, z) \<in> ltlr_rel R"
  "(And_ltlr a b, z) \<in> ltlr_rel R"
  "(Or_ltlr a b, z) \<in> ltlr_rel R"
  "(Next_ltlr a, z) \<in> ltlr_rel R"
  "(Until_ltlr a b, z) \<in> ltlr_rel R"
  "(Release_ltlr a b, z) \<in> ltlr_rel R"

lemma ltlr_rel_sv[relator_props]: 
  assumes SV: "single_valued R"  
  shows "single_valued (\<langle>R\<rangle>ltlr_rel)"
proof (intro single_valuedI allI impI)
  fix x y z
  assume "(x, y) \<in> \<langle>R\<rangle>ltlr_rel" "(x, z) \<in> \<langle>R\<rangle>ltlr_rel"
  then show "y=z"
    apply (induction arbitrary: z)
    apply (simp (no_asm_use) only: ltlr_rel_left_simps 
      | blast intro: single_valuedD[OF SV])+
    done
qed

lemma ltlr_rel_id[relator_props]: "\<lbrakk> R = Id \<rbrakk> \<Longrightarrow> \<langle>R\<rangle>ltlr_rel = Id"
proof (intro equalityI subsetI, clarsimp_all)
  fix a b
  assume "(a,b)\<in>\<langle>Id\<rangle>ltlr_rel"
  then show "a=b"
    by induction auto
next
  fix a
  show "(a,a)\<in>\<langle>Id\<rangle>ltlr_rel"
    by (induction a) (auto intro: ltlr_rel_intros)
qed

lemma ltlr_rel_id_simp[simp]:  "\<langle>Id\<rangle>ltlr_rel = Id" by (rule ltlr_rel_id) simp

consts i_ltlr :: "interface \<Rightarrow> interface"
lemmas [autoref_rel_intf] = REL_INTFI[of ltlr_rel i_ltlr]

thm ltlr_rel_intros[no_vars]

lemma ltlr_con_param[param, autoref_rules]:
  "(True_ltlr, True_ltlr) \<in> \<langle>R\<rangle>ltlr_rel"
  "(False_ltlr, False_ltlr) \<in> \<langle>R\<rangle>ltlr_rel"
  "(Prop_ltlr, Prop_ltlr) \<in> R \<rightarrow> \<langle>R\<rangle>ltlr_rel"
  "(Nprop_ltlr, Nprop_ltlr) \<in> R \<rightarrow> \<langle>R\<rangle>ltlr_rel"
  "(And_ltlr, And_ltlr) \<in> \<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel"
  "(Or_ltlr, Or_ltlr) \<in> \<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel"
  "(Next_ltlr, Next_ltlr) \<in> \<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel"
  "(Until_ltlr, Until_ltlr) \<in> \<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel"
  "(Release_ltlr, Release_ltlr) \<in> \<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel"
  by (auto intro: ltlr_rel_intros)

lemma case_ltlr_param[param, autoref_rules]: 
  "(case_ltlr,case_ltlr) \<in> Rv \<rightarrow> Rv \<rightarrow> (R \<rightarrow> Rv)
                \<rightarrow> (R \<rightarrow> Rv)
                  \<rightarrow> (\<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> Rv)
                    \<rightarrow> (\<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> Rv)
                      \<rightarrow> (\<langle>R\<rangle>ltlr_rel \<rightarrow> Rv)
                        \<rightarrow> (\<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> Rv)
                          \<rightarrow> (\<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> Rv) \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> Rv"
  apply (clarsimp)
  apply (case_tac ai, simp_all add: ltlr_rel_left_simps)
  apply (clarsimp_all)
  apply parametricity+
  done

lemma rec_ltlr_param[param, autoref_rules]: 
  "(rec_ltlr,rec_ltlr) \<in> Rv \<rightarrow> Rv \<rightarrow> (R \<rightarrow> Rv)
                \<rightarrow> (R \<rightarrow> Rv)
                  \<rightarrow> (\<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> Rv \<rightarrow> Rv \<rightarrow> Rv)
                    \<rightarrow> (\<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> Rv \<rightarrow> Rv \<rightarrow> Rv)
                      \<rightarrow> (\<langle>R\<rangle>ltlr_rel \<rightarrow> Rv \<rightarrow> Rv)
                        \<rightarrow> (\<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> Rv \<rightarrow> Rv \<rightarrow> Rv)
                          \<rightarrow> (\<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> Rv \<rightarrow> Rv \<rightarrow> Rv)
                            \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> Rv"
proof (clarsimp, goal_cases)
  case prems: 1
  from prems(10)
  show ?case 
    apply (induction)
    using prems(1-9)
    apply simp_all
    apply parametricity+
    done
qed

lemma case_ltlr_mono[refine_mono]: 
  assumes "\<phi> = True_ltlr \<Longrightarrow> a\<le>a'"
  assumes "\<phi> = False_ltlr \<Longrightarrow> b\<le>b'"
  assumes "\<And>p. \<phi> = Prop_ltlr p \<Longrightarrow> c p\<le>c' p"
  assumes "\<And>p. \<phi> = Nprop_ltlr p \<Longrightarrow> d p\<le>d' p"
  assumes "\<And>\<mu> \<nu>. \<phi> = And_ltlr \<mu> \<nu> \<Longrightarrow> e \<mu> \<nu>\<le>e' \<mu> \<nu>"
  assumes "\<And>\<mu> \<nu>. \<phi> = Or_ltlr \<mu> \<nu> \<Longrightarrow> f \<mu> \<nu>\<le>f' \<mu> \<nu>"
  assumes "\<And>\<mu>. \<phi> = Next_ltlr \<mu> \<Longrightarrow> g \<mu>\<le>g' \<mu>"
  assumes "\<And>\<mu> \<nu>. \<phi> = Until_ltlr \<mu> \<nu> \<Longrightarrow> h \<mu> \<nu>\<le>h' \<mu> \<nu>"
  assumes "\<And>\<mu> \<nu>. \<phi> = Release_ltlr \<mu> \<nu> \<Longrightarrow> i \<mu> \<nu>\<le>i' \<mu> \<nu>"
  shows "case_ltlr a b c d e f g h i \<phi> \<le> case_ltlr a' b' c' d' e' f' g' h' i' \<phi>"
  using assms
  apply (cases \<phi>)
  apply simp_all
  done


primrec ltlr_eq where
  "ltlr_eq eq True_ltlr f \<longleftrightarrow> (case f of True_ltlr \<Rightarrow> True | _ \<Rightarrow> False)"
| "ltlr_eq eq False_ltlr f \<longleftrightarrow> (case f of False_ltlr \<Rightarrow> True | _ \<Rightarrow> False)"
| "ltlr_eq eq (Prop_ltlr p) f \<longleftrightarrow> (case f of Prop_ltlr p' \<Rightarrow> eq p p' | _ \<Rightarrow> False)"
| "ltlr_eq eq (Nprop_ltlr p) f \<longleftrightarrow> (case f of Nprop_ltlr p' \<Rightarrow> eq p p' | _ \<Rightarrow> False)"
| "ltlr_eq eq (And_ltlr \<mu> \<nu>) f 
  \<longleftrightarrow> (case f of And_ltlr \<mu>' \<nu>' \<Rightarrow> ltlr_eq eq \<mu> \<mu>' \<and> ltlr_eq eq \<nu> \<nu>' | _ \<Rightarrow> False)"
| "ltlr_eq eq (Or_ltlr \<mu> \<nu>) f 
  \<longleftrightarrow> (case f of Or_ltlr \<mu>' \<nu>' \<Rightarrow> ltlr_eq eq \<mu> \<mu>' \<and> ltlr_eq eq \<nu> \<nu>' | _ \<Rightarrow> False)"
| "ltlr_eq eq (Next_ltlr \<phi>) f 
  \<longleftrightarrow> (case f of Next_ltlr \<phi>' \<Rightarrow> ltlr_eq eq \<phi> \<phi>' | _ \<Rightarrow> False)"
| "ltlr_eq eq (Until_ltlr \<mu> \<nu>) f 
  \<longleftrightarrow> (case f of Until_ltlr \<mu>' \<nu>' \<Rightarrow> ltlr_eq eq \<mu> \<mu>' \<and> ltlr_eq eq \<nu> \<nu>' | _ \<Rightarrow> False)"
| "ltlr_eq eq (Release_ltlr \<mu> \<nu>) f 
  \<longleftrightarrow> (case f of 
    Release_ltlr \<mu>' \<nu>' \<Rightarrow> ltlr_eq eq \<mu> \<mu>' \<and> ltlr_eq eq \<nu> \<nu>' 
  | _ \<Rightarrow> False)"

lemma ltlr_eq_autoref[autoref_rules]:
  assumes EQP: "(eq,(=)) \<in> R \<rightarrow> R \<rightarrow> bool_rel"
  shows "(ltlr_eq eq, (=)) \<in> \<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> bool_rel"
proof (intro fun_relI)
  fix \<mu>' \<mu> \<nu>' \<nu>
  assume "(\<mu>',\<mu>)\<in>\<langle>R\<rangle>ltlr_rel" and "(\<nu>',\<nu>)\<in>\<langle>R\<rangle>ltlr_rel"
  then show "(ltlr_eq eq \<mu>' \<nu>', \<mu>=\<nu>)\<in>bool_rel"
    apply (induction arbitrary: \<nu>' \<nu>)
    apply (erule ltlr_rel_cases, simp_all) []
    apply (erule ltlr_rel_cases, simp_all) []
    apply (erule ltlr_rel_cases, 
      simp_all add: EQP[THEN fun_relD, THEN fun_relD, THEN IdD]) []
    apply (erule ltlr_rel_cases, 
      simp_all add: EQP[THEN fun_relD, THEN fun_relD, THEN IdD]) []
    apply (rotate_tac -1)
    apply (erule ltlr_rel_cases, simp_all) []
    apply (rotate_tac -1)
    apply (erule ltlr_rel_cases, simp_all) []
    apply (rotate_tac -1)
    apply (erule ltlr_rel_cases, simp_all) []
    apply (rotate_tac -1)
    apply (erule ltlr_rel_cases, simp_all) []
    apply (rotate_tac -1)
    apply (erule ltlr_rel_cases, simp_all) []
    done
qed

lemma ltlr_dflt_cmp[autoref_rules_raw]: 
  assumes "PREFER_id R"
  shows
  "(dflt_cmp (\<le>) (<), dflt_cmp (\<le>) (<)) 
  \<in> \<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> comp_res_rel"
  using assms
  by simp

type_synonym
  node_name_impl = node_name 

abbreviation (input) "node_name_rel \<equiv> Id :: (node_name_impl\<times>node_name) set"

lemma case_ltlr_gtransfer:
  assumes
  "\<gamma> ai \<le> a"
  "\<gamma> bi \<le> b"
  "\<And>a. \<gamma> (ci a) \<le> c a"
  "\<And>a. \<gamma> (di a) \<le> d a"
  "\<And>ltlr1 ltlr2. \<gamma> (ei ltlr1 ltlr2) \<le> e ltlr1 ltlr2"
  "\<And>ltlr1 ltlr2. \<gamma> (fi ltlr1 ltlr2) \<le> f ltlr1 ltlr2"
  "\<And>ltlr. \<gamma> (gi ltlr) \<le> g ltlr"
  "\<And>ltlr1 ltlr2. \<gamma> (hi ltlr1 ltlr2) \<le> h ltlr1 ltlr2"
  "\<And>ltlr1 ltlr2. \<gamma> (iiv ltlr1 ltlr2) \<le> i ltlr1 ltlr2"
  shows "\<gamma> (case_ltlr ai bi ci di ei fi gi hi iiv \<phi>) 
    \<le> (case_ltlr a b c d e f g h i \<phi>)"
  apply (cases \<phi>)
  apply (auto intro: assms)
  done

lemmas [refine_transfer] 
  = case_ltlr_gtransfer[where \<gamma>=nres_of] case_ltlr_gtransfer[where \<gamma>=RETURN]

lemma [refine_transfer]:
  assumes 
  "ai \<noteq> dSUCCEED"
  "bi \<noteq> dSUCCEED"
  "\<And>a. ci a \<noteq> dSUCCEED"
  "\<And>a. di a \<noteq> dSUCCEED"
  "\<And>ltlr1 ltlr2. ei ltlr1 ltlr2 \<noteq> dSUCCEED"
  "\<And>ltlr1 ltlr2. fi ltlr1 ltlr2 \<noteq> dSUCCEED"
  "\<And>ltlr. gi ltlr \<noteq> dSUCCEED"
  "\<And>ltlr1 ltlr2. hi ltlr1 ltlr2 \<noteq> dSUCCEED"
  "\<And>ltlr1 ltlr2. iiv ltlr1 ltlr2 \<noteq> dSUCCEED"
  shows "case_ltlr ai bi ci di ei fi gi hi iiv \<phi> \<noteq> dSUCCEED"
  apply (cases \<phi>)
  apply (simp_all add: assms)
  done

subsubsection \<open>Nodes\<close>

record 'a node_impl =
  name_impl   :: node_name_impl
  incoming_impl :: "(node_name_impl,unit) RBT_Impl.rbt"
  new_impl :: "'a frml list"
  old_impl :: "'a frml list"
  next_impl :: "'a frml list"

definition node_rel where node_rel_def_internal: "node_rel Re R \<equiv> {( 
  \<lparr> name_impl = namei, 
    incoming_impl = inci, 
    new_impl = newi,
    old_impl = oldi,
    next_impl = nexti,
    \<dots> = morei
  \<rparr>, 
  \<lparr> name = name,
    incoming = inc,
    new=new,
    old=old,
    next = next,
    \<dots> = more
  \<rparr> ) | namei name inci inc newi new oldi old nexti next morei more. 
    (namei,name)\<in>node_name_rel 
  \<and> (inci,inc)\<in>\<langle>node_name_rel\<rangle>dflt_rs_rel 
  \<and> (newi,new)\<in>\<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel
  \<and> (oldi,old)\<in>\<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel
  \<and> (nexti,next)\<in>\<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel
  \<and> (morei,more)\<in>Re
  }"

lemma node_rel_def: "\<langle>Re,R\<rangle>node_rel = {( 
  \<lparr> name_impl = namei, 
    incoming_impl = inci, 
    new_impl = newi,
    old_impl = oldi,
    next_impl = nexti,
    \<dots> = morei
  \<rparr>, 
  \<lparr> name = name,
    incoming = inc,
    new=new,
    old=old,
    next = next,
    \<dots> = more
  \<rparr> ) | namei name inci inc newi new oldi old nexti next morei more. 
    (namei,name)\<in>node_name_rel 
  \<and> (inci,inc)\<in>\<langle>node_name_rel\<rangle>dflt_rs_rel  
  \<and> (newi,new)\<in>\<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel
  \<and> (oldi,old)\<in>\<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel
  \<and> (nexti,next)\<in>\<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel
  \<and> (morei,more)\<in>Re
  }" by (simp add: node_rel_def_internal relAPP_def)


lemma node_rel_sv[relator_props]: 
  "single_valued Re \<Longrightarrow> single_valued R \<Longrightarrow> single_valued (\<langle>Re,R\<rangle>node_rel)"
  apply (rule single_valuedI)
  apply (simp add: node_rel_def)
  apply (auto 
    dest: single_valuedD lss.rel_sv[OF ltlr_rel_sv] map2set_rel_sv[OF ahm_rel_sv] 
    dest: single_valuedD[
      OF map2set_rel_sv[OF rbt_map_rel_sv[OF single_valued_Id single_valued_Id]]
    ])
  done

consts i_node :: "interface \<Rightarrow> interface \<Rightarrow> interface"

lemmas [autoref_rel_intf] = REL_INTFI[of node_rel i_node]

lemma [autoref_rules]: "(node_impl_ext, node_ext) \<in> 
  node_name_rel 
  \<rightarrow> \<langle>node_name_rel\<rangle>dflt_rs_rel 
  \<rightarrow> \<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel 
  \<rightarrow> \<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel 
  \<rightarrow> \<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel 
  \<rightarrow> Re 
  \<rightarrow> \<langle>Re,R\<rangle>node_rel"
  unfolding node_rel_def
  by auto

lemma [autoref_rules]: 
  "(node_impl.name_impl_update,node.name_update) 
  \<in> (node_name_rel \<rightarrow> node_name_rel) \<rightarrow> \<langle>Re,R\<rangle>node_rel \<rightarrow> \<langle>Re,R\<rangle>node_rel"
  "(node_impl.incoming_impl_update,node.incoming_update) 
  \<in> (\<langle>node_name_rel\<rangle>dflt_rs_rel \<rightarrow> \<langle>node_name_rel\<rangle>dflt_rs_rel) 
    \<rightarrow> \<langle>Re,R\<rangle>node_rel 
    \<rightarrow> \<langle>Re,R\<rangle>node_rel"
  "(node_impl.new_impl_update,node.new_update) 
  \<in> (\<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel \<rightarrow> \<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel) \<rightarrow> \<langle>Re,R\<rangle>node_rel \<rightarrow> \<langle>Re,R\<rangle>node_rel"
  "(node_impl.old_impl_update,node.old_update) 
  \<in> (\<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel \<rightarrow> \<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel) \<rightarrow> \<langle>Re,R\<rangle>node_rel \<rightarrow> \<langle>Re,R\<rangle>node_rel"
  "(node_impl.next_impl_update,node.next_update) 
  \<in> (\<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel \<rightarrow> \<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel) \<rightarrow> \<langle>Re,R\<rangle>node_rel \<rightarrow> \<langle>Re,R\<rangle>node_rel"
  "(node_impl.more_update,node.more_update) 
  \<in> (Re \<rightarrow> Re) \<rightarrow> \<langle>Re,R\<rangle>node_rel \<rightarrow> \<langle>Re,R\<rangle>node_rel"
  unfolding node_rel_def
  by (auto dest: fun_relD)

term name
lemma [autoref_rules]:
  "(node_impl.name_impl,node.name)\<in>\<langle>Re,R\<rangle>node_rel \<rightarrow> node_name_rel"
  "(node_impl.incoming_impl,node.incoming)
  \<in> \<langle>Re,R\<rangle>node_rel \<rightarrow> \<langle>node_name_rel\<rangle>dflt_rs_rel"
  "(node_impl.new_impl,node.new)\<in>\<langle>Re,R\<rangle>node_rel \<rightarrow> \<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel"
  "(node_impl.old_impl,node.old)\<in>\<langle>Re,R\<rangle>node_rel \<rightarrow> \<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel"
  "(node_impl.next_impl,node.next)\<in>\<langle>Re,R\<rangle>node_rel \<rightarrow> \<langle>\<langle>R\<rangle>ltlr_rel\<rangle>lss.rel"
  "(node_impl.more, node.more)\<in>\<langle>Re,R\<rangle>node_rel \<rightarrow> Re"
  unfolding node_rel_def by auto


subsection \<open>Massaging the Abstract Algorithm\<close>
text \<open>
  In a first step, we do some refinement steps on the abstract data structures,
  with the goal to make the algorithm more efficient.
\<close>

subsubsection \<open>Creation of the Nodes\<close>
text \<open>
  In the expand-algorithm, we replace nested conditionals by case-distinctions,
  and slightly stratify the code.
\<close>



abbreviation (input) "expand2 exp n ns \<phi> n1 nx1 n2 \<equiv> do {
    (nm, nds) \<leftarrow> exp (
      n\<lparr> 
        new := insert n1 (new n), 
        old := insert \<phi> (old n), 
        next := nx1 \<union> next n \<rparr>, 
      ns);
    exp (n\<lparr> name := nm, new := n2 \<union> new n, old := {\<phi>} \<union> old n \<rparr>, nds)
  }"



definition "expand_aimpl \<equiv> REC\<^sub>T (\<lambda>expand (n,ns). 
      if new n = {} then ( 
        if (\<exists>n'\<in>ns. old n' = old n \<and> next n' = next n) then 
          RETURN (name n, upd_incoming n ns)
        else do {
          ASSERT (n \<notin> ns);
          ASSERT (name n \<notin> name`ns);
          expand (\<lparr> 
            name=expand_new_name (name n), 
            incoming={name n}, 
            new=next n, 
            old={}, 
            next={} \<rparr>, 
            insert n ns)
        }
      ) else do { 
        \<phi> \<leftarrow> SPEC (\<lambda>x. x\<in>(new n));
        let n = n\<lparr> new := new n - {\<phi>} \<rparr>;
        case \<phi> of
          prop\<^sub>r(q) \<Rightarrow> 
            if nprop\<^sub>r(q)\<in>old n then RETURN (name n, ns)
            else expand (n\<lparr> old := {\<phi>} \<union> old n \<rparr>, ns)
        | nprop\<^sub>r(q) \<Rightarrow> 
            if prop\<^sub>r(q)\<in>old n then RETURN (name n, ns)
            else expand (n\<lparr> old := {\<phi>} \<union> old n \<rparr>, ns)
        | true\<^sub>r \<Rightarrow> expand (n\<lparr> old := {\<phi>} \<union> old n \<rparr>, ns)
        | false\<^sub>r \<Rightarrow> RETURN (name n, ns)
        | \<nu> and\<^sub>r \<mu> \<Rightarrow> expand (n\<lparr> 
            new := insert \<nu> (insert \<mu> (new n)), 
            old := {\<phi>} \<union> old n, 
            next := next n \<rparr>, ns)
        | X\<^sub>r \<nu> \<Rightarrow> expand 
            (n\<lparr> new := new n, old := {\<phi>} \<union> old n, next := insert \<nu> (next n) \<rparr>, ns)
        | \<mu> or\<^sub>r \<nu> \<Rightarrow> expand2 expand n ns \<phi> \<mu> {} {\<nu>}
        | \<mu> U\<^sub>r \<nu> \<Rightarrow> expand2 expand n ns \<phi> \<mu> {\<phi>} {\<nu>}
        | \<mu> R\<^sub>r \<nu> \<Rightarrow> expand2 expand n ns \<phi> \<nu> {\<phi>} {\<mu>,\<nu>}
        \<^cancel>\<open>| _ \<Rightarrow> do {
          (nm, nds) \<leftarrow> expand (
            n\<lparr> 
              new := new1 \<phi> \<union> new n, 
              old := {\<phi>} \<union> old n, 
              next := next1 \<phi> \<union> next n \<rparr>,
            ns);
          expand (n\<lparr> name := nm, new := new2 \<phi> \<union> new n, old := {\<phi>} \<union> old n \<rparr>, nds)
        }\<close>
      }
     )"


lemma expand_aimpl_refine:
  fixes n_ns :: "('a node \<times> _)"
  defines "R \<equiv> Id \<inter> {(_,(n,ns)). \<forall>n'\<in>ns. n > name n'}"
  defines "R' \<equiv> Id \<inter> {(_,(n,ns)). \<forall>n'\<in>ns. name n > name n'}"
  assumes [refine]: "(n_ns',n_ns)\<in>R'"
  shows "expand_aimpl n_ns' \<le> \<Down>R (expand\<^sub>T n_ns)"
  using [[goals_limit = 1]]
proof -
  have [relator_props]: "single_valued R" 
    by (auto simp add: R_def intro: single_valuedI)
  have [relator_props]: "single_valued R'" 
    by (auto simp add: R'_def intro: single_valuedI)

  {
    fix n :: "'a node" and ns and n' ns'
    assume "((n', ns'), (n, ns)) \<in> R'"
    then have "(RETURN (name n', ns') \<le> \<Down> R (RETURN (name n, ns)))"
      by (auto simp: R_def R'_def pw_le_iff refine_pw_simps)
  } note aux = this


  show ?thesis
    unfolding expand_aimpl_def expand\<^sub>T_def
    apply refine_rcg
    apply (simp add: R_def R'_def)
    apply (simp add: R_def R'_def)
    apply (auto simp add: R_def R'_def upd_incoming_def) []
    apply (auto simp add: R_def R'_def upd_incoming_def) []
    apply (auto simp add: R_def R'_def upd_incoming_def) []
    apply rprems
    apply (auto simp: R'_def expand_new_name_def) []
    apply (simp add: R'_def)

    apply (auto split: ltlr.split) []
    apply (fastforce simp: R_def R'_def) []
    apply (fastforce simp: R_def R'_def) []

    apply (auto simp: R_def R'_def) []
    apply (auto simp: R_def R'_def) []
    apply (auto simp: R_def R'_def) []
    apply (auto simp: R_def R'_def) []
    apply (auto simp: R_def R'_def) []
    apply (auto simp: R_def R'_def) []
    apply (auto simp: R_def R'_def) []
    apply (auto simp: R_def R'_def) []
    apply (auto simp: R_def R'_def) []
    apply (refine_rcg, rprems, (fastforce simp: R_def R'_def)+) []
    apply (fastforce simp: R'_def) []
    apply (refine_rcg, rprems, (fastforce simp: R_def R'_def)+) []
    apply (refine_rcg, rprems, (fastforce simp: R_def R'_def)+) []
    done
qed


thm create_graph_def
definition "create_graph_aimpl \<phi> = do {
  (_, nds) \<leftarrow>
  expand_aimpl
   (\<lparr>name = expand_new_name expand_init, incoming = {expand_init},
       new = {\<phi>}, old = {}, next = {}\<rparr>,
    {});
  RETURN nds
}"

lemma create_graph_aimpl_refine: "create_graph_aimpl \<phi> \<le> \<Down>Id (create_graph\<^sub>T \<phi>)"
  unfolding create_graph_aimpl_def create_graph\<^sub>T_def
  apply (refine_rcg expand_aimpl_refine)
  apply auto
  done

subsubsection \<open>Creation of GBA from Nodes\<close>

text \<open>
  We summarize creation of the GBA and renaming of the nodes into one step
\<close>
lemma create_name_gba_alt: "create_name_gba \<phi> = do {
  nds \<leftarrow> create_graph\<^sub>T \<phi>;
  ASSERT (nds_invars nds);
  RETURN (gba_rename_ext (\<lambda>_. ()) name (create_gba_from_nodes \<phi> nds))
  }"
proof -
  have [simp]: "\<And>nds. g_V (create_gba_from_nodes \<phi> nds) = nds"
    by (auto simp: create_gba_from_nodes_def)

  show ?thesis
    unfolding create_name_gba_def create_gba_def
    by simp
qed

text \<open>In the following, we implement the componenents of the
  renamed GBA separately.
\<close>

text \<open>\paragraph{Successor Function}\<close>

definition "build_succ nds = 
  FOREACH 
    nds (\<lambda>q' s.
    FOREACH
      (incoming q') (\<lambda>qn s. 
        if qn=expand_init then 
          RETURN s 
        else 
          RETURN (s(qn \<mapsto> insert (name q') (the_default {} (s qn))))
    ) s
  ) Map.empty"

lemma build_succ_aux1:
  assumes [simp]: "finite nds"
  assumes [simp]: "\<And>q. q\<in>nds \<Longrightarrow> finite (incoming q)"
  shows "build_succ nds \<le> SPEC (\<lambda>r. r = (\<lambda>qn. 
  dflt_None_set {qn'. \<exists>q'. 
    q'\<in>nds \<and> qn' = name q' \<and> qn\<in>incoming q' \<and> qn\<noteq>expand_init 
  }))"
  unfolding build_succ_def
  apply (refine_rcg refine_vcg 
    FOREACH_rule[where
      I="\<lambda>it s. s = (\<lambda>qn. dflt_None_set {qn'. \<exists>q'. q'\<in>nds-it \<and> qn' = name q' 
    \<and> qn\<in>incoming q' \<and> qn\<noteq>expand_init })"])

  apply (simp_all add: dflt_None_set_def) [2]
  apply (rename_tac q' it s)
  apply (rule_tac I="\<lambda>it2 s. s = 
    (\<lambda>qn. dflt_None_set (
      {qn'. \<exists>q'. q'\<in>nds-it \<and> qn' = name q' \<and> qn\<in>incoming q' \<and> qn\<noteq>expand_init } \<union> 
      {qn' . qn'=name q' \<and> qn\<in>incoming q' - it2 \<and> qn\<noteq>expand_init} ))" 
    in FOREACH_rule)

  apply auto []

  apply (simp_all add: dflt_None_set_def)

  apply (refine_rcg refine_vcg)
  apply (auto simp: dflt_None_set_def intro!: ext) []
  apply (rule ext, (auto) [])+
  done

lemma build_succ_aux2:
  assumes NINIT: "expand_init \<notin> name`nds"
  assumes CL: "\<And>nd. nd\<in>nds \<Longrightarrow> incoming nd \<subseteq> insert expand_init (name`nds)"
  shows
  "(\<lambda>qn. dflt_None_set 
    {qn'. \<exists>q'. q'\<in>nds \<and> qn' = name q' \<and> qn\<in>incoming q' \<and> qn\<noteq>expand_init }) 
  = (\<lambda>qn. dflt_None_set (succ_of_E 
       (rename_E name {(q, q'). q \<in> nds \<and> q' \<in> nds \<and> name q \<in> incoming q'}) qn))" 
  (is "(\<lambda>qn. dflt_None_set (?L qn)) = (\<lambda>qn. dflt_None_set (?R qn))")
  apply (intro ext)
  apply (fo_rule arg_cong)
proof (intro ext equalityI subsetI)
  fix qn x
  assume "x\<in>?R qn"
  then show "x\<in>?L qn" using NINIT
    by (force simp: succ_of_E_def)
next
  fix qn x
  assume XL: "x\<in>?L qn"
  show "x\<in>?R qn"
  proof (cases "qn = expand_init")
    case False
    from XL obtain q' where 
      A: "q'\<in>nds" "qn\<in>incoming q'" 
      and [simp]: "x=name q'" 
      by auto
    from False obtain q where B: "q\<in>nds" and [simp]: "qn = name q"
      using CL A by auto

    from A B show "x\<in>?R qn"
      by (auto simp: succ_of_E_def image_def)
  next
    case [simp]: True
    from XL show "x\<in>?R qn" by simp
  qed
qed

lemma build_succ_correct:
  assumes NINIT: "expand_init \<notin> name`nds"
  assumes FIN: "finite nds"
  assumes CL: "\<And>nd. nd\<in>nds \<Longrightarrow> incoming nd \<subseteq> insert expand_init (name`nds)"
  shows "build_succ nds \<le> SPEC (\<lambda>r. 
    E_of_succ (\<lambda>qn. the_default {} (r qn)) 
    = rename_E (\<lambda>u. name u) {(q, q'). q \<in> nds \<and> q' \<in> nds \<and> name q \<in> incoming q'})"
proof -
  from FIN CL have FIN': "\<And>q. q\<in>nds \<Longrightarrow> finite (incoming q)"
    by (metis finite_imageI finite_insert infinite_super)
  
  note build_succ_aux1[OF FIN FIN']
  also note build_succ_aux2[OF NINIT CL]
  finally show ?thesis
    by (rule order_trans) auto
qed

text \<open>\paragraph{ Accepting Sets}\<close>

primrec until_frmlsr :: "'a frml \<Rightarrow> ('a frml \<times> 'a frml) set" where
  "until_frmlsr (\<mu> and\<^sub>r \<psi>) = (until_frmlsr \<mu>) \<union> (until_frmlsr \<psi>)"
| "until_frmlsr (X\<^sub>r \<mu>) = until_frmlsr \<mu>"
| "until_frmlsr (\<mu> U\<^sub>r \<psi>) = insert (\<mu>, \<psi>) ((until_frmlsr \<mu>) \<union> (until_frmlsr \<psi>))"
| "until_frmlsr (\<mu> R\<^sub>r \<psi>) = (until_frmlsr \<mu>) \<union> (until_frmlsr \<psi>)"
| "until_frmlsr (\<mu> or\<^sub>r \<psi>) = (until_frmlsr \<mu>) \<union> (until_frmlsr \<psi>)"
| "until_frmlsr (true\<^sub>r) = {}"
| "until_frmlsr (false\<^sub>r) = {}"
| "until_frmlsr (prop\<^sub>r(_)) = {}"
| "until_frmlsr (nprop\<^sub>r(_)) = {}"

lemma until_frmlsr_correct: 
  "until_frmlsr \<phi> = {(\<mu>, \<eta>). Until_ltlr \<mu> \<eta> \<in> subfrmlsr \<phi>}"
  by (induct \<phi>) auto


definition "build_F nds \<phi> 
  \<equiv> (\<lambda>(\<mu>,\<eta>). name ` {q \<in> nds. (Until_ltlr \<mu> \<eta> \<in> old q \<longrightarrow> \<eta> \<in> old q)}) `
    until_frmlsr \<phi>"

lemma build_F_correct: "build_F nds \<phi> = 
  {name ` A |A. \<exists>\<mu> \<eta>. A = {q \<in> nds. Until_ltlr \<mu> \<eta> \<in> old q \<longrightarrow> \<eta> \<in> old q} \<and>
                     Until_ltlr \<mu> \<eta> \<in> subfrmlsr \<phi>}"
proof -
  have "{name ` A |A. \<exists>\<mu> \<eta>. A = {q \<in> nds. Until_ltlr \<mu> \<eta> \<in> old q \<longrightarrow> \<eta> \<in> old q} \<and>
                     Until_ltlr \<mu> \<eta> \<in> subfrmlsr \<phi>}
    = (\<lambda>(\<mu>,\<eta>). name`{q\<in>nds. Until_ltlr \<mu> \<eta> \<in> old q \<longrightarrow> \<eta> \<in> old q}) 
      ` {(\<mu>, \<eta>). Until_ltlr \<mu> \<eta> \<in> subfrmlsr \<phi>}"
    by auto
  also have "\<dots> = (\<lambda>(\<mu>,\<eta>). name`{q\<in>nds. Until_ltlr \<mu> \<eta> \<in> old q \<longrightarrow> \<eta> \<in> old q}) 
      ` until_frmlsr \<phi>"
    unfolding until_frmlsr_correct ..
  finally show ?thesis
    unfolding build_F_def by simp
qed

text \<open>\paragraph{ Labeling Function }\<close>
definition "pn_props ps \<equiv> FOREACHi 
  (\<lambda>it (P,N). P = {p. Prop_ltlr p \<in> ps - it} \<and> N = {p. Nprop_ltlr p \<in> ps - it}) 
  ps (\<lambda>p (P,N). 
    case p of Prop_ltlr p \<Rightarrow> RETURN (insert p P,N)
    | Nprop_ltlr p \<Rightarrow> RETURN (P, insert p N)
    | _ \<Rightarrow> RETURN (P,N)
  ) ({},{})"

lemma pn_props_correct: 
  assumes [simp]: "finite ps"
  shows "pn_props ps \<le> SPEC(\<lambda>r. r = 
  ({p. Prop_ltlr p \<in> ps}, {p. Nprop_ltlr p \<in> ps}))"
  unfolding pn_props_def
  apply (refine_rcg refine_vcg)
  apply (auto split: ltlr.split)
  done

definition "pn_map nds \<equiv> FOREACH nds 
  (\<lambda>nd m. do {
    PN \<leftarrow> pn_props (old nd);
    RETURN (m(name nd \<mapsto> PN))
  }) Map.empty"

lemma pn_map_correct: 
  assumes [simp]: "finite nds"
  assumes FIN': "\<And>nd. nd\<in>nds \<Longrightarrow> finite (old nd)"
  assumes INJ: "inj_on name nds"
  shows "pn_map nds \<le> SPEC (\<lambda>r. \<forall>qn. 
    case r qn of 
      None \<Rightarrow> qn \<notin> name`nds
    | Some (P,N) \<Rightarrow> qn \<in> name`nds 
      \<and> P = {p. Prop_ltlr p \<in> old (the_inv_into nds name qn)}
      \<and> N = {p. Nprop_ltlr p \<in> old (the_inv_into nds name qn)}
  )"
  unfolding pn_map_def
  apply (refine_rcg refine_vcg
    FOREACH_rule[where I="\<lambda>it r. \<forall>qn. 
      case r qn of 
        None \<Rightarrow> qn \<notin> name`(nds - it)
      | Some (P,N) \<Rightarrow> qn \<in> name`(nds - it)
        \<and> P = {p. Prop_ltlr p \<in> old (the_inv_into nds name qn)}
        \<and> N = {p. Nprop_ltlr p \<in> old (the_inv_into nds name qn)}"]
    order_trans[OF pn_props_correct]
  )
  apply simp_all
  apply (blast dest: subsetD[THEN FIN']) []
  apply (force 
    split: option.splits 
    simp: the_inv_into_f_f[OF INJ] it_step_insert_iff) []
  apply (fastforce split: option.splits) []
  done

 
text \<open>\paragraph{ Assembling the Implementation }\<close>
  
definition "cr_rename_gba nds \<phi> \<equiv> do {
  let V = name ` nds;
  let V0 = name ` {q \<in> nds. expand_init \<in> incoming q};
  succmap \<leftarrow> build_succ nds;
  let E = E_of_succ (the_default {} o succmap);
  let F = build_F nds \<phi>;
  pnm \<leftarrow> pn_map nds;
  let L = (\<lambda>qn l. case pnm qn of 
      None \<Rightarrow> False 
    | Some (P,N) \<Rightarrow> (\<forall>p\<in>P. p\<in>(l:::\<^sub>r\<langle>Id\<rangle>fun_set_rel)) \<and> (\<forall>p\<in>N. p\<notin>l)
  );
  RETURN (\<lparr> g_V = V, g_E=E, g_V0=V0, gbg_F = F, gba_L = L \<rparr>)
}"

lemma cr_rename_gba_refine:
  assumes INV: "nds_invars nds"
  assumes REL[simplified]: "(nds',nds)\<in>Id" "(\<phi>',\<phi>)\<in>Id"
  shows "cr_rename_gba nds' \<phi>' 
  \<le> \<Down>Id (RETURN (gba_rename_ext (\<lambda>_. ()) name (create_gba_from_nodes \<phi> nds)))"
  unfolding RETURN_SPEC_conv
proof (rule Id_SPEC_refine)
  from INV have
    NINIT: "expand_init \<notin> name`nds"
    and FIN: "finite nds"
    and FIN': "\<And>nd. nd\<in>nds \<Longrightarrow> finite (old nd)"
    and CL: "\<And>nd. nd\<in>nds \<Longrightarrow> incoming nd \<subseteq> insert expand_init (name`nds)"
    and INJ: "inj_on name nds"
    unfolding nds_invars_def by auto
  show "cr_rename_gba nds' \<phi>'
    \<le> SPEC (\<lambda>x. x = gba_rename_ext (\<lambda>_. ()) name (create_gba_from_nodes \<phi> nds))"
    unfolding REL
    unfolding cr_rename_gba_def
    apply (refine_rcg refine_vcg
      order_trans[OF build_succ_correct[OF NINIT FIN CL]]
      order_trans[OF pn_map_correct[OF FIN FIN' INJ]]
    )
    unfolding gba_rename_ecnv_def gb_rename_ecnv_def 
      fr_rename_ext_def create_gba_from_nodes_def
    apply simp
    apply (intro conjI)
    apply (simp add: comp_def)
    apply (simp add: build_F_correct)
    apply (intro ext)
    apply (drule_tac x=qn in spec)
    apply (auto simp: the_inv_into_f_f[OF INJ] split: option.split prod.split)
    done
qed

definition "create_name_gba_aimpl \<phi> \<equiv> do {
  nds \<leftarrow> create_graph_aimpl \<phi>;
  ASSERT (nds_invars nds);
  cr_rename_gba nds \<phi>
}"


lemma create_name_gba_aimpl_refine: 
  "create_name_gba_aimpl \<phi> \<le> \<Down>Id (create_name_gba \<phi>)"
  unfolding create_name_gba_aimpl_def create_name_gba_alt
  apply (refine_rcg create_graph_aimpl_refine cr_rename_gba_refine)
  by auto

subsection \<open>Refinement to Efficient Data Structures\<close>

subsubsection \<open>Creation of GBA from Nodes\<close>

schematic_goal until_frmlsr_impl_aux:
  assumes [relator_props, simp]: "R=Id"
  shows "(?c,until_frmlsr) 
  \<in> \<langle>(R::(_\<times>_::linorder) set)\<rangle>ltlr_rel \<rightarrow> \<langle>\<langle>R\<rangle>ltlr_rel \<times>\<^sub>r \<langle>R\<rangle>ltlr_rel\<rangle>dflt_rs_rel"
  unfolding until_frmlsr_def
  apply (autoref (keep_goal, trace))
  done
concrete_definition until_frmlsr_impl uses until_frmlsr_impl_aux
lemmas [autoref_rules] = until_frmlsr_impl.refine[OF PREFER_id_D]




schematic_goal build_succ_impl_aux:
  shows "(?c,build_succ) \<in> 
    \<langle>\<langle>Rm,R\<rangle>node_rel\<rangle>list_set_rel 
    \<rightarrow> \<langle>\<langle>nat_rel,\<langle>nat_rel\<rangle>list_set_rel\<rangle>iam_map_rel\<rangle>nres_rel"
  unfolding build_succ_def[abs_def] expand_init_def
  using [[autoref_trace_failed_id]]
  apply (autoref (keep_goal, trace))
  done

concrete_definition build_succ_impl uses build_succ_impl_aux
lemmas [autoref_rules] = build_succ_impl.refine

(* TODO: Post-processing should be on by default! *)
schematic_goal build_succ_code_aux: "RETURN ?c \<le> build_succ_impl x"
  unfolding build_succ_impl_def
  apply (refine_transfer (post))
  done

concrete_definition build_succ_code uses build_succ_code_aux
lemmas [refine_transfer] = build_succ_code.refine




schematic_goal build_F_impl_aux:
  assumes [relator_props]:  "R = Id"
  shows "(?c,build_F) \<in> 
    \<langle>\<langle>Rm,R\<rangle>node_rel\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>\<langle>nat_rel\<rangle>list_set_rel\<rangle>list_set_rel"
  unfolding build_F_def[abs_def]
  using [[autoref_trace_failed_id]]
  apply (autoref (keep_goal, trace))
  done

concrete_definition build_F_impl uses build_F_impl_aux
lemmas [autoref_rules] = build_F_impl.refine[OF PREFER_id_D]




schematic_goal pn_map_impl_aux:
  shows "(?c,pn_map) \<in> 
    \<langle>\<langle>Rm,Id\<rangle>node_rel\<rangle>list_set_rel 
    \<rightarrow> \<langle>\<langle>nat_rel,\<langle>Id\<rangle>list_set_rel \<times>\<^sub>r \<langle>Id\<rangle>list_set_rel\<rangle>iam_map_rel\<rangle>nres_rel"
  unfolding pn_map_def[abs_def] pn_props_def
  using [[autoref_trace_failed_id]]
  apply (autoref (keep_goal, trace))
  done

concrete_definition pn_map_impl uses pn_map_impl_aux
lemma pn_map_impl_autoref[autoref_rules]: 
  assumes "PREFER_id R"
  shows "(pn_map_impl,pn_map) \<in> 
    \<langle>\<langle>Rm,R\<rangle>node_rel\<rangle>list_set_rel 
    \<rightarrow> \<langle>\<langle>nat_rel,\<langle>R\<rangle>list_set_rel \<times>\<^sub>r \<langle>R\<rangle>list_set_rel\<rangle>iam_map_rel\<rangle>nres_rel"
  using assms pn_map_impl.refine by simp

schematic_goal pn_map_code_aux: "RETURN ?c \<le> pn_map_impl x"
  unfolding pn_map_impl_def
  apply (refine_transfer (post))
  done
concrete_definition pn_map_code uses pn_map_code_aux
lemmas [refine_transfer] = pn_map_code.refine 

schematic_goal cr_rename_gba_impl_aux:
  assumes ID[relator_props]: "R=Id"
  notes [autoref_tyrel del] = tyrel_dflt_linorder_set
  notes [autoref_tyrel] = ty_REL[of "\<langle>nat_rel\<rangle>list_set_rel"]
  shows "(?c,cr_rename_gba) \<in> 
    \<langle>\<langle>Rm,R\<rangle>node_rel\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow> (?R::(?'c \<times> _) set)"
  unfolding ID
  unfolding cr_rename_gba_def[abs_def] expand_init_def comp_def
  using [[autoref_trace_failed_id]]
  apply (autoref (keep_goal, trace))
  done
concrete_definition cr_rename_gba_impl uses cr_rename_gba_impl_aux

thm cr_rename_gba_impl.refine

lemma cr_rename_gba_autoref[autoref_rules]:
  assumes "PREFER_id R"
  shows "(cr_rename_gba_impl, cr_rename_gba) \<in> 
    \<langle>\<langle>Rm, R\<rangle>node_rel\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>ltlr_rel \<rightarrow>
    \<langle>gbav_impl_rel_ext unit_rel nat_rel (\<langle>R\<rangle>fun_set_rel)\<rangle>nres_rel"
  using assms cr_rename_gba_impl.refine[of R Rm] by simp


schematic_goal cr_rename_gba_code_aux: "RETURN ?c \<le> cr_rename_gba_impl x y"
  unfolding cr_rename_gba_impl_def
  apply (refine_transfer (post))
  done
concrete_definition cr_rename_gba_code uses cr_rename_gba_code_aux
lemmas [refine_transfer] = cr_rename_gba_code.refine 


subsubsection \<open>Creation of Graph\<close>

text \<open>
  The implementation of the node-set. The relation enforces that there are no
  different nodes with the same name. This effectively establishes an additional
  invariant, made explicit by an assertion in the refined program. This invariant
  allows for a more efficient implementation.
\<close>
definition ls_nds_rel_def_internal: 
  "ls_nds_rel R \<equiv> \<langle>R\<rangle>list_set_rel \<inter> {(_,s). inj_on name s}"
lemma ls_nds_rel_def: "\<langle>R\<rangle>ls_nds_rel = \<langle>R\<rangle>list_set_rel \<inter> {(_,s). inj_on name s}"
  by (simp add: relAPP_def ls_nds_rel_def_internal)

lemmas [autoref_rel_intf] = REL_INTFI[of ls_nds_rel i_set]

lemma ls_nds_rel_sv[relator_props]: 
  assumes "single_valued R" 
  shows "single_valued (\<langle>R\<rangle>ls_nds_rel)"
  using list_set_rel_sv[OF assms]
  unfolding ls_nds_rel_def
  by (metis inf.cobounded1 single_valued_subset)

context begin interpretation autoref_syn .
lemma lsnds_empty_autoref[autoref_rules]:
  assumes "PREFER_id R"
  shows "([],{})\<in>\<langle>R\<rangle>ls_nds_rel"
  using assms
  apply (simp add: ls_nds_rel_def)
  by autoref

lemma lsnds_insert_autoref[autoref_rules]:
  assumes "SIDE_PRECOND (name n \<notin> name`ns)"
  assumes "(n',n)\<in>R"
  assumes "(ns',ns)\<in>\<langle>R\<rangle>ls_nds_rel"
  shows "(n'#ns',(OP insert ::: R \<rightarrow> \<langle>R\<rangle>ls_nds_rel \<rightarrow> \<langle>R\<rangle>ls_nds_rel)$n$ns)
   \<in> \<langle>R\<rangle>ls_nds_rel"
  using assms
  unfolding ls_nds_rel_def
  apply simp
proof (elim conjE, rule conjI)
  assume [autoref_rules]: "(n', n) \<in> R" "(ns', ns) \<in> \<langle>R\<rangle>list_set_rel"
  assume "name n \<notin> name ` ns"
    and "inj_on name ns"
  then have "n \<notin> ns" by (auto)
  then show "(n' # ns', insert n ns) \<in> \<langle>R\<rangle>list_set_rel"
    by autoref
qed auto

lemma ls_nds_image_autoref_aux:
  assumes [autoref_rules]: "(fi,f) \<in> Ra \<rightarrow> Rb"
  assumes "(l,s) \<in> \<langle>Ra\<rangle>ls_nds_rel"
  assumes [simp]: "\<forall>x. name (f x) = name x"
  shows "(map fi l, f`s) \<in> \<langle>Rb\<rangle>ls_nds_rel"
proof -
  from assms have 
    [autoref_rules]: "(l,s)\<in>\<langle>Ra\<rangle>list_set_rel" 
      and INJ: "(inj_on name s)"
    by (auto simp add: ls_nds_rel_def)
  
  have [simp]: "inj_on f s"
    by (rule inj_onI) (metis INJ assms(3) inj_on_eq_iff)

  have "(map fi l, f`s) \<in> \<langle>Rb\<rangle>list_set_rel"
    by (autoref (keep_goal))
  moreover have "inj_on name (f`s)"
    apply (rule inj_onI)
    apply (auto simp: image_iff dest: inj_onD[OF INJ])
    done
  ultimately show ?thesis
    by (auto simp: ls_nds_rel_def)
qed  

lemma ls_nds_image_autoref[autoref_rules]:
  assumes "(fi,f) \<in> Ra \<rightarrow> Rb"
  assumes "SIDE_PRECOND (\<forall>x. name (f x) = name x)"
  shows "(map fi, (OP (`) ::: (Ra\<rightarrow>Rb) \<rightarrow> \<langle>Ra\<rangle>ls_nds_rel \<rightarrow> \<langle>Rb\<rangle>ls_nds_rel)$f) 
    \<in> \<langle>Ra\<rangle>ls_nds_rel \<rightarrow> \<langle>Rb\<rangle>ls_nds_rel"
  using assms
  unfolding autoref_tag_defs
  using ls_nds_image_autoref_aux
  by blast

lemma list_set_autoref_to_list[autoref_ga_rules]: 
  shows "is_set_to_sorted_list (\<lambda>_ _. True) R ls_nds_rel id"
  unfolding is_set_to_list_def is_set_to_sorted_list_def ls_nds_rel_def
    it_to_sorted_list_def list_set_rel_def br_def
  by auto


end

context begin interpretation autoref_syn .
lemma [autoref_itype]:
  "upd_incoming 
    ::\<^sub>i \<langle>Im, I\<rangle>\<^sub>ii_node \<rightarrow>\<^sub>i \<langle>\<langle>Im', I\<rangle>\<^sub>ii_node\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>\<langle>Im', I\<rangle>\<^sub>ii_node\<rangle>\<^sub>ii_set"
  by simp
end

term upd_incoming
schematic_goal upd_incoming_impl_aux:
  assumes "REL_IS_ID R"
  shows "(?c, upd_incoming)\<in>\<langle>Rm1,R\<rangle>node_rel 
  \<rightarrow> \<langle>\<langle>Rm2,R\<rangle>node_rel\<rangle>ls_nds_rel 
  \<rightarrow> \<langle>\<langle>Rm2,R\<rangle>node_rel\<rangle>ls_nds_rel"
  using assms apply simp
  unfolding upd_incoming_def[abs_def]
  using [[autoref_trace_failed_id]]
  apply (autoref (keep_goal))
  done

concrete_definition upd_incoming_impl uses upd_incoming_impl_aux
lemmas [autoref_rules] = upd_incoming_impl.refine[OF PREFER_D[of REL_IS_ID]]


schematic_goal expand_impl_aux: "(?c, expand_aimpl) \<in> 
  \<langle>unit_rel,Id\<rangle>node_rel \<times>\<^sub>r \<langle>\<langle>unit_rel,Id\<rangle>node_rel\<rangle>ls_nds_rel 
  \<rightarrow> \<langle>nat_rel \<times>\<^sub>r \<langle>\<langle>unit_rel,Id\<rangle>node_rel\<rangle>ls_nds_rel\<rangle>nres_rel"
  unfolding expand_aimpl_def[abs_def] expand_new_name_def
  using [[autoref_trace_failed_id, autoref_trace_intf_unif]]
  apply (autoref (trace,keep_goal))
  done

concrete_definition expand_impl uses expand_impl_aux

context begin interpretation autoref_syn .
lemma [autoref_itype]: "expand\<^sub>T 
  ::\<^sub>i \<langle>\<langle>i_unit, I\<rangle>\<^sub>ii_node, \<langle>\<langle>i_unit, I\<rangle>\<^sub>ii_node\<rangle>\<^sub>ii_set\<rangle>\<^sub>ii_prod 
  \<rightarrow>\<^sub>i \<langle>\<langle>i_nat,\<langle>\<langle>i_unit, I\<rangle>\<^sub>ii_node\<rangle>\<^sub>ii_set\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_nres" by simp

lemma expand_autoref[autoref_rules]:
  assumes ID: "PREFER_id R"
  assumes A: "(n_ns', n_ns) 
    \<in> \<langle>unit_rel,R\<rangle>node_rel \<times>\<^sub>r \<langle>\<langle>unit_rel,R\<rangle>node_rel\<rangle>list_set_rel"
  assumes B: "SIDE_PRECOND (
    let (n,ns)=n_ns in inj_on name ns \<and> (\<forall>n'\<in>ns. name n > name n')
  )"
  shows "(expand_impl n_ns', 
    (OP expand_aimpl
    ::: \<langle>unit_rel,R\<rangle>node_rel \<times>\<^sub>r \<langle>\<langle>unit_rel,R\<rangle>node_rel\<rangle>list_set_rel 
    \<rightarrow> \<langle>nat_rel \<times>\<^sub>r \<langle>\<langle>unit_rel,R\<rangle>node_rel\<rangle>list_set_rel\<rangle>nres_rel)$n_ns) 
  \<in> \<langle>nat_rel \<times>\<^sub>r \<langle>\<langle>unit_rel,R\<rangle>node_rel\<rangle>list_set_rel\<rangle>nres_rel"
proof simp
  from ID A B have 
    1: "(n_ns, n_ns) \<in> Id \<inter> {(_,(n,ns)). \<forall>n'\<in>ns. name n > name n'}"
    and 2: "(n_ns', n_ns) 
      \<in> \<langle>unit_rel,Id\<rangle>node_rel \<times>\<^sub>r \<langle>\<langle>unit_rel,Id\<rangle>node_rel\<rangle>ls_nds_rel"
    unfolding ls_nds_rel_def
    apply -
    apply auto []
    apply (cases n_ns')
    apply auto []
    done

  have [simp]: "single_valued (nat_rel \<times>\<^sub>r \<langle>\<langle>unit_rel, Id\<rangle>node_rel\<rangle>list_set_rel)"
    by tagged_solver


  have [relator_props]: "\<And>R. single_valued (Id \<inter> R)"
    by (metis IntE single_valuedD single_valuedI single_valued_Id)
    
  have [simp]: "single_valued ((nat_rel \<times>\<^sub>r \<langle>\<langle>unit_rel, Id\<rangle>node_rel\<rangle>ls_nds_rel) O
                          (Id \<inter> {(_, n, ns). \<forall>n'\<in>ns. name n' < n}))"
    by (tagged_solver)
    
  from expand_impl.refine[THEN fun_relD, OF 2, THEN nres_relD]
  show "(expand_impl n_ns', expand_aimpl n_ns)
    \<in> \<langle>nat_rel \<times>\<^sub>r \<langle>\<langle>unit_rel, R\<rangle>node_rel\<rangle>list_set_rel\<rangle>nres_rel"
    apply -
    apply (rule nres_relI)
    using ID
    apply (simp add: pw_le_iff refine_pw_simps)
    apply (fastforce simp: ls_nds_rel_def)
    done
qed

end


schematic_goal expand_code_aux: "RETURN ?c \<le> expand_impl n_ns"
  unfolding expand_impl_def
  by (refine_transfer the_resI)
concrete_definition expand_code uses expand_code_aux
prepare_code_thms expand_code_def
lemmas [refine_transfer] = expand_code.refine 


schematic_goal create_graph_impl_aux: 
  assumes ID: "R=Id"
  shows "(?c, create_graph_aimpl) 
    \<in> \<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>\<langle>\<langle>unit_rel,R\<rangle>node_rel\<rangle>list_set_rel\<rangle>nres_rel"
  unfolding ID
  unfolding create_graph_aimpl_def[abs_def] expand_init_def expand_new_name_def
  using [[autoref_trace_failed_id]]
  apply (autoref (keep_goal))
  done
concrete_definition create_graph_impl uses create_graph_impl_aux

lemmas [autoref_rules] = create_graph_impl.refine[OF PREFER_id_D]

schematic_goal create_graph_code_aux: "RETURN ?c \<le> create_graph_impl \<phi>" 
  unfolding create_graph_impl_def
  by refine_transfer
concrete_definition create_graph_code uses create_graph_code_aux
lemmas [refine_transfer] = create_graph_code.refine


schematic_goal create_name_gba_impl_aux: 
  "(?c, (create_name_gba_aimpl:: 'a::linorder ltlr \<Rightarrow> _)) 
  \<in> \<langle>Id\<rangle>ltlr_rel \<rightarrow> (?R::(?'c\<times>_) set)"
  unfolding create_name_gba_aimpl_def[abs_def]
  using [[autoref_trace_failed_id]]
  apply (autoref (keep_goal, trace))
  done
concrete_definition create_name_gba_impl uses create_name_gba_impl_aux

lemma create_name_gba_autoref[autoref_rules]:
  assumes "PREFER_id R"
  shows
  "(create_name_gba_impl, create_name_gba)
  \<in> \<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>gbav_impl_rel_ext unit_rel nat_rel (\<langle>R\<rangle>fun_set_rel)\<rangle>nres_rel" 
  (is "_:_\<rightarrow>\<langle>?R\<rangle>nres_rel")
proof (intro fun_relI nres_relI)
  fix \<phi> \<phi>'
  assume A: "(\<phi>,\<phi>')\<in>\<langle>R\<rangle>ltlr_rel"
  from assms have RID[simp]: "R=Id" by simp
    
  note create_name_gba_impl.refine[THEN fun_relD,THEN nres_relD, OF A[unfolded RID]]
  also note create_name_gba_aimpl_refine
  finally show "create_name_gba_impl \<phi> \<le> \<Down> ?R (create_name_gba \<phi>')" by simp
qed
 
schematic_goal create_name_gba_code_aux: "RETURN ?c \<le> create_name_gba_impl \<phi>" 
  unfolding create_name_gba_impl_def
  by (refine_transfer (post))
concrete_definition create_name_gba_code uses create_name_gba_code_aux
lemmas [refine_transfer] = create_name_gba_code.refine

schematic_goal create_name_igba_impl_aux: 
  assumes RID: "R=Id"
  shows "(?c,create_name_igba)\<in>
  \<langle>R\<rangle>ltlr_rel \<rightarrow> \<langle>igbav_impl_rel_ext unit_rel nat_rel (\<langle>R\<rangle>fun_set_rel)\<rangle>nres_rel"
  unfolding RID
  unfolding create_name_igba_def[abs_def]
  using [[autoref_trace_failed_id]]
  apply (autoref (trace, keep_goal))
  done
concrete_definition create_name_igba_impl uses create_name_igba_impl_aux
lemmas [autoref_rules] = create_name_igba_impl.refine[OF PREFER_id_D]

schematic_goal create_name_igba_code_aux: "RETURN ?c \<le> create_name_igba_impl \<phi>" 
  unfolding create_name_igba_impl_def
  by (refine_transfer (post))
concrete_definition create_name_igba_code uses create_name_igba_code_aux
lemmas [refine_transfer] = create_name_igba_code.refine

export_code create_name_igba_code checking SML

end
