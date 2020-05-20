(*  
  Title:    Preference_Profiles_Cmd.thy
  Author:   Manuel Eberl, TU München

  Provides the preference_profile command that defines preference profiles,
  proves well-formedness, and provides some useful lemmas for them.
*)

section \<open>Automatic definition of Preference Profiles\<close>

theory Preference_Profile_Cmd
imports
  Complex_Main
  "../Elections"
keywords
  "preference_profile" :: thy_goal
begin

ML_file \<open>preference_profiles.ML\<close>


context election
begin

lemma preferred_alts_prefs_from_table:
  assumes "prefs_from_table_wf agents alts xs" "i \<in> set (map fst xs)"
  shows   "preferred_alts (prefs_from_table xs i) x = 
             of_weak_ranking_Collect_ge (rev (the (map_of xs i))) x"
proof -
  interpret pref_profile_wf agents alts "prefs_from_table xs"
    by (intro pref_profile_from_tableI assms)
  from assms have [simp]: "i \<in> agents" by (auto simp: prefs_from_table_wf_def)
  have "of_weak_ranking_Collect_ge (rev (the (map_of xs i))) x = 
          Collect (of_weak_ranking (the (map_of xs i)) x)"
    by (rule eval_Collect_of_weak_ranking [symmetric])
  also from assms(2) have "the (map_of xs i) \<in> set (map snd xs)"
    by (cases "map_of xs i") (force simp: map_of_eq_None_iff dest: map_of_SomeD)+
  from prefs_from_table_wfD(5)[OF assms(1) this]
    have "Collect (of_weak_ranking (the (map_of xs i)) x) = 
            {y\<in>alts. of_weak_ranking (the (map_of xs i)) x y}"
    by safe (force elim!: of_weak_ranking.cases)
  also from assms 
    have "of_weak_ranking (the (map_of xs i)) = prefs_from_table xs i"
    by (subst prefs_from_table_map_of[OF assms(1)])
       (auto simp: prefs_from_table_wf_def)
  finally show ?thesis by (simp add: of_weak_ranking_Collect_ge_def preferred_alts_altdef)
qed

lemma favorites_prefs_from_table:
  assumes wf: "prefs_from_table_wf agents alts xs" and i: "i \<in> agents"
  shows   "favorites (prefs_from_table xs) i = hd (the (map_of xs i))"
proof (cases "map_of xs i")
  case None
  with assms show ?thesis
    by (auto simp: map_of_eq_None_iff prefs_from_table_wf_def)
next
  case (Some y)
  with assms have "is_finite_weak_ranking y" "y \<noteq> []"
    by (auto simp: prefs_from_table_wf_def)
  with Some show ?thesis
    unfolding favorites_def using assms
    by (simp add: prefs_from_table_def is_finite_weak_ranking_def 
                  Max_wrt_of_weak_ranking prefs_from_table_wfD)
qed 

lemma has_unique_favorites_prefs_from_table:
  assumes wf: "prefs_from_table_wf agents alts xs"
  shows   "has_unique_favorites (prefs_from_table xs) = 
             list_all (\<lambda>z. is_singleton (hd (snd z))) xs"
proof -
  interpret pref_profile_wf agents alts "prefs_from_table xs"
    by (intro pref_profile_from_tableI assms)
  from wf have "agents = set (map fst xs)" "distinct (map fst xs)"
    by (auto simp: prefs_from_table_wf_def)
  thus ?thesis
    unfolding has_unique_favorites_altdef using assms
    by (auto simp: favorites_prefs_from_table list_all_iff)
qed

end


subsection \<open>Automatic definition of preference profiles from tables\<close>

function favorites_prefs_from_table where
  "i = j \<Longrightarrow> favorites_prefs_from_table ((j,x)#xs) i = hd x"
| "i \<noteq> j \<Longrightarrow> favorites_prefs_from_table ((j,x)#xs) i =
               favorites_prefs_from_table xs i"
| "favorites_prefs_from_table [] i = {}"
  by (metis list.exhaust old.prod.exhaust) auto
termination by lexicographic_order

lemma (in election) eval_favorites_prefs_from_table:
  assumes "prefs_from_table_wf agents alts xs"
  shows   "favorites_prefs_from_table xs i = 
             favorites (prefs_from_table xs) i"
proof (cases "i \<in> agents")
  assume i: "i \<in> agents"
  with assms have "favorites (prefs_from_table xs) i = hd (the (map_of xs i))"
    by (simp add: favorites_prefs_from_table)
  also from assms i have "i \<in> set (map fst xs)"
    by (auto simp: prefs_from_table_wf_def)
  hence "hd (the (map_of xs i)) = favorites_prefs_from_table xs i"
    by (induction xs i rule: favorites_prefs_from_table.induct) simp_all
  finally show ?thesis ..
next
  assume i: "i \<notin> agents"
  with assms have i': "i \<notin> set (map fst xs)"
    by (simp add: prefs_from_table_wf_def)
  hence "map_of xs i = None" 
    by (simp add: map_of_eq_None_iff)
  hence "prefs_from_table xs i = (\<lambda>_ _. False)"
    by (intro ext) (auto simp: prefs_from_table_def)
  hence "favorites (prefs_from_table xs) i = {}"
    by (simp add: favorites_def Max_wrt_altdef)
  also from i' have "\<dots> = favorites_prefs_from_table xs i"
    by (induction xs i rule: favorites_prefs_from_table.induct) simp_all
  finally show ?thesis ..
qed

function weak_ranking_prefs_from_table where
  "i \<noteq> j \<Longrightarrow> weak_ranking_prefs_from_table ((i,x)#xs) j = weak_ranking_prefs_from_table xs j"
| "i = j \<Longrightarrow> weak_ranking_prefs_from_table ((i,x)#xs) j = x"
| "weak_ranking_prefs_from_table [] j = []"
  by (metis list.exhaust old.prod.exhaust) auto
termination by lexicographic_order

lemma eval_weak_ranking_prefs_from_table:
  assumes "prefs_from_table_wf agents alts xs"
  shows   "weak_ranking_prefs_from_table xs i = weak_ranking (prefs_from_table xs i)"
proof (cases "i \<in> agents")
  assume i: "i \<in> agents"
  with assms have "weak_ranking (prefs_from_table xs i) = the (map_of xs i)"
    by (auto simp: prefs_from_table_def prefs_from_table_wf_def weak_ranking_of_weak_ranking
             split: option.splits)
  also from assms i have "i \<in> set (map fst xs)"
    by (auto simp: prefs_from_table_wf_def)
  hence "the (map_of xs i) = weak_ranking_prefs_from_table xs i"
    by (induction xs i rule: weak_ranking_prefs_from_table.induct) simp_all
  finally show ?thesis ..
next
  assume i: "i \<notin> agents"
  with assms have i': "i \<notin> set (map fst xs)"
    by (simp add: prefs_from_table_wf_def)
  hence "map_of xs i = None" 
    by (simp add: map_of_eq_None_iff)
  hence "prefs_from_table xs i = (\<lambda>_ _. False)"
    by (intro ext) (auto simp: prefs_from_table_def)
  hence "weak_ranking (prefs_from_table xs i) = []" by simp
  also from i' have "\<dots> = weak_ranking_prefs_from_table xs i"
    by (induction xs i rule: weak_ranking_prefs_from_table.induct) simp_all
  finally show ?thesis ..
qed

lemma eval_prefs_from_table_aux:
  assumes "R \<equiv> prefs_from_table xs" "prefs_from_table_wf agents alts xs"
  shows   "R i a b \<longleftrightarrow> prefs_from_table xs i a b"
          "a \<prec>[R i] b \<longleftrightarrow> prefs_from_table xs i a b \<and> \<not>prefs_from_table xs i b a"
          "anonymous_profile R = mset (map snd xs)"
          "election agents alts \<Longrightarrow> i \<in> set (map fst xs) \<Longrightarrow> 
             preferred_alts (R i) x = 
             of_weak_ranking_Collect_ge (rev (the (map_of xs i))) x"
          "election agents alts \<Longrightarrow> i \<in> set (map fst xs) \<Longrightarrow>
             favorites R i = favorites_prefs_from_table xs i"
          "election agents alts \<Longrightarrow> i \<in> set (map fst xs) \<Longrightarrow>
             weak_ranking (R i) = weak_ranking_prefs_from_table xs i"
          "election agents alts \<Longrightarrow> i \<in> set (map fst xs) \<Longrightarrow>
             favorite R i = the_elem (favorites_prefs_from_table xs i)"
          "election agents alts \<Longrightarrow> 
             has_unique_favorites R \<longleftrightarrow> list_all (\<lambda>z. is_singleton (hd (snd z))) xs"
  using assms prefs_from_table_wfD[OF assms(2)]
  by (simp_all add: strongly_preferred_def favorite_def anonymise_prefs_from_table
        election.preferred_alts_prefs_from_table election.eval_favorites_prefs_from_table
        election.has_unique_favorites_prefs_from_table eval_weak_ranking_prefs_from_table)

lemma pref_profile_from_tableI':
  assumes "R1 \<equiv> prefs_from_table xss" "prefs_from_table_wf agents alts xss"
  shows   "pref_profile_wf agents alts R1"
  using assms by (simp add: pref_profile_from_tableI)


ML \<open>

signature PREFERENCE_PROFILES_CMD =
sig

type info

val preference_profile : 
  (term * term) * ((binding * (term * term list list) list) list) -> Proof.context -> Proof.state

val preference_profile_cmd : 
  (string * string) * ((binding * (string * string list list) list) list) -> 
    Proof.context -> Proof.state

val get_info : term -> Proof.context -> info
val add_info : term -> info -> Context.generic -> Context.generic
val transform_info : info -> morphism -> info

end

structure Preference_Profiles_Cmd : PREFERENCE_PROFILES_CMD =
struct

open Preference_Profiles


type info = 
  { term : term, def_thm : thm, wf_thm : thm, wf_raw_thm : thm, binding : binding,
    raw : (term * term list list) list, eval_thms : thm list }

fun transform_info ({term = t, binding, def_thm, wf_thm, wf_raw_thm, raw, eval_thms} : info) phi =
    let
      val thm = Morphism.thm phi
      val fact = Morphism.fact phi
      val term = Morphism.term phi
      val bdg = Morphism.binding phi
    in
      { term = term t, binding = bdg binding, def_thm = thm def_thm, wf_thm = thm wf_thm, 
        wf_raw_thm = thm wf_raw_thm, raw = map (fn (a, bss) => (term a, map (map term) bss)) raw,
        eval_thms = fact eval_thms }
    end

structure Data = Generic_Data
(
  type T = (term * info) Item_Net.T
  val empty = Item_Net.init (op aconv o apply2 fst) (single o fst)
  val extend = I
  val merge = Item_Net.merge
);

fun get_info term lthy = 
  Item_Net.retrieve (Data.get (Context.Proof lthy)) term |> the_single |> snd

fun add_info term info lthy =
  Data.map (Item_Net.update (term, info)) lthy
  
fun add_infos infos lthy =
  Data.map (fold Item_Net.update infos) lthy

fun preference_profile_aux agents alts (binding, args) lthy = 
  let
    val dest_Type' = Term.dest_Type #> snd #> hd
    val (agentT, altT) = apply2 (dest_Type' o fastype_of) (agents, alts)
    val alt_setT = HOLogic.mk_setT altT
    fun define t = 
      Local_Theory.define ((binding, NoSyn), 
        ((Binding.suffix_name "_def" binding, @{attributes [code]}), t)) lthy
    val ty = HOLogic.mk_prodT (agentT, HOLogic.listT (HOLogic.mk_setT altT))
    val args' = 
      args |> map (fn x => x ||> map (HOLogic.mk_set altT) ||> HOLogic.mk_list alt_setT)
    val t_raw = 
      args' 
        |> map HOLogic.mk_prod 
        |> HOLogic.mk_list ty
    val t = Const (@{const_name prefs_from_table}, 
              HOLogic.listT ty --> pref_profileT agentT altT) $ t_raw
    val ((prefs, prefs_def), lthy) = define t
    val prefs_from_table_wf_const = 
      Const (@{const_name prefs_from_table_wf}, HOLogic.mk_setT agentT --> HOLogic.mk_setT altT --> 
          HOLogic.listT (HOLogic.mk_prodT (agentT, HOLogic.listT (HOLogic.mk_setT altT))) -->
          HOLogic.boolT)
    val wf_prop = (prefs_from_table_wf_const $ agents $ alts $ t_raw) |> HOLogic.mk_Trueprop

  in
    ((prefs, wf_prop, prefs_def), lthy)
  end

fun fold_accum f xs s =
  let
    fun fold_accum_aux _ [] s acc = (rev acc, s)
      | fold_accum_aux f (x::xs) s acc = 
          case f x s of (y, s') => fold_accum_aux f xs s' (y::acc)
  in
    fold_accum_aux f xs s []
  end

fun preference_profile ((agents, alts), args) lthy =
  let
    fun qualify pref suff = Binding.qualify true (Binding.name_of pref) (Binding.name suff)
    val (results, lthy) = fold_accum (preference_profile_aux agents alts) args lthy
    val prefs_terms = map #1 results
    val wf_props = map #2 results
    val defs = map (snd o #3) results
    val raws = map snd args
    val bindings = map fst args

    fun tac lthy =
       let 
         val lthy' = put_simpset HOL_ss lthy addsimps
           @{thms list.set Union_insert Un_insert_left insert_not_empty Int_empty_left Int_empty_right
              insert_commute Un_empty_left Un_empty_right insert_absorb2 Union_empty
              is_weak_ranking_Cons is_weak_ranking_Nil finite_insert finite.emptyI
              Set.singleton_iff Set.empty_iff Set.ball_simps}
        in
          Local_Defs.unfold_tac lthy defs
            THEN ALLGOALS (resolve_tac lthy [@{thm prefs_from_table_wfI}])
            THEN Local_Defs.unfold_tac lthy @{thms is_finite_weak_ranking_def list.set insert_iff
               empty_iff simp_thms list.map snd_conv fst_conv}
            THEN ALLGOALS (TRY o REPEAT_ALL_NEW (eresolve_tac lthy @{thms disjE}))
            THEN ALLGOALS (TRY o Hypsubst.hyp_subst_tac lthy)
            THEN ALLGOALS (Simplifier.asm_full_simp_tac lthy')
            THEN ALLGOALS (TRY o REPEAT_ALL_NEW (resolve_tac lthy @{thms conjI}))
            THEN distinct_subgoals_tac
        end

    fun after_qed [wf_thms_raw] lthy =
      let
        fun prep_thms attrs suffix (thms : thm list) binding = 
          (((qualify binding suffix, attrs), [(thms,[])]))
        fun prep_thmss simp suffix thmss = map2 (prep_thms simp suffix) thmss bindings
        fun notes thmss suffix attrs lthy = 
            Local_Theory.notes (prep_thmss attrs suffix thmss) lthy |> snd
        fun note thms suffix attrs lthy = notes (map single thms) suffix attrs lthy
        val eval_thmss = map2 (fn def => fn wf => 
          map (fn thm => thm OF [def, wf]) @{thms eval_prefs_from_table_aux}) 
          defs wf_thms_raw
        val wf_thms = map2 (fn def => fn wf => 
          @{thm pref_profile_from_tableI'} OF [def, wf]) defs wf_thms_raw
        val mk_infos =
          let 
            fun aux acc (bdg::bdgs) (t::ts) (r::raws) (def::def_thms) (wf::wf_thms) 
                   (wf_raw::wf_raw_thms) (evals::eval_thmss) =
              aux ((t, {binding = bdg, term = t, raw = r, def_thm = def, wf_thm = wf,
                 wf_raw_thm = wf_raw, eval_thms = evals}) :: acc) 
                 bdgs ts raws def_thms wf_thms wf_raw_thms eval_thmss
            | aux acc [] _ _ _ _ _ _ = (acc : (term * info) list)
            | aux _ _ _ _ _ _ _ _ = raise Match
          in
            aux []
          end
        val infos = mk_infos bindings prefs_terms raws defs wf_thms wf_thms_raw eval_thmss
      in
        lthy 
        |> note wf_thms_raw "wf_raw" []
        |> note wf_thms "wf" @{attributes [simp]} 
        |> notes eval_thmss "eval" []
        |> Local_Theory.declaration {syntax = false, pervasive = false}
             (fn m => add_infos (map (fn (t,i) => (Morphism.term m t, transform_info i m)) infos))
      end
    | after_qed _ _ = raise Match

  in
    Proof.theorem NONE after_qed [map (fn prop => (prop, [])) wf_props] lthy
    |> Proof.refine_singleton (Method.Basic (SIMPLE_METHOD o tac))
  end

fun preference_profile_cmd ((agents, alts), argss) lthy =
  let
    val read = Syntax.read_term lthy
    fun read' ty t = Syntax.parse_term lthy t |> Type.constraint ty |> Syntax.check_term lthy 
    val agents' = read agents
    val alts' = read alts
    val agentT = agents' |> fastype_of |> dest_Type |> snd |> hd
    val altT = alts' |> fastype_of |> dest_Type |> snd |> hd
    fun read_pref_elem ts = map (read' altT) ts
    fun read_prefs prefs = map read_pref_elem prefs
    fun prep (binding, args) = 
      (binding, map (fn (agent, prefs) => (read' agentT agent, read_prefs prefs)) args)
  in
    preference_profile ((agents', alts'), map prep argss) lthy
  end

val parse_prefs = 
  let
    val parse_pref_elem = 
      (Args.bracks (Parse.list1 Parse.term)) ||
      Parse.term >> single
  in
    Parse.list1 parse_pref_elem
  end

val parse_pref_profile =
  Parse.binding --| Args.$$$ "=" -- Scan.repeat1 (Parse.term --| Args.colon -- parse_prefs)

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword preference_profile}
    "construct preference profiles from a table"
    (Args.$$$ "agents" |-- Args.colon |-- Parse.term --| Args.$$$ "alts" --| Args.colon 
       -- Parse.term --| Args.$$$ "where" --
     Parse.and_list1 parse_pref_profile >> preference_profile_cmd);

end
\<close>

end
