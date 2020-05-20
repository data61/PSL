(* Author: Dmitriy Traytel *)

section \<open>Deciding Equivalence of $\Pi$-Extended Regular Expressions\<close>

(*<*)
theory Pi_Equivalence_Checking
imports Pi_Regular_Exp "HOL-Library.While_Combinator" List_More
begin
(*>*)

lemma image2p_in_rel: "BNF_Greatest_Fixpoint.image2p f g (in_rel R) =  in_rel (map_prod f g ` R)"
  unfolding image2p_def fun_eq_iff by auto

lemma image2p_apply: "BNF_Greatest_Fixpoint.image2p f g R x y = (\<exists>x' y'. R x' y' \<and> f x' = x \<and> g y' = y)"
  unfolding image2p_def fun_eq_iff by auto

lemma rtrancl_fold_product:
shows "{((r, s), (f a r, f a s))| r s a. a \<in> A}^* =
       {((r, s), (fold f w r, fold f w s))| r s w. w \<in> lists A}" (is "?L = ?R")
proof-
  { fix x :: "('a \<times> 'a) \<times> 'a \<times> 'a"
    obtain r s r' s' where x: "x = ((r, s), (r', s'))" by (cases x) auto
    have "((r, s), (r', s')) \<in> ?L \<Longrightarrow> ((r, s), (r', s')) \<in> ?R"
    proof(induction rule: converse_rtrancl_induct2)
      case refl show ?case by(force intro!: fold_simps(1)[symmetric])
    next
      case step thus ?case by(force intro!: fold_simps(2)[symmetric])
    qed
    with x have "x \<in> ?L \<Longrightarrow> x \<in> ?R" by simp
  } moreover
  { fix x :: "('a \<times> 'a) \<times> 'a \<times> 'a"
    obtain r s r' s' where x: "x = ((r, s), (r', s'))" by (cases x) auto
    { fix w have "\<forall>x\<in>set w. x \<in> A \<Longrightarrow> ((r, s), fold f w r, fold f w s) \<in> ?L"
      proof(induction w rule: rev_induct)
        case Nil show ?case by simp
      next
        case snoc thus ?case by (auto elim!: rtrancl_into_rtrancl)
      qed
    } 
    hence "((r, s), (r', s')) \<in> ?R \<Longrightarrow> ((r, s), (r', s')) \<in> ?L" by auto
    with x have "x \<in> ?R \<Longrightarrow> x \<in> ?L" by simp
  } ultimately show ?thesis by blast
qed

lemma in_fold_lQuot: "v \<in> fold lQuot w L \<longleftrightarrow> w @ v \<in> L"
  by (induct w arbitrary: L) (simp_all add: lQuot_def)

lemma (in project) lang_eq_ext: "\<lbrakk>wf n r; wf n s\<rbrakk> \<Longrightarrow> (lang n r = lang n s) =
  (\<forall>w \<in> lists(\<Sigma> n). w \<in> lang n r \<longleftrightarrow> w \<in> lang n s)"
  by (auto dest!: lang_subset_lists)

lemma (in project) lang_eq_ext_Nil_fold_Deriv:
  fixes r s n
  assumes WF: "wf n r" "wf n s"
  defines "\<BB> \<equiv> {(fold lQuot w (lang n r), fold lQuot w (lang n s))| w. w\<in>lists (\<Sigma> n)}"
  shows "lang n r = lang n s \<longleftrightarrow> (\<forall>(K, L) \<in> \<BB>. [] \<in> K \<longleftrightarrow> [] \<in> L)"
  unfolding lang_eq_ext[OF WF] \<BB>_def
  by (subst (1 2) in_fold_lQuot[of "[]", simplified, symmetric]) auto

locale rexp_DA = project "set o \<sigma>" wf_atom project lookup
  for \<sigma> :: "nat \<Rightarrow> 'a list"
  and wf_atom :: "nat \<Rightarrow> 'b :: linorder \<Rightarrow> bool"
  and project :: "'a \<Rightarrow> 'a"
  and lookup :: "'b \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes init :: "'b rexp \<Rightarrow> 's"
  fixes delta :: "'a \<Rightarrow> 's \<Rightarrow> 's"
  fixes final :: "'s \<Rightarrow> bool"
  fixes wf_state :: "'s \<Rightarrow> bool"
  fixes post :: "'s \<Rightarrow> 's"
  fixes L :: "'s \<Rightarrow> 'a lang"
  fixes n :: "nat"
  assumes L_init[simp]: "wf n r \<Longrightarrow> L (init r) = lang n r"
  assumes L_delta[simp]: "\<lbrakk>a \<in> set (\<sigma> n); wf_state s\<rbrakk> \<Longrightarrow> L (delta a s) = lQuot a (L s)"
  assumes final_iff_Nil[simp]: "final s \<longleftrightarrow> [] \<in> L s"
  assumes L_wf_state[dest]: "wf_state s \<Longrightarrow> L s \<subseteq> lists (set (\<sigma> n))"
  assumes init_wf_state[simp]: "wf n r \<Longrightarrow> wf_state (init r)"
  assumes delta_wf_state[simp]: "\<lbrakk>a \<in> set (\<sigma> n); wf_state s\<rbrakk> \<Longrightarrow> wf_state (delta a s)"
  assumes L_post[simp]: "wf_state s \<Longrightarrow> L (post s) = L s"
  assumes wf_state_post[simp]: "wf_state s \<Longrightarrow> wf_state (post s)"
begin

lemma L_deltas[simp]: "\<lbrakk>wf_word n w; wf_state s\<rbrakk> \<Longrightarrow> L (fold delta w s) = fold lQuot w (L s)"
  by (induction w arbitrary: s) auto

definition progression (infix "\<rightarrow>" 60) where 
  "R \<rightarrow> S = (\<forall>s1 s2. R s1 s2 \<longrightarrow> wf_state s1 \<and> wf_state s2 \<and> final s1 = final s2 \<and>
     (\<forall>x \<in> set (\<sigma> n). BNF_Greatest_Fixpoint.image2p post post S (post (delta x s1)) (post (delta x s2))))"

lemma SUPR_progression[intro!]: "\<forall>n. \<exists>m. X n \<rightarrow> Y m \<Longrightarrow> (SUP n. X n) \<rightarrow> (SUP n. Y n)"
  unfolding progression_def image2p_def by fastforce

definition bisimulation where
  "bisimulation R = R \<rightarrow> R"

definition bisimulation_upto where
  "bisimulation_upto R f = R \<rightarrow> f R"

declare image2pI[intro!] image2pE[elim!]
lemmas bisim_def = bisimulation_def progression_def
lemmas bisim_upto_def = bisimulation_upto_def progression_def

definition compatible where
  "compatible f = (mono f \<and> (\<forall>R S. R \<rightarrow> S \<longrightarrow> f R \<rightarrow> f S))"

lemmas compat_def = compatible_def progression_def

lemma bisimulation_upto_bisimulation:
  assumes "compatible f" "bisimulation_upto R f"
  obtains S where "bisimulation S" "R \<le> S"
proof
  { fix n from assms have "(f^^n) R \<rightarrow> (f^^Suc n) R"
     by (induct n) (auto simp: bisimulation_upto_def compatible_def) }
  then show "bisimulation (SUP n. (f^^n) R)"
    unfolding bisimulation_def by (auto simp del: funpow.simps)
  show "R \<le> (SUP n. (f^^n) R)" by (auto intro!: exI[of _ 0])
qed

lemma bisimulation_eqL: "bisimulation (\<lambda>s1 s2. wf_state s1 \<and> wf_state s2 \<and> L s1 = L s2)"
  unfolding bisim_def by (auto simp: lQuot_def)

lemma coinduction:
  assumes bisim[unfolded bisim_def]: "bisimulation R" and
    WF: "wf_state s1" "wf_state s2" and R: "R s1 s2"
  shows "L s1 = L s2"
proof (rule set_eqI)
  fix w
  from R WF show "w \<in> L s1 \<longleftrightarrow> w \<in> L s2"
  proof (induction w arbitrary: s1 s2)
    case Nil then show ?case using bisim by simp
  next
    case (Cons a w s1 s2)
    show ?case
    proof cases
      assume a: "a \<in> set (\<sigma> n)"
      with \<open>R s1 s2\<close> obtain s1' s2' where "R s1' s2'" "wf_state s1'" "wf_state s2'" and
        *[symmetric]: "post s1' = post (delta a s1)"  "post s2' = post (delta a s2)"
        using bisim unfolding image2p_apply by blast
      then have "w \<in> L (post (delta a s1)) \<longleftrightarrow> w \<in> L (post (delta a s2))"
        unfolding * using Cons.IH[of s1' s2'] by simp
      with a Cons.prems(2,3) show ?case by (simp add: lQuot_def)
    next
      assume "a \<notin> set (\<sigma> n)"
      thus ?case using Cons.prems bisim by force
    qed
  qed
qed

lemma coinduction_upto:
  assumes "bisimulation_upto R f" and WF: "wf_state s1" "wf_state s2" and "R s1 s2" "compatible f"
  shows "L s1 = L s2"
proof (rule bisimulation_upto_bisimulation[OF assms(5,1)])
  fix S assume "R \<le> S"
  assume "bisimulation S"
  then show "L s1 = L s2"
  proof (rule coinduction[OF _ WF])
    from \<open>R \<le> S\<close> \<open>R s1 s2\<close> show "S s1 s2" by blast
  qed
qed

fun test_invariant where
  "test_invariant (ws, _ :: ('s \<times> 's) list , _ :: 's rel) = (case ws of [] \<Rightarrow>  False | (w::'a list,p,q)#_ \<Rightarrow> final p = final q)"
fun test where "test (ws, _ :: 's rel) = (case ws of [] \<Rightarrow>  False | (p,q)#_ \<Rightarrow> final p = final q)"

fun step_invariant where "step_invariant (ws, ps, N) =
    (let
      (w, r, s) = hd ws;
      ps' = (r, s) # ps;
      succs = map (\<lambda>a.
        let r' = delta a r; s' = delta a s
        in ((a # w, r', s'), (post r', post s'))) (\<sigma> n);
      new = remdups' snd (filter (\<lambda>(_, rs). rs \<notin> N) succs);
      ws' = tl ws @ map fst new;
      N' = set (map snd new) \<union> N
    in (ws', ps', N'))"

fun step where "step (ws, N) =
    (let
      (r, s) = hd ws;
      succs = map (\<lambda>a.
        let r' = delta a r; s' = delta a s
        in ((r', s'), (post r', post s'))) (\<sigma> n);
      new = remdups' snd (filter (\<lambda>(_, rs). rs \<notin> N) succs)
    in (tl ws @ map fst new, set (map snd new) \<union> N))"

definition closure_invariant where "closure_invariant = while_option test_invariant step_invariant"
definition closure where "closure = while_option test step"

definition invariant where
  "invariant r s = (\<lambda>(ws, ps, N).
     (r, s) \<in> snd ` set ws \<union> set ps \<and>
     distinct (map snd ws @ ps) \<and>
     bij_betw (map_prod post post) (set (map snd ws @ ps)) N \<and>
     (\<forall>(w, r', s') \<in> set ws. fold delta (rev w) r = r' \<and> fold delta (rev w) s = s' \<and>
        wf_word n (rev w) \<and> wf_state r' \<and> wf_state s') \<and>
     (\<forall>(r', s') \<in> set ps. (\<exists>w. fold delta w r = r' \<and> fold delta w s = s') \<and>
       wf_state r' \<and> wf_state s' \<and> (final r' \<longleftrightarrow> final s') \<and>
       (\<forall>a\<in>set (\<sigma> n). (post (delta a r'), post (delta a s')) \<in> N)))"

lemma invariant_start:
  "\<lbrakk>wf_state r; wf_state s\<rbrakk> \<Longrightarrow> invariant r s ([([], r, s)], [], {(post r, post s)})"
  by (auto simp add: invariant_def bij_betw_def)

lemma step_invariant_mono:
  assumes "step_invariant (ws, ps, N) = (ws', ps', N')"
  shows "snd ` set ws \<union> set ps \<subseteq> snd ` set ws' \<union> set ps'"
using assms proof (intro subsetI, elim UnE)
  fix x assume "x \<in> snd `set ws"
  with assms show "x \<in> snd ` set ws' \<union> set ps'"
  proof (cases "x = snd (hd ws)")
    case False with \<open>x \<in> image snd (set ws)\<close> have "x \<in> snd ` set (tl ws)" by (cases ws) auto
    with assms show ?thesis by (auto split: prod.splits simp: Let_def)
  qed (auto split: prod.splits simp: Let_def)
qed (auto split: prod.splits simp: Let_def)

lemma step_invatiant_unfold: "step_invariant (w # ws, ps, N) = (ws', ps', N') \<Longrightarrow> (\<exists>xs r s.
  w = (xs, r, s) \<and> ps' = (r, s) # ps \<and>
  ws' = ws @ remdups' (map_prod post post o snd) (filter (\<lambda>(_, p). map_prod post post p \<notin> N)
   (map (\<lambda>a. (a#xs, delta a r, delta a s)) (\<sigma> n))) \<and>
  N' = set (map (\<lambda>a. (post (delta a r), post (delta a s))) (\<sigma> n)) \<union> N)"
  by (auto split: prod.splits dest!: mp_remdups'
  simp: Let_def filter_map set_n_lists image_Collect image_image comp_def)

lemma invariant: "invariant r s st \<Longrightarrow> test_invariant st \<Longrightarrow> invariant r s (step_invariant st)"
proof (unfold invariant_def, (split prod.splits)+, elim case_prodE conjE, clarify, intro allI impI conjI)
  fix ws ps N ws' ps' N'
  assume test_invariant: "test_invariant (ws, ps, N)"
  and step_invariant: "step_invariant (ws, ps, N) = (ws', ps', N')"
  and rs: "(r, s) \<in> snd ` set ws \<union> set ps"
  and distinct: "distinct (map snd ws @ ps)"
  and bij: "bij_betw (map_prod post post) (set (map snd ws @ ps)) N"
  and ws: "\<forall>(w, r', s') \<in> set ws. fold delta (rev w) r = r' \<and> fold delta (rev w) s = s' \<and>
    wf_word n (rev w) \<and> wf_state r' \<and> wf_state s'"
      (is "\<forall>(w, r', s') \<in> set ws. ?ws w r' s'")
  and ps: "\<forall>(r', s') \<in> set ps. (\<exists>w. fold delta w r = r' \<and> fold delta w s = s') \<and>
    wf_state r' \<and> wf_state s' \<and> (final r' \<longleftrightarrow> final s') \<and>
    (\<forall>a\<in>set (\<sigma> n). (post (delta a r'), post (delta a s')) \<in> N)"
      (is "\<forall>(r, s) \<in> set ps. ?ps r s N")
  from test_invariant obtain x xs where ws_Cons: "ws = x # xs" by (cases ws) auto
  obtain w r' s' where x: "x = (w, r', s')" and ps': "ps' = (r', s') # ps"
    and ws': "ws' = xs @ remdups' (map_prod post post o snd)
      (filter (\<lambda>(_, p). map_prod post post p \<notin> N)
        (map (\<lambda>a. (a # w, delta a r',  delta a s')) (\<sigma> n)))"
    and N': "N' = (set (map (\<lambda>a. (post (delta a r'), post (delta a s'))) (\<sigma> n)) - N) \<union> N"
    using step_invatiant_unfold[OF step_invariant[unfolded ws_Cons]] by blast
  hence ws'ps': "set (map snd ws' @ ps') =
     set (remdups' (map_prod post post) (filter (\<lambda>p. map_prod post post p \<notin> N)
    (map (\<lambda>a. (delta a r',  delta a s')) (\<sigma> n)))) \<union> (set (map snd ws @ ps))"
    unfolding ws' ps' ws_Cons x by (auto dest!: mp_remdups' simp: filter_map image_image image_Un o_def)
  from rs step_invariant show "(r, s) \<in> snd ` set ws' \<union> set ps'" by (blast dest: step_invariant_mono)
(*next*)
  from distinct ps' ws' ws_Cons x bij show "distinct (map snd ws' @ ps')"
    by (auto simp: bij_betw_def
      intro!: imageI[of _ _ "map_prod post post"] distinct_remdups'_strong
        map_prod_imageI[of _ _ _ post post]
      dest!: mp_remdups'
      elim: image_eqI[of _ snd, OF sym[OF snd_conv]])
(*next*)
  from ps' ws' N' ws x bij show "bij_betw (map_prod post post) (set (map snd ws' @ ps')) N'"
  unfolding ws'ps' N' by (intro bij_betw_combine[OF _ bij]) (auto simp: bij_betw_def map_prod_def)
(*next*)
  from ws x ws_Cons have wr's': "?ws w r' s'" by auto
  with ws ws_Cons show "\<forall>(w, r', s') \<in> set ws'. ?ws w r' s'" unfolding ws'
    by (auto dest!: mp_remdups' elim!: subsetD)
(*next*)
  from ps wr's' test_invariant[unfolded ws_Cons x] show "\<forall>(r', s') \<in> set ps'. ?ps r' s' N'" unfolding ps' N'
    by (fastforce simp: image_Collect)
qed

lemma step_commute: "ws \<noteq> [] \<Longrightarrow>
  (case step_invariant (ws, ps, N) of (ws', ps', N') \<Rightarrow> (map snd ws', N')) = step (map snd ws, N)"
apply (auto split: prod.splits)
   apply (auto simp only: step_invariant.simps step.simps Let_def map_apfst_remdups' filter_map list.map_comp apfst_def map_prod_def snd_conv id_def)
   apply (auto simp: filter_map comp_def map_tl hd_map)
 apply (intro image_eqI, auto)+
done

lemma closure_invariant_closure:
  "map_option (\<lambda>(ws, ps, N). (map snd ws, N)) (closure_invariant (ws, ps, N)) = closure (map snd ws, N)"
  unfolding closure_invariant_def closure_def
  by (rule trans[OF while_option_commute[of _ test _ _ "step"]])
   (auto split: list.splits simp del: step_invariant.simps step.simps list.map simp: step_commute)

lemma
  assumes result: "closure_invariant ([([], init r, init s)], [], {(post (init r), post (init s))}) =
    Some(ws, ps, N)" (is "closure_invariant ([([], ?r, ?s)], _) = _")
  and WF: "wf n r" "wf n s"
  shows closure_invariant_sound: "ws = [] \<Longrightarrow> lang n r = lang n s" and
    counterexample: "ws \<noteq> [] \<Longrightarrow> rev (fst (hd ws)) \<in> lang n r \<longleftrightarrow> rev (fst (hd ws)) \<notin> lang n s"
proof -
  from WF have wf_state: "wf_state ?r" "wf_state ?s" by simp_all
  from invariant invariant_start[OF wf_state] have invariant_ps: "invariant ?r ?s (ws, ps, N)"
    by (rule while_option_rule[OF _ result[unfolded closure_invariant_def]])
  { assume "ws = []"
    with invariant_ps have "bisimulation (in_rel (set ps))" "(?r, ?s) \<in> set ps"
      by (auto simp: bij_betw_def invariant_def bisimulation_def progression_def image2p_in_rel)
    with wf_state have "L ?r = L ?s" by (auto dest: coinduction)
    with WF show "lang n r = lang n s" by simp
  }
  { assume "ws \<noteq> []"
    then obtain w r' s' ws' where ws: "ws = (w, r', s') # ws'" by (cases ws) auto
    with invariant_ps have "r' = fold delta (rev w) (init r)" "s' = fold delta (rev w) (init s)"
      "wf_word n (rev w)" unfolding invariant_def by auto
    moreover have "\<not> test_invariant ((w, r', s') # ws', ps, N)"
      by (rule while_option_stop[OF result[unfolded ws closure_invariant_def]])
    ultimately have "rev (fst (hd ws)) \<in> L ?r \<longleftrightarrow> rev (fst (hd ws)) \<notin> L ?s"
      unfolding ws using wf_state by (simp add: in_fold_lQuot)
    with WF show "rev (fst (hd ws)) \<in> lang n r \<longleftrightarrow> rev (fst (hd ws)) \<notin> lang n s" by simp
  }
qed

lemma closure_sound:
  assumes result: "closure ([(init r, init s)], {(post (init r), post (init s))}) = Some ([], N)"
  and WF: "wf n r" "wf n s"
  shows "lang n r = lang n s"
  using trans[OF closure_invariant_closure[of "[([], init r, init s)]", simplified] result]
  by (auto dest: closure_invariant_sound[OF _ WF])

definition check_eqv where
  "check_eqv r s =
    (let r' = init r; s' = init s in (case closure ([(r', s')], {(post r', post s')}) of
       Some ([], _) \<Rightarrow> True | _ \<Rightarrow> False))"

lemma check_eqv_sound:
  assumes "check_eqv r s" and WF: "wf n r" "wf n s"
  shows "lang n r = lang n s"
  using closure_sound assms
  by (auto simp: check_eqv_def Let_def split: option.splits list.splits)

definition counterexample where
  "counterexample r s =
    (let r' = init r; s' = init s in (case closure_invariant ([([], r', s')], [], {(post r', post s')}) of
       Some((w,_,_) # _, _) \<Rightarrow> Some (rev w) | _ => None))"

lemma counterexample_sound:
  assumes result: "counterexample r s = Some w"  and WF: "wf n r" "wf n s"
  shows "w \<in> lang n r \<longleftrightarrow> w \<notin> lang n s"
  using assms unfolding counterexample_def Let_def
  by (auto dest!: counterexample[of r s] split: option.splits list.splits)

text\<open>Auxiliary exacutable functions:\<close>

definition reachable :: "'b rexp \<Rightarrow> 's set" where
  "reachable s = snd (the (rtrancl_while (\<lambda>_. True) (\<lambda>s. map (\<lambda>a. post (delta a s)) (\<sigma> n)) (init s)))"

definition automaton :: "'b rexp \<Rightarrow> (('s * 'a) * 's) set" where
  "automaton s =
    snd (the
    (let i = init s;
         start = (([i], {post i}), {});
         test_invariant = \<lambda>((ws, Z), A). ws \<noteq> [];
         step_invariant = \<lambda>((ws, Z), A).
           (let s = hd ws;
                new_edges = map (\<lambda>a. ((s, a), delta a s)) (\<sigma> n);
                new = remdups (filter (\<lambda>ss. post ss \<notin> Z) (map snd new_edges))
           in ((new @ tl ws, post ` set new \<union> Z), set new_edges \<union> A))
    in while_option test_invariant step_invariant start))"

definition match :: "'b rexp \<Rightarrow> 'a list \<Rightarrow> bool" where
  "match s w = final (fold delta w (init s))"

lemma match_correct: "\<lbrakk>wf_word n w; wf n s\<rbrakk> \<Longrightarrow> match s w \<longleftrightarrow> w \<in> lang n s"
  unfolding match_def
  by (induct w arbitrary: s) (auto simp: in_fold_lQuot lQuot_def)

end

locale rexp_DFA = rexp_DA \<sigma> wf_atom project lookup init delta final wf_state post L n
  for \<sigma> :: "nat \<Rightarrow> 'a list"
  and wf_atom :: "nat \<Rightarrow> 'b :: linorder \<Rightarrow> bool"
  and project :: "'a \<Rightarrow> 'a"
  and lookup :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  and init :: "'b rexp \<Rightarrow> 's"
  and delta :: "'a \<Rightarrow> 's \<Rightarrow> 's"
  and final :: "'s \<Rightarrow> bool"
  and wf_state :: "'s \<Rightarrow> bool"
  and post :: "'s \<Rightarrow> 's"
  and L :: "'s \<Rightarrow> 'a lang"
  and n :: nat +
assumes fin: "finite {fold delta w (init s) | w. True}"
begin

abbreviation "Reachable s \<equiv> {fold delta w (init s) | w. True}"

lemma closure_invariant_termination:
  assumes WF: "wf n r" "wf n s"
  and result: "closure_invariant ([([], init r, init s)], [], {(post (init r), post (init s))}) = None"
    (is "closure_invariant ([([], ?r, ?s)], _) = None" is "?cl = None")
  shows "False"
proof -
  let ?D =  "post ` Reachable r \<times> post ` Reachable s"
  let ?X = "\<lambda>ps. ?D - map_prod post post ` set ps"
  let ?f = "\<lambda>(ws, ps, N). card (?X ps)"
  have "\<exists>st. ?cl = Some st" unfolding closure_invariant_def
  proof (rule measure_while_option_Some[of "invariant ?r ?s" _ _ ?f], intro conjI)
    fix st assume base: "invariant ?r ?s st" and "test_invariant st"
    hence step: "invariant ?r ?s (step_invariant st)" by (rule invariant)
    obtain ws ps N where st: "st = (ws, ps, N)" by (cases st) blast
    hence "finite (?X ps)" by (blast intro: finite_cartesian_product fin)
    moreover obtain ws' ps' N' where step_invariant: "step_invariant (ws, ps, N) = (ws', ps', N')"
      by (cases "step_invariant (ws, ps, N)") blast
    moreover
    { have "map_prod post post ` set ps \<subseteq> ?D" using base[unfolded st invariant_def] by fast
      moreover
      have "map_prod post post ` set ps' \<subseteq> ?D" using step[unfolded st step_invariant invariant_def]
        by fast
      moreover
      { have "distinct (map snd ws @ ps)" "inj_on (map_prod post post) (set (map snd ws @ ps))"
          using base[unfolded st invariant_def] by (auto simp: bij_betw_def)
        hence "distinct (map (map_prod post post) (map snd ws @ ps))" unfolding distinct_map ..
        hence "map_prod post post ` set ps \<subset> map_prod post post ` set (snd (hd ws) # ps)"
          using \<open>test_invariant st\<close> st by (cases ws) (simp_all, blast)
        moreover have "map_prod post post ` set ps' = map_prod post post ` set (snd (hd ws) # ps)"
          using step_invariant by (auto split: prod.splits)
        ultimately have "map_prod post post ` set ps \<subset> map_prod post post ` set ps'" by simp
      }
      ultimately have "?X ps' \<subset> ?X ps" by (auto simp add: image_set simp del: set_map)
    }
    ultimately show "?f (step_invariant st) < ?f st" unfolding st step_invariant
      using psubset_card_mono[of "?X ps" "?X ps'"] by simp
  qed (auto simp add: invariant_start WF invariant)
  then show False using result by auto
qed

lemma closure_termination:
  assumes WF: "wf n r" "wf n s"
  and result: "closure ([(init r, init s)], {(post (init r), post (init s))}) = None"
  shows "False"
  using trans[OF closure_invariant_closure[of "[([], init r, init s)]", simplified] result]
  by (auto intro: closure_invariant_termination[OF WF])

lemma closure_invariant_complete:
  assumes eq: "lang n r = lang n s"
  and WF:  "wf n r" "wf n s"
  shows "\<exists>ps N. closure_invariant ([([], init r, init s)], [], {(post (init r), post (init s))}) =
    Some([], ps, N)" (is "\<exists>_ _. closure_invariant ([([], ?r, ?s)], _) = _" is "\<exists>_ _. ?cl = _")
proof (cases ?cl)
  case (Some st)
  moreover obtain ws ps N where ws_ps_N: "st = (ws, ps, N)" by (cases st) blast
  ultimately show ?thesis
  proof (cases ws)
    case (Cons wrs ws)
    with Some obtain w where "counterexample r s = Some w" unfolding counterexample_def
      by (cases wrs) (auto simp: ws_ps_N)
    with eq counterexample_sound[OF _ WF] show ?thesis by blast
  qed blast
qed (auto intro: closure_invariant_termination[OF WF])

lemma closure_complete:
  assumes "lang n r = lang n s" "wf n r" "wf n s"
  shows "\<exists>N. closure ([(init r, init s)], {(post (init r), post (init s))}) = Some ([], N)"
  using closure_invariant_complete[OF assms]
  by (subst closure_invariant_closure[of "[([], init r, init s)]", simplified, symmetric]) auto

lemma check_eqv_complete:
  assumes "lang n r = lang n s" "wf n r" "wf n s"
  shows "check_eqv r s"
  using closure_complete[OF assms] by (auto simp: check_eqv_def)

lemma counterexample_complete:
  assumes "lang n r \<noteq> lang n s" and WF: "wf n r" "wf n s"
  shows "\<exists>w. counterexample r s = Some w"
  using closure_invariant_sound[OF _ WF] closure_invariant_termination[OF WF] assms
  by (fastforce simp: counterexample_def Let_def split: option.splits list.splits)

end

locale rexp_DA_no_post = rexp_DA \<sigma> wf_atom project lookup init delta final wf_state id L n
  for \<sigma> :: "nat \<Rightarrow> 'a list"
  and wf_atom :: "nat \<Rightarrow> 'b :: linorder \<Rightarrow> bool"
  and project :: "'a \<Rightarrow> 'a"
  and lookup :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  and init :: "'b rexp \<Rightarrow> 's"
  and delta :: "'a \<Rightarrow> 's \<Rightarrow> 's"
  and final :: "'s \<Rightarrow> bool"
  and wf_state :: "'s \<Rightarrow> bool"
  and L :: "'s \<Rightarrow> 'a lang"
  and n :: nat
begin

lemma step_efficient[code]: "step (ws, N) =
  (let
    (r, s) = hd ws;
    new = remdups (filter (\<lambda>(r,s). (r,s) \<notin> N) (map (\<lambda>a. (delta a r, delta a s)) (\<sigma> n)))
  in (tl ws @ new, set new \<union> N))"
  by (force simp: Let_def map_apfst_remdups' filter_map o_def split: prod.splits)

end

locale rexp_DFA_no_post = rexp_DFA \<sigma> wf_atom project lookup init delta final wf_state id L
  for \<sigma> :: "nat \<Rightarrow> 'a list"
  and wf_atom :: "nat \<Rightarrow> 'b :: linorder \<Rightarrow> bool"
  and project :: "'a \<Rightarrow> 'a"
  and lookup :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  and init :: "'b rexp \<Rightarrow> 's"
  and delta :: "'a \<Rightarrow> 's \<Rightarrow> 's"
  and final :: "'s \<Rightarrow> bool"
  and wf_state :: "'s \<Rightarrow> bool"
  and L :: "'s \<Rightarrow> 'a lang"
begin

sublocale rexp_DA_no_post by unfold_locales

end

locale rexp_DA_sim = project "set o \<sigma>" wf_atom project lookup
  for \<sigma> :: "nat \<Rightarrow> 'a list"
  and wf_atom :: "nat \<Rightarrow> 'b :: linorder \<Rightarrow> bool"
  and project :: "'a \<Rightarrow> 'a"
  and lookup :: "'b \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes init :: "'b rexp \<Rightarrow> 's"
  fixes sim_delta :: "'s \<Rightarrow> 's list"
  fixes final :: "'s \<Rightarrow> bool"
  fixes wf_state :: "'s \<Rightarrow> bool"
  fixes L :: "'s \<Rightarrow> 'a lang"
  fixes post :: "'s \<Rightarrow> 's"
  fixes n :: nat
  assumes L_init[simp]: "wf n r \<Longrightarrow> L (init r) = lang n r"
  assumes final_iff_Nil[simp]: "final s \<longleftrightarrow> [] \<in> L s"
  assumes L_wf_state[dest]: "wf_state s \<Longrightarrow> L s \<subseteq> lists (set (\<sigma> n))"
  assumes init_wf_state[simp]: "wf n r \<Longrightarrow> wf_state (init r)"
  assumes L_post[simp]: "wf_state s \<Longrightarrow> L (post s) = L s"
  assumes wf_state_post[simp]: "wf_state s \<Longrightarrow> wf_state (post s)"
  assumes L_sim_delta[simp]: "wf_state s \<Longrightarrow> map L (sim_delta s) = map (\<lambda>a. lQuot a (L s)) (\<sigma> n)"
  assumes sim_delta_wf_state[simp]: "wf_state s \<Longrightarrow> \<forall>s' \<in> set (sim_delta s). wf_state s'"
begin

definition "delta a s = sim_delta s ! index (\<sigma> n) a"

lemma length_sim_delta[simp]: "wf_state s \<Longrightarrow> length (sim_delta s) = length (\<sigma> n)"
  by (metis L_sim_delta length_map)

lemma L_delta[simp]: "\<lbrakk>a \<in> set (\<sigma> n); wf_state s\<rbrakk> \<Longrightarrow> L (delta a s) = lQuot a (L s)"
  using L_sim_delta[of s] unfolding delta_def in_set_conv_nth
  by (subst (asm) list_eq_iff_nth_eq) auto

lemma delta_wf_state[simp]: "\<lbrakk>a \<in> set (\<sigma> n); wf_state s\<rbrakk> \<Longrightarrow> wf_state (delta a s)"
  unfolding delta_def by (auto intro: bspec[OF sim_delta_wf_state nth_mem])


sublocale rexp_DA \<sigma> wf_atom project lookup init delta final wf_state post L
  by unfold_locales auto

sublocale rexp_DA_sim_no_post: rexp_DA_no_post \<sigma> wf_atom project lookup init delta final wf_state L
  by unfold_locales auto

end

(*<*)
end
(*>*)
