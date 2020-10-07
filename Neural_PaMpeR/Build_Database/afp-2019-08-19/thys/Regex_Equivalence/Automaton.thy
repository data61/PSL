(*  Author: Tobias Nipkow, Dmitriy Traytel *)

section "Regular Expressions Equivalence Framework"

(*<*)
theory Automaton
imports "Regular-Sets.Regular_Exp" "HOL-Library.While_Combinator"
begin
(*>*)

primrec add_atoms :: "'a rexp \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "add_atoms Zero = id"
| "add_atoms One = id"
| "add_atoms (Atom a) = List.insert a"
| "add_atoms (Plus r s) = add_atoms s o add_atoms r"
| "add_atoms (Times r s) = add_atoms s o add_atoms r"
| "add_atoms (Star r) = add_atoms r"

lemma set_add_atoms: "set (add_atoms r as) = atoms r \<union> set as"
by (induction r arbitrary: as) auto

lemma rtrancl_fold_product:
shows "{((r,s),(f a r,f a s))| r s a. a : A}^* =
       {((r,s),(fold f w r,fold f w s))| r s w. w : lists A}" (is "?L = ?R")
proof-
  { fix r s r' s'
    have "((r,s),(r',s')) : ?L \<Longrightarrow> ((r,s),(r',s')) : ?R"
    proof(induction rule: converse_rtrancl_induct2)
      case refl show ?case by(force intro!: fold_simps(1)[symmetric])
    next
      case step thus ?case by(force intro!: fold_simps(2)[symmetric])
    qed
  } moreover
  { fix r s r' s'
    { fix w have "\<forall>x\<in>set w. x \<in> A \<Longrightarrow> ((r, s), fold f w r, fold f w s) :?L"
      proof(induction w rule: rev_induct)
        case Nil show ?case by simp
      next
        case snoc thus ?case by (auto elim!: rtrancl_into_rtrancl)
      qed
    } 
    hence "((r,s),(r',s')) : ?R \<Longrightarrow> ((r,s),(r',s')) : ?L" by auto
  } ultimately show ?thesis by (auto simp: in_lists_conv_set) blast
qed

lemma rtrancl_fold_product1:
shows "{(r,s). \<exists>a \<in> A. s = f a r}^* =
       {(r,fold f w r) | r w. w : lists A}" (is "?L = ?R")
proof-
  { fix r s
    have "(r,s) : ?L \<Longrightarrow> (r,s) : ?R"
    proof(induction rule: converse_rtrancl_induct)
      case base show ?case by(force intro!: fold_simps(1)[symmetric])
    next
      case step thus ?case by(force intro!: fold_simps(2)[symmetric])
    qed
  } moreover
  { fix r s
    { fix w have "\<forall>x\<in>set w. x \<in> A \<Longrightarrow> (r, fold f w r) :?L"
      proof(induction w rule: rev_induct)
        case Nil show ?case by simp
      next
        case snoc thus ?case by (auto elim!: rtrancl_into_rtrancl)
      qed
    } 
    hence "(r,s) : ?R \<Longrightarrow> (r,s) : ?L" by auto
  } ultimately show ?thesis by (auto simp: in_lists_conv_set) blast
qed

lemma lang_eq_ext_Nil_fold_Deriv:
  fixes r s
  defines "\<BB> \<equiv> {(fold Deriv w (lang r), fold Deriv w (lang s))| w. w\<in>lists (atoms r \<union> atoms s)}"
  shows "lang r = lang s \<longleftrightarrow> (\<forall>(K, L) \<in> \<BB>. [] \<in> K \<longleftrightarrow> [] \<in> L)"
  unfolding lang_eq_ext \<BB>_def by (subst (1 2) in_fold_Deriv[of "[]", simplified, symmetric]) auto



locale rexp_DA =
fixes init :: "'a rexp \<Rightarrow> 's"
fixes delta :: "'a \<Rightarrow> 's \<Rightarrow> 's"
fixes final :: "'s \<Rightarrow> bool"
fixes L :: "'s \<Rightarrow> 'a lang"
assumes L_init: "L (init r) = lang r"
assumes L_delta: "L(delta a s) = Deriv a (L s)"
assumes final_iff_Nil: "final s \<longleftrightarrow> [] \<in> L s"
begin

lemma L_deltas: "L (fold delta w s) = fold Deriv w (L s)"
  by (induction w arbitrary: s) (auto simp add: L_delta)

definition closure :: "'a list \<Rightarrow> 's * 's \<Rightarrow> (('s * 's) list * ('s * 's) set) option"
where
"closure as = rtrancl_while (\<lambda>(p,q). final p = final q)
          (\<lambda>(p,q). map (\<lambda>a. (delta a p, delta a q)) as)"
(* stop when same opti? *)

theorem closure_sound_complete:
assumes result: "closure as (init r,init s) = Some(ws,R)"
and atoms: "set as = atoms r \<union> atoms s"
shows "ws = [] \<longleftrightarrow> lang r = lang s"
proof -
  have leq: "(lang r = lang s) =
  (\<forall>(r',s') \<in> {((r0,s0),(delta a r0,delta a s0))| r0 s0 a. a : set as}^* `` {(init r,init s)}.
    final r' = final s')"
    by (simp add: atoms rtrancl_fold_product Ball_def lang_eq_ext_Nil_fold_Deriv imp_ex
      L_deltas L_init final_iff_Nil del: Un_iff)
  have "{(x,y). y \<in> set ((\<lambda>(p,q). map (\<lambda>a. (delta a p, delta a q)) as) x)} =
    {((r,s), delta a r, delta a s) |r s a. a \<in> set as}"
    by auto
  with atoms rtrancl_while_Some[OF result[unfolded closure_def]]
  show ?thesis by (auto simp add: leq Ball_def split: if_splits)
qed

subsection \<open>The overall procedure\<close>

definition check_eqv :: "'a rexp \<Rightarrow> 'a rexp \<Rightarrow> bool" where
"check_eqv r s =
  (let as = add_atoms r (add_atoms s [])
   in case closure as (init r, init s) of
     Some([],_) \<Rightarrow> True | _ \<Rightarrow> False)"

lemma soundness: 
assumes "check_eqv r s" shows "lang r = lang s"
proof -
  let ?as = "add_atoms r (add_atoms s [])"
  obtain R where 1: "closure ?as (init r, init s) = Some([],R)"
    using assms by (auto simp: check_eqv_def Let_def split:option.splits list.splits)
  from closure_sound_complete[OF this]
  show "lang r = lang s" by (simp add: set_add_atoms)
qed

(* completeness needs termination of closure, otherwise result could be None *)

text\<open>Auxiliary functions:\<close>
definition reachable :: "'a list \<Rightarrow> 'a rexp \<Rightarrow> 's set" where
"reachable as s =
  snd(the(rtrancl_while (\<lambda>_. True) (\<lambda>s. map (\<lambda>a. delta a s) as) (init s)))"

definition automaton :: "'a list \<Rightarrow> 'a rexp \<Rightarrow> (('s * 'a) * 's) set" where
"automaton as s =
  snd (the
  (let i = init s;
       start = (([i], {i}), {});
       test = \<lambda>((ws, Z), A). ws \<noteq> [];
       step = \<lambda>((ws, Z), A).
         (let s = hd ws;
              new_edges = map (\<lambda>a. ((s, a), delta a s)) as;
              new = remdups (filter (\<lambda>ss. ss \<notin> Z) (map snd new_edges))
         in ((new @ tl ws, set new \<union> Z), set new_edges \<union> A))
  in while_option test step start))"

definition match :: "'a rexp \<Rightarrow> 'a list \<Rightarrow> bool" where
"match s w = final (fold delta w (init s))"

lemma match_correct: "match s w \<longleftrightarrow> w \<in> lang s"
  unfolding match_def
  by (induct w arbitrary: s)
    (auto simp: L_init L_delta in_fold_Deriv final_iff_Nil L_deltas Deriv_def)

end

locale rexp_DFA = rexp_DA +
assumes fin: "finite {fold delta w (init s) | w. True}"
begin

lemma finite_rtrancl_delta_Image:
  "finite ({((r,s),(delta a r,delta a s))| r s a. a : A}^* `` {(init r, init s)})"
  unfolding rtrancl_fold_product Image_singleton
  by (auto intro: finite_subset[OF _ finite_cartesian_product[OF fin fin]])

lemma "termination": "\<exists>st. closure as (init r,init s) = Some st" (is "\<exists>_. closure as ?i = _")
unfolding closure_def proof (rule rtrancl_while_finite_Some)
  show "finite ({(x, st). st \<in> set ((\<lambda>(p,q). map (\<lambda>a. (delta a p, delta a q)) as) x)}\<^sup>* `` {?i})"
    by (rule finite_subset[OF Image_mono[OF rtrancl_mono] finite_rtrancl_delta_Image]) auto
qed

lemma completeness: 
assumes "lang r = lang s" shows "check_eqv r s"
proof -
  let ?as = "add_atoms r (add_atoms s [])"
  obtain ws R where 1: "closure ?as (init r, init s) = Some(ws,R)"
    using "termination" by fastforce
  with closure_sound_complete[OF this] assms
  show "check_eqv r s" by (simp add: check_eqv_def set_add_atoms)
qed

lemma finite_rtrancl_delta_Image1:
  "finite ({(r,s). \<exists>a \<in> A. s = delta a r}^* `` {init r})"
  unfolding rtrancl_fold_product1 by (auto intro: finite_subset[OF _ fin])

lemma reachable: "reachable as r = {fold delta w (init r) | w. w \<in> lists (set as)}"
  and finite_reachable: "finite (reachable as r)"
proof -
  obtain wsZ where *: "rtrancl_while (\<lambda>_. True) (\<lambda>s. map (\<lambda>a. delta a s) as) (init r) = Some wsZ"
    by (atomize_elim,intro rtrancl_while_finite_Some Image_mono rtrancl_mono
      finite_subset[OF _ finite_rtrancl_delta_Image1[of "set as" r]]) auto
  then show "reachable as r = {fold delta w (init r) | w. w \<in> lists (set as)}"
    unfolding reachable_def by (cases wsZ)
      (auto dest!: rtrancl_while_Some split: if_splits simp: rtrancl_fold_product1 image_iff)
  then show "finite (reachable as r)" by (auto intro: finite_subset[OF _ fin])
qed
  
end

(*<*)
end
(*>*)
