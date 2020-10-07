theory Worklist
imports "HOL-Library.While_Combinator" RTranCl Quasi_Order
begin

definition
  worklist_aux :: "('s \<Rightarrow> 'a \<Rightarrow> 'a list) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's)
    \<Rightarrow> 'a list * 's \<Rightarrow> ('a list * 's)option"
where
"worklist_aux succs f =
 while_option 
   (\<lambda>(ws,s). ws \<noteq> [])
   (\<lambda>(ws,s). case ws of x#ws' \<Rightarrow> (succs s x @ ws', f x s))"

definition worklist :: "('s \<Rightarrow> 'a \<Rightarrow> 'a list) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's)
    \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 's option" where
"worklist succs f ws s =
  (case worklist_aux succs f (ws,s) of
     None \<Rightarrow> None | Some(ws,s) \<Rightarrow> Some s)"

lemma worklist_aux_Nil: "worklist_aux succs f ([],s) = Some([],s)"
by(simp add: worklist_aux_def while_option_unfold)

lemma worklist_aux_Cons:
 "worklist_aux succs f (x#ws',s) = worklist_aux succs f (succs s x @ ws', f x s)"
by(simp add: worklist_aux_def while_option_unfold)

lemma worklist_aux_unfold[code]:
 "worklist_aux succs f (ws,s) =
 (case ws of [] \<Rightarrow> Some([],s)
  | x#ws' \<Rightarrow> worklist_aux succs f (succs s x @ ws', f x s))"
by(simp add: worklist_aux_Nil worklist_aux_Cons split: list.split)

definition
  worklist_tree_aux :: "('a \<Rightarrow> 'a list) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's)
    \<Rightarrow> 'a list * 's \<Rightarrow> ('a list * 's)option"
where
"worklist_tree_aux succs = worklist_aux (\<lambda>s. succs)"

lemma worklist_tree_aux_unfold[code]:
"worklist_tree_aux succs f (ws,s) =
 (case ws of [] \<Rightarrow> Some([],s) |
  x#ws' \<Rightarrow> worklist_tree_aux succs f (succs x @ ws', f x s))"
by(simp add: worklist_tree_aux_def worklist_aux_Nil worklist_aux_Cons split: list.split)


abbreviation Rel :: "('a \<Rightarrow> 'a list) \<Rightarrow> ('a * 'a)set" where
"Rel f == {(x,y). y : set(f x)}"

lemma Image_Rel_set:
  "(Rel succs)\<^sup>* `` set(succs x) = (Rel succs)\<^sup>+ `` {x}"
by(auto simp add: trancl_unfold_left)

lemma RTranCl_conv:
  "g [succs]\<rightarrow>* h \<longleftrightarrow> (g,h) : ((Rel succs)\<^sup>*)" (is "?L = ?R")
proof-
  have "?L \<Longrightarrow> ?R"
    apply(erule RTranCl_induct)
    apply blast
    apply (auto elim: rtrancl_into_rtrancl)
    done
  moreover
  have "?R \<Longrightarrow> ?L"
    apply(erule converse_rtrancl_induct)
    apply(rule RTranCl.refl)
    apply (auto elim: RTranCl.succs)
    done
  ultimately show ?thesis by blast
qed

lemma worklist_end_empty:
  "worklist_aux succs f (ws,s) = Some(ws',s') \<Longrightarrow> ws' = []"
unfolding worklist_aux_def
by (drule while_option_stop) simp

theorem worklist_tree_aux_Some_foldl:
assumes "worklist_tree_aux succs f (ws,s) = Some(ws',s')"
shows "\<exists>rs. set rs = ((Rel succs)\<^sup>*) `` (set ws) \<and>
              s' = foldl (\<lambda>s x. f x s) s rs"
proof -
  let ?b = "\<lambda>(ws,s). ws \<noteq> []"
  let ?c = "\<lambda>(ws,s). case ws of x#ws' \<Rightarrow> (succs x @ ws', f x s)"
  let ?Q = "\<lambda>ws' s' done.
    s' = foldl (\<lambda>x s. f s x) s done \<and>
      ((Rel succs)\<^sup>*) `` (set ws) =
          set done \<union> ((Rel succs)\<^sup>*) `` set ws'"
  let ?P = "\<lambda>(ws,s). \<exists>done. ?Q ws s done"
  have 0: "while_option ?b ?c (ws,s) = Some(ws',s')"
    using assms by(simp add: worklist_tree_aux_def worklist_aux_def)
  from while_option_stop[OF 0] have "ws' = []" by simp
  have init: "?P (ws,s)"
    apply auto
    apply(rule_tac x = "[]" in exI)
    apply simp
    done
  { fix ws s
    assume "?P (ws,s)"
    then obtain "done" where "?Q ws s done" by blast
    assume "?b(ws,s)"
    then obtain x ws' where "ws = x # ws'" by(auto simp: neq_Nil_conv)
    then have "?Q (succs x @ ws') (f x s) (done @ [x])"
      using \<open>?Q ws s done\<close>
      apply simp
      apply(erule thin_rl)+
      apply (auto simp add: Image_Un Image_Rel_set)
      apply (blast elim: rtranclE intro: rtrancl_into_trancl1)
      done
    hence "?P(?c(ws,s))" using \<open>ws=x#ws'\<close>
      by(simp only: split_conv list.cases) blast
  }
  then have "?P(ws',s')"
    using while_option_rule[where P="?P", OF _ 0 init]
    by auto
  then show ?thesis using \<open>ws'=[]\<close> by auto
qed

definition "worklist_tree succs f ws s =
  (case worklist_tree_aux succs f (ws,s) of
     None \<Rightarrow> None | Some(ws,s) \<Rightarrow> Some s)"

theorem worklist_tree_Some_foldl:
  "worklist_tree succs f ws s = Some s' \<Longrightarrow>
   \<exists>rs. set rs = ((Rel succs)\<^sup>*) `` (set ws) \<and>
              s' = foldl (\<lambda>s x. f x s) s rs"
by(simp add: worklist_tree_def worklist_tree_aux_Some_foldl split:option.splits prod.splits)

lemma invariant_succs:
assumes "invariant I succs"
and "\<forall>x\<in>S. I x"
shows "\<forall>x \<in> (Rel succs)\<^sup>* `` S. I x"
proof-
  { fix x y have "(x,y) : (Rel succs)\<^sup>* \<Longrightarrow> I x \<Longrightarrow> I y"
    proof(induct rule:rtrancl_induct)
      case base thus ?case .
    next
      case step with assms(1) show ?case by(auto simp:invariant_def)
    qed
  } with assms(2) show ?thesis by blast
qed

lemma worklist_tree_aux_rule:
assumes "worklist_tree_aux succs f (ws,s) = Some(ws',s')"
and "invariant I succs"
and "\<forall>x \<in> set ws. I x"
and "\<And>s. P [] s s"
and "\<And>r x ws s. I x \<Longrightarrow> \<forall>x \<in> set ws. I x \<Longrightarrow> P ws (f x s) r \<Longrightarrow> P (x#ws) s r"
shows "\<exists>rs. set rs = ((Rel succs)\<^sup>* ) `` (set ws) \<and> P rs s s'"
proof-
  let ?R = "(Rel succs)\<^sup>* `` set ws"
  from worklist_tree_aux_Some_foldl[OF assms(1)] obtain rs where
    rs: "set rs = ?R" "s' = foldl (\<lambda>s x. f x s) s rs" by blast
  { fix xs have "(\<forall>x \<in> set xs. I x) \<Longrightarrow> P xs s (foldl (\<lambda>s x. f x s) s xs)"
    proof(induct xs arbitrary: s)
      case Nil show ?case using assms(4) by simp
    next
      case Cons thus ?case using assms(5) by simp
    qed
  }
  with invariant_succs[OF assms(2,3)] show ?thesis by (metis rs)
qed

lemma worklist_tree_aux_rule2:
assumes "worklist_tree_aux succs f (ws,s) = Some(ws',s')"
and "invariant I succs"
and "\<forall>x \<in> set ws. I x"
and "S s" and "\<And>x s. I x \<Longrightarrow> S s \<Longrightarrow> S(f x s)"
and "\<And>s. P [] s s"
and "\<And>r x ws s. I x \<Longrightarrow> \<forall>x \<in> set ws. I x \<Longrightarrow> S s
  \<Longrightarrow> P ws (f x s) r \<Longrightarrow> P (x#ws) s r"
shows "\<exists>rs. set rs = ((Rel succs)\<^sup>*) `` (set ws) \<and> P rs s s'"
proof-
  let ?R = "(Rel succs)\<^sup>* `` set ws"
  from worklist_tree_aux_Some_foldl[OF assms(1)] obtain rs where
    rs: "set rs = ?R" "s' = foldl (\<lambda>s x. f x s) s rs" by blast
  { fix xs have "(\<forall>x \<in> set xs. I x) \<Longrightarrow> S s \<Longrightarrow> P xs s (foldl (\<lambda>s x. f x s) s xs)"
    proof(induct xs arbitrary: s)
      case Nil show ?case using assms(6) by simp
    next
      case Cons thus ?case using assms(5,7) by simp
    qed
  }
  with invariant_succs[OF assms(2,3)] assms(4) show ?thesis by (metis rs)
qed

lemma worklist_tree_rule:
assumes "worklist_tree succs f ws s = Some(s')"
and "invariant I succs"
and "\<forall>x \<in> set ws. I x"
and "\<And>s. P [] s s"
and "\<And>r x ws s. I x \<Longrightarrow> \<forall>x \<in> set ws. I x \<Longrightarrow> P ws (f x s) r \<Longrightarrow> P (x#ws) s r"
shows "\<exists>rs. set rs = ((Rel succs)\<^sup>*) `` (set ws) \<and> P rs s s'"
proof-
  obtain ws' where "worklist_tree_aux succs f (ws,s) = Some(ws',s')" using assms(1)
    by(simp add: worklist_tree_def split: option.split_asm prod.split_asm)
  from worklist_tree_aux_rule[where P=P,OF this assms(2-5)] show ?thesis by blast
qed

lemma worklist_tree_rule2:
assumes "worklist_tree succs f ws s = Some(s')"
and "invariant I succs"
and "\<forall>x \<in> set ws. I x"
and "S s" and "\<And>x s. I x \<Longrightarrow> S s \<Longrightarrow> S(f x s)"
and "\<And>s. P [] s s"
and "\<And>r x ws s. I x \<Longrightarrow> \<forall>x \<in> set ws. I x \<Longrightarrow> S s
  \<Longrightarrow> P ws (f x s) r \<Longrightarrow> P (x#ws) s r"
shows "\<exists>rs. set rs = ((Rel succs)\<^sup>*) `` (set ws) \<and> P rs s s'"
proof-
  obtain ws' where "worklist_tree_aux succs f (ws,s) = Some(ws',s')" using assms(1)
    by(simp add: worklist_tree_def split: option.split_asm prod.split_asm)
  from worklist_tree_aux_rule2[where P=P and S=S,OF this assms(2-7)]
  show ?thesis by blast
qed

lemma worklist_tree_aux_state_inv:
assumes "worklist_tree_aux succs f (ws,s) = Some(ws',s')"
and "I s"
and "\<And>x s. I s \<Longrightarrow> I(f x s)"
shows "I s'"
proof-
  from worklist_tree_aux_rule[where P="\<lambda>ws s s'. I s \<longrightarrow> I s'" and I="\<lambda>x. True",
    OF assms(1)] assms(2-3)
  show ?thesis by(auto simp: invariant_def)
qed

lemma worklist_tree_state_inv:
  "worklist_tree succs f ws s = Some(s')
   \<Longrightarrow> I s \<Longrightarrow> (\<And>x s. I s \<Longrightarrow> I(f x s)) \<Longrightarrow> I s'"
unfolding worklist_tree_def
by(auto intro: worklist_tree_aux_state_inv split: option.splits)


locale set_modulo = quasi_order +
fixes empty :: "'s"
and insert_mod :: "'a \<Rightarrow> 's \<Rightarrow> 's"
and set_of :: "'s \<Rightarrow> 'a set"
and I :: "'a \<Rightarrow> bool"
and S :: "'s \<Rightarrow> bool"
assumes set_of_empty: "set_of empty = {}"
and set_of_insert_mod: "I x \<Longrightarrow> S s \<and> (\<forall>x \<in> set_of s. I x)
  \<Longrightarrow>
  set_of(insert_mod x s) = insert x (set_of s) \<or>
  (\<exists>y \<in> set_of s. x \<preceq> y) \<and> set_of (insert_mod x s) = set_of s"
and S_empty: "S empty"
and S_insert_mod: "S s \<Longrightarrow> S (insert_mod x s)"
begin

definition insert_mod2 :: "('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 's \<Rightarrow> 's" where
"insert_mod2 P f x s = (if P x then insert_mod (f x) s else s)"

definition "SI s = (S s \<and> (\<forall>x \<in> set_of s. I x))"

lemma SI_empty: "SI empty"
by(simp add: SI_def S_empty set_of_empty)

lemma SI_insert_mod:
  "I x \<Longrightarrow> SI s \<Longrightarrow> SI (insert_mod x s)"
apply(simp add: SI_def S_insert_mod)
by (metis insertE set_of_insert_mod)

lemma SI_insert_mod2: "(\<And>x. inv0 x \<Longrightarrow> I (f x)) \<Longrightarrow>
  inv0 x \<Longrightarrow> SI s \<Longrightarrow> SI (insert_mod2 P f x s)"
by (metis insert_mod2_def SI_insert_mod)

definition worklist_tree_coll_aux ::
  "('b \<Rightarrow> 'b list) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 's \<Rightarrow> 's option"
where
"worklist_tree_coll_aux succs P f = worklist_tree succs (insert_mod2 P f)"

definition worklist_tree_coll ::
  "('b \<Rightarrow> 'b list) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 's option"
where
"worklist_tree_coll succs P f ws = worklist_tree_coll_aux succs P f ws empty"

lemma worklist_tree_coll_aux_equiv:
assumes "worklist_tree_coll_aux succs P f ws s = Some s'"
and "invariant inv0 succs"
and "\<forall>x \<in> set ws. inv0 x"
and "\<And>x. inv0 x \<Longrightarrow> I(f x)"
and "SI s"
shows "set_of s' =\<^sub>\<preceq>
  f ` {x : (Rel succs)\<^sup>* `` (set ws). P x} \<union> set_of s"
apply(insert assms(1))
unfolding worklist_tree_coll_aux_def
apply(drule worklist_tree_rule2[where I = inv0 and S = SI and
  P = "\<lambda>ws s s'. SI s \<longrightarrow> set_of s' =\<^sub>\<preceq> f ` {x : set ws. P x} \<union> set_of s",
  OF _ assms(2,3,5)])
   apply(simp add: SI_insert_mod2 assms(4))
  apply(clarsimp)
 apply(clarsimp simp add: insert_mod2_def split: if_split_asm)
  apply(frule assms(4))
  apply(frule SI_def[THEN iffD1])
  apply(frule (1) set_of_insert_mod)
  apply (simp add: SI_insert_mod)
  apply(erule disjE)
   prefer 2
   apply(rule seteq_qle_trans)
    apply assumption
   apply (simp add: "defs")
   apply blast
  apply(rule seteq_qle_trans)
   apply assumption
  apply (simp add: "defs")
  apply blast
 apply(rule seteq_qle_trans)
  apply assumption
 apply (simp add: "defs")
 apply blast
using assms(5)
apply auto
done

lemma worklist_tree_coll_equiv:
  "worklist_tree_coll succs P f ws = Some s' \<Longrightarrow> invariant inv0 succs
   \<Longrightarrow> \<forall>x \<in> set ws. inv0 x \<Longrightarrow> (\<And>x. inv0 x \<Longrightarrow> I(f x))
   \<Longrightarrow> set_of s' =\<^sub>\<preceq> f ` {x : (Rel succs)\<^sup>* `` (set ws). P x}"
unfolding worklist_tree_coll_def
apply(drule (2) worklist_tree_coll_aux_equiv)
apply(auto simp: set_of_empty SI_empty)
done

lemma worklist_tree_coll_aux_subseteq:
  "worklist_tree_coll_aux succs P f ws t\<^sub>0 = Some t \<Longrightarrow>
  invariant inv0 succs \<Longrightarrow>  \<forall>g \<in> set ws. inv0 g \<Longrightarrow>
  (\<And>x. inv0 x \<Longrightarrow> I(f x)) \<Longrightarrow> SI t\<^sub>0 \<Longrightarrow>
  set_of t \<subseteq> set_of t\<^sub>0 \<union> f ` {h : (Rel succs)\<^sup>* `` set ws. P h}"
unfolding worklist_tree_coll_aux_def
apply(drule worklist_tree_rule2[where I = inv0 and S = SI and P =
  "\<lambda>ws t t'. set_of t' \<subseteq> set_of t \<union> f ` {g \<in> set ws. P g}"])
      apply assumption
     apply assumption
    apply assumption
   apply(simp add: SI_insert_mod2)
  apply clarsimp
 apply (clarsimp simp: insert_mod2_def split: if_split_asm)
  using set_of_insert_mod
  apply(simp add: SI_def image_def)
  apply(blast)
 apply blast
apply blast
done

lemma worklist_tree_coll_subseteq:
  "worklist_tree_coll succs P f ws = Some t \<Longrightarrow>
  invariant inv0 succs \<Longrightarrow> \<forall>g \<in> set ws. inv0 g \<Longrightarrow>
  (\<And>x. inv0 x \<Longrightarrow> I(f x)) \<Longrightarrow>
  set_of t \<subseteq> f ` {h : (Rel succs)\<^sup>* `` set ws. P h}"
unfolding worklist_tree_coll_def
apply(drule (1) worklist_tree_coll_aux_subseteq)
apply(auto simp: set_of_empty SI_empty)
done

lemma worklist_tree_coll_inv:
  "worklist_tree_coll succs P f ws = Some s \<Longrightarrow> S s"
unfolding worklist_tree_coll_def worklist_tree_coll_aux_def
apply(drule worklist_tree_state_inv[where I = S])
apply (auto simp: S_empty insert_mod2_def S_insert_mod)
done

end

end
