theory Step_Conv
imports Main
begin
  (* Different ways of representing transitions, 
    and functions to convert between them:

    rel :: ('a \<times> 'b) set
    pred :: 'a \<Rightarrow> 'b \<Rightarrow> bool
    succ :: 'a \<Rightarrow> 'b set
  *)

  definition "rel_of_pred s \<equiv> {(a,b). s a b}"
  definition "rel_of_succ s \<equiv> {(a,b). b\<in>s a}"

  definition "pred_of_rel s \<equiv> \<lambda>a b. (a,b)\<in>s"
  definition "pred_of_succ s \<equiv> \<lambda>a b. b\<in>s a"

  definition "succ_of_rel s \<equiv> \<lambda>a. {b. (a,b)\<in>s}"
  definition "succ_of_pred s \<equiv> \<lambda>a. {b. s a b}"

  lemma rps_expand[simp]:
    "(a,b)\<in>rel_of_pred p \<longleftrightarrow> p a b"
    "(a,b)\<in>rel_of_succ s \<longleftrightarrow> b \<in> s a"

    "pred_of_rel r a b \<longleftrightarrow> (a,b)\<in>r"
    "pred_of_succ s a b \<longleftrightarrow> b \<in> s a"

    "b\<in>succ_of_rel r a \<longleftrightarrow> (a,b)\<in>r"
    "b\<in>succ_of_pred p a \<longleftrightarrow> p a b"
    unfolding rel_of_pred_def pred_of_rel_def
    unfolding rel_of_succ_def succ_of_rel_def
    unfolding pred_of_succ_def succ_of_pred_def
    by auto

  lemma rps_conv[simp]:
    "rel_of_pred (pred_of_rel r) = r"
    "rel_of_pred (pred_of_succ s) = rel_of_succ s"

    "rel_of_succ (succ_of_rel r) = r"
    "rel_of_succ (succ_of_pred p) = rel_of_pred p"

    "pred_of_rel (rel_of_pred p) = p"
    "pred_of_rel (rel_of_succ s) = pred_of_succ s"

    "pred_of_succ (succ_of_pred p) = p"
    "pred_of_succ (succ_of_rel r) = pred_of_rel r"

    "succ_of_rel (rel_of_succ s) = s"
    "succ_of_rel (rel_of_pred p) = succ_of_pred p"

    "succ_of_pred (pred_of_succ s) = s"
    "succ_of_pred (pred_of_rel r) = succ_of_rel r"
    unfolding rel_of_pred_def pred_of_rel_def
    unfolding rel_of_succ_def succ_of_rel_def
    unfolding pred_of_succ_def succ_of_pred_def
    by auto

  (* Lifting transitions from option monad to option\<times>option *)
  definition m2r_rel :: "('a \<times> 'a option) set \<Rightarrow> 'a option rel"
    where "m2r_rel r \<equiv> {(Some a,b)|a b. (a,b)\<in>r}"

  definition m2r_pred :: "('a \<Rightarrow> 'a option \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> bool"
    where "m2r_pred p \<equiv> \<lambda>None \<Rightarrow> \<lambda>_. False | Some a \<Rightarrow> p a"

  definition m2r_succ :: "('a \<Rightarrow> 'a option set) \<Rightarrow> 'a option \<Rightarrow> 'a option set"
    where "m2r_succ s \<equiv> \<lambda>None \<Rightarrow> {} | Some a \<Rightarrow> s a"

  lemma m2r_expand[simp]:
    "(a,b)\<in>m2r_rel r \<longleftrightarrow> (\<exists>a'. a=Some a' \<and> (a',b)\<in>r)"
    "m2r_pred p a b \<longleftrightarrow> (\<exists>a'. a=Some a' \<and> p a' b)"
    "b\<in>m2r_succ s a \<longleftrightarrow> (\<exists>a'. a=Some a' \<and> b \<in> s a')"
    unfolding m2r_rel_def m2r_succ_def m2r_pred_def
    by (auto split: option.splits)

  lemma m2r_conv[simp]:
    "m2r_rel (rel_of_succ s) = rel_of_succ (m2r_succ s)"
    "m2r_rel (rel_of_pred p) = rel_of_pred (m2r_pred p)"

    "m2r_pred (pred_of_succ s) = pred_of_succ (m2r_succ s)"
    "m2r_pred (pred_of_rel r) = pred_of_rel (m2r_rel r)"

    "m2r_succ (succ_of_pred p) = succ_of_pred (m2r_pred p)"
    "m2r_succ (succ_of_rel r) = succ_of_rel (m2r_rel r)"
    unfolding rel_of_pred_def pred_of_rel_def
    unfolding rel_of_succ_def succ_of_rel_def
    unfolding pred_of_succ_def succ_of_pred_def
    unfolding m2r_rel_def m2r_succ_def m2r_pred_def
    by (auto split: option.splits)


  definition "rel_of_enex enex \<equiv> let (en, ex) = enex in {(s, ex a s) |s a. a \<in> en s}"
  definition "pred_of_enex enex \<equiv> \<lambda>s s'. let (en,ex) = enex in \<exists>a\<in>en s. s'=ex a s"
  definition "succ_of_enex enex \<equiv> \<lambda>s. let (en,ex) = enex in {s'. \<exists>a\<in>en s. s'=ex a s}"
  
  lemma x_of_enex_expand[simp]: 
    "(s, s') \<in> rel_of_enex (en, ex) \<longleftrightarrow> (\<exists> a \<in> en s. s' = ex a s)"
    "pred_of_enex (en,ex) s s' \<longleftrightarrow> (\<exists>a\<in>en s. s'=ex a s)"
    "s'\<in>succ_of_enex (en,ex) s \<longleftrightarrow> (\<exists>a\<in>en s. s'=ex a s)"
    unfolding rel_of_enex_def pred_of_enex_def succ_of_enex_def by auto
  
  lemma x_of_enex_conv[simp]:
    "rel_of_pred (pred_of_enex enex) = rel_of_enex enex"
    "rel_of_succ (succ_of_enex enex) = rel_of_enex enex"
    "pred_of_rel (rel_of_enex enex) = pred_of_enex enex"
    "pred_of_succ (succ_of_enex enex) = pred_of_enex enex"
    "succ_of_rel (rel_of_enex enex) = succ_of_enex enex"
    "succ_of_pred (pred_of_enex enex) = succ_of_enex enex"
    unfolding rel_of_enex_def pred_of_enex_def succ_of_enex_def 
    unfolding rel_of_pred_def rel_of_succ_def
    unfolding pred_of_rel_def pred_of_succ_def
    unfolding succ_of_rel_def succ_of_pred_def
    by auto

end
