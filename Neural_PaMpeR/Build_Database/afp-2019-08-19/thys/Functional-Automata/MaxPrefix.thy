(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "Maximal prefix"

theory MaxPrefix
imports "HOL-Library.Sublist"
begin

definition
 is_maxpref :: "('a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_maxpref P xs ys =
 (prefix xs ys \<and> (xs=[] \<or> P xs) \<and> (\<forall>zs. prefix zs ys \<and> P zs \<longrightarrow> prefix zs xs))"

type_synonym 'a splitter = "'a list \<Rightarrow> 'a list * 'a list"

definition
 is_maxsplitter :: "('a list \<Rightarrow> bool) \<Rightarrow> 'a splitter \<Rightarrow> bool" where
"is_maxsplitter P f =
 (\<forall>xs ps qs. f xs = (ps,qs) = (xs=ps@qs \<and> is_maxpref P ps xs))"

fun maxsplit :: "('a list \<Rightarrow> bool) \<Rightarrow> 'a list * 'a list \<Rightarrow> 'a list \<Rightarrow> 'a splitter" where
"maxsplit P res ps []     = (if P ps then (ps,[]) else res)" |
"maxsplit P res ps (q#qs) = maxsplit P (if P ps then (ps,q#qs) else res)
                                     (ps@[q]) qs"

declare if_split[split del]

lemma maxsplit_lemma: "(maxsplit P res ps qs = (xs,ys)) =
  (if \<exists>us. prefix us qs \<and> P(ps@us) then xs@ys=ps@qs \<and> is_maxpref P xs (ps@qs)
   else (xs,ys)=res)"
proof (induction P res ps qs rule: maxsplit.induct)
  case 1
  thus ?case by (auto simp: is_maxpref_def split: if_splits)
next
  case (2 P res ps q qs)
  show ?case
  proof (cases "\<exists>us. prefix us qs \<and> P ((ps @ [q]) @ us)")
    case True
    note ex1 = this
    then guess us by (elim exE conjE) note us = this
    hence ex2: "\<exists>us. prefix us (q # qs) \<and> P (ps @ us)"
      by (intro exI[of _ "q#us"]) auto
    with ex1 and 2 show ?thesis by simp
  next
    case False
    note ex1 = this
    show ?thesis
    proof (cases "\<exists>us. prefix us (q#qs) \<and> P (ps @ us)")
      case False
      from 2 show ?thesis
        by (simp only: ex1 False) (insert ex1 False, auto simp: prefix_Cons)
    next
      case True
      note ex2 = this
      show ?thesis
      proof (cases "P ps")
        case True
        with 2 have "(maxsplit P (ps, q # qs) (ps @ [q]) qs = (xs, ys)) \<longleftrightarrow> (xs = ps \<and> ys = q # qs)"
          by (simp only: ex1 ex2) simp_all
        also have "\<dots> \<longleftrightarrow> (xs @ ys = ps @ q # qs \<and> is_maxpref P xs (ps @ q # qs))"
          using ex1 True
          by (auto simp: is_maxpref_def prefix_append prefix_Cons append_eq_append_conv2)
        finally show ?thesis using True by (simp only: ex1 ex2) simp_all
      next
        case False
        with 2 have "(maxsplit P res (ps @ [q]) qs = (xs, ys)) \<longleftrightarrow> ((xs, ys) = res)"
          by (simp only: ex1 ex2) simp
        also have "\<dots> \<longleftrightarrow> (xs @ ys = ps @ q # qs \<and> is_maxpref P xs (ps @ q # qs))"
          using ex1 ex2 False
          by (auto simp: append_eq_append_conv2 is_maxpref_def prefix_Cons)
        finally show ?thesis
          using False by (simp only: ex1 ex2) simp
      qed
    qed
  qed
qed

declare if_split[split]

lemma is_maxpref_Nil[simp]:
 "\<not>(\<exists>us. prefix us xs \<and> P us) \<Longrightarrow> is_maxpref P ps xs = (ps = [])"
  by (auto simp: is_maxpref_def)

lemma is_maxsplitter_maxsplit:
 "is_maxsplitter P (\<lambda>xs. maxsplit P ([],xs) [] xs)"
  by (auto simp: maxsplit_lemma is_maxsplitter_def)

lemmas maxsplit_eq = is_maxsplitter_maxsplit[simplified is_maxsplitter_def]

end
