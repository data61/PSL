(*  Title:       Lazy_TLList.thy
    Author:      Andreas Lochbihler
*)

section \<open>Code generator setup to implement terminated lazy lists lazily\<close>

theory Lazy_TLList imports
  TLList
  Lazy_LList
begin

code_identifier code_module Lazy_TLList \<rightharpoonup>
  (SML) TLList and
  (OCaml) TLList and
  (Haskell) TLList and
  (Scala) TLList

definition Lazy_tllist :: "(unit \<Rightarrow> 'a \<times> ('a, 'b) tllist + 'b) \<Rightarrow> ('a, 'b) tllist"
where [code del]:
  "Lazy_tllist xs = (case xs () of Inl (x, ys) \<Rightarrow> TCons x ys | Inr b \<Rightarrow> TNil b)"

definition force :: "('a, 'b) tllist \<Rightarrow> 'a \<times> ('a, 'b) tllist + 'b"
where [simp, code del]: "force xs = (case xs of TNil b \<Rightarrow> Inr b | TCons x ys \<Rightarrow> Inl (x, ys))"

code_datatype Lazy_tllist

declare \<comment> \<open>Restore consistency in code equations between @{const partial_term_of} and @{const narrowing} for @{typ "('a, 'b) tllist"}\<close>
   [[code drop: "partial_term_of :: (_, _) tllist itself => _"]]

lemma partial_term_of_tllist_code [code]:
  fixes tytok :: "('a :: partial_term_of, 'b :: partial_term_of) tllist itself" shows
  "partial_term_of tytok (Quickcheck_Narrowing.Narrowing_variable p tt) \<equiv>
   Code_Evaluation.Free (STR ''_'') (Typerep.typerep TYPE(('a, 'b) tllist))"
  "partial_term_of tytok (Quickcheck_Narrowing.Narrowing_constructor 0 [b]) \<equiv>
   Code_Evaluation.App
     (Code_Evaluation.Const (STR ''TLList.tllist.TNil'') (Typerep.typerep TYPE('b \<Rightarrow> ('a, 'b) tllist)))
     (partial_term_of TYPE('b) b)"
  "partial_term_of tytok (Quickcheck_Narrowing.Narrowing_constructor 1 [head, tail]) \<equiv>
   Code_Evaluation.App
     (Code_Evaluation.App
        (Code_Evaluation.Const
           (STR ''TLList.tllist.TCons'')
           (Typerep.typerep TYPE('a \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist)))
        (partial_term_of TYPE('a) head))
     (partial_term_of TYPE(('a, 'b) tllist) tail)"
by-(rule partial_term_of_anything)+

declare Lazy_tllist_def [simp]
declare sum.splits [split]

lemma TNil_Lazy_tllist [code]: 
  "TNil b = Lazy_tllist (\<lambda>_. Inr b)"
by simp

lemma TCons_Lazy_tllist [code, code_unfold]:
  "TCons x xs = Lazy_tllist (\<lambda>_. Inl (x, xs))"
by simp

lemma Lazy_tllist_inverse [simp, code]:
  "force (Lazy_tllist xs) = xs ()"
by(simp)

declare [[code drop: "equal_class.equal :: (_, _) tllist \<Rightarrow> _"]]

lemma equal_tllist_Lazy_tllist [code]:
  "equal_class.equal (Lazy_tllist xs) (Lazy_tllist ys) =
  (case xs () of 
     Inr b \<Rightarrow> (case ys () of Inr b' \<Rightarrow> b = b' | _ \<Rightarrow> False)
   | Inl (x, xs') \<Rightarrow>
     (case ys () of Inr b' \<Rightarrow> False | Inl (y, ys') \<Rightarrow> if x = y then equal_class.equal xs' ys' else False))"
by(auto simp add: equal_tllist_def)

declare
  [[code drop: thd ttl]]
  thd_def [code]
  ttl_def [code]

declare [[code drop: is_TNil]]

lemma is_TNil_code [code]:
  "is_TNil (Lazy_tllist xs) \<longleftrightarrow> 
  (case xs () of Inl _ \<Rightarrow> False | Inr _ \<Rightarrow> True)"
by simp

declare [[code drop: corec_tllist]]

lemma corec_tllist_Lazy_tllist [code]:
  "corec_tllist IS_TNIL TNIL THD endORmore TTL_end TTL_more b = Lazy_tllist
  (\<lambda>_. if IS_TNIL b then Inr (TNIL b)
       else Inl (THD b, if endORmore b then TTL_end b else corec_tllist IS_TNIL TNIL THD endORmore TTL_end TTL_more (TTL_more b)))"
by(rule tllist.expand) simp_all

declare [[code drop: unfold_tllist]]

lemma unfold_tllist_Lazy_tllist [code]:
  "unfold_tllist IS_TNIL TNIL THD TTL b = Lazy_tllist
  (\<lambda>_. if IS_TNIL b then Inr (TNIL b)
       else Inl (THD b, unfold_tllist IS_TNIL TNIL THD TTL (TTL b)))"
by(rule tllist.expand) auto

declare [[code drop: case_tllist]]

lemma case_tllist_Lazy_tllist [code]:
  "case_tllist n c (Lazy_tllist xs) = 
  (case xs () of Inl (x, ys) \<Rightarrow> c x ys | Inr b \<Rightarrow> n b)"
by simp

declare [[code drop: tllist_of_llist]]

lemma tllist_of_llist_Lazy_llist [code]:
  "tllist_of_llist b (Lazy_llist xs) =
  Lazy_tllist (\<lambda>_. case xs () of None \<Rightarrow> Inr b | Some (x, ys) \<Rightarrow> Inl (x, tllist_of_llist b ys))"
by(simp add: Lazy_llist_def split: option.splits)

declare [[code drop: terminal]]

lemma terminal_Lazy_tllist [code]:
  "terminal (Lazy_tllist xs) = 
  (case xs () of Inl (_, ys) \<Rightarrow> terminal ys | Inr b \<Rightarrow> b)"
by simp

declare [[code drop: tmap]]

lemma tmap_Lazy_tllist [code]:
  "tmap f g (Lazy_tllist xs) =
  Lazy_tllist (\<lambda>_. case xs () of Inl (x, ys) \<Rightarrow> Inl (f x, tmap f g ys) | Inr b \<Rightarrow> Inr (g b))"
by simp

declare [[code drop: tappend]]

lemma tappend_Lazy_tllist [code]:
  "tappend (Lazy_tllist xs) ys =
  Lazy_tllist (\<lambda>_. case xs () of Inl (x, xs') \<Rightarrow> Inl (x, tappend xs' ys) | Inr b \<Rightarrow> force (ys b))"
by(auto split: tllist.split)

declare [[code drop: lappendt]]

lemma lappendt_Lazy_llist [code]:
  "lappendt (Lazy_llist xs) ys =
  Lazy_tllist (\<lambda>_. case xs () of None \<Rightarrow> force ys | Some (x, xs') \<Rightarrow> Inl (x, lappendt xs' ys))"
by(auto simp add: Lazy_llist_def split: option.split tllist.split)

declare [[code drop: TLList.tfilter']]

lemma tfilter'_Lazy_tllist [code]:
  "TLList.tfilter' b P (Lazy_tllist xs) =
   Lazy_tllist (\<lambda>_. case xs () of Inl (x, xs') \<Rightarrow> if P x then Inl (x, TLList.tfilter' b P xs') else force (TLList.tfilter' b P xs') | Inr b' \<Rightarrow> Inr b')"
by(simp split: tllist.split)

declare [[code drop: TLList.tconcat']]

lemma tconcat_Lazy_tllist [code]:
  "TLList.tconcat' b (Lazy_tllist xss) =
  Lazy_tllist (\<lambda>_. case xss () of Inr b' \<Rightarrow> Inr b' | Inl (xs, xss') \<Rightarrow> force (lappendt xs (TLList.tconcat' b xss')))"
by(simp split: tllist.split)

declare [[code drop: tllist_all2]]

lemma tllist_all2_Lazy_tllist [code]:
  "tllist_all2 P Q (Lazy_tllist xs) (Lazy_tllist ys) \<longleftrightarrow>
  (case xs () of 
    Inr b \<Rightarrow> (case ys () of Inr b' \<Rightarrow> Q b b' | Inl _ \<Rightarrow> False)
  | Inl (x, xs') \<Rightarrow> (case ys () of Inr _ \<Rightarrow> False | Inl (y, ys') \<Rightarrow> P x y \<and> tllist_all2 P Q xs' ys'))"
by(simp add: tllist_all2_TNil1 tllist_all2_TNil2)

declare [[code drop: llist_of_tllist]]

lemma llist_of_tllist_Lazy_tllist [code]:
  "llist_of_tllist (Lazy_tllist xs) =
  Lazy_llist (\<lambda>_. case xs () of Inl (x, ys) \<Rightarrow> Some (x, llist_of_tllist ys) | Inr b \<Rightarrow> None)"
by(simp add: Lazy_llist_def)

declare [[code drop: tnth]]

lemma tnth_Lazy_tllist [code]:
  "tnth (Lazy_tllist xs) n =
  (case xs () of Inr b \<Rightarrow> undefined n | Inl (x, ys) \<Rightarrow> if n = 0 then x else tnth ys (n - 1))"
by(cases n)(auto simp add: tnth_TNil)

declare [[code drop: gen_tlength]]

lemma gen_tlength_Lazy_tllist [code]:
  "gen_tlength n (Lazy_tllist xs) =
  (case xs () of Inr b \<Rightarrow> enat n | Inl (_, xs') \<Rightarrow> gen_tlength (n + 1) xs')"
by(simp add: gen_tlength_code)

declare [[code drop: tdropn]]

lemma tdropn_Lazy_tllist [code]:
  "tdropn n (Lazy_tllist xs) =
  Lazy_tllist (\<lambda>_. if n = 0 then xs () else case xs () of Inr b \<Rightarrow> Inr b | Inl (x, xs') \<Rightarrow> force (tdropn (n - 1) xs'))"
by(cases n)(auto split: tllist.split)

declare Lazy_tllist_def [simp del]
declare sum.splits [split del]

text \<open>Simple ML test for laziness\<close>

ML_val \<open>
  val zeros = @{code unfold_tllist} (K false) (K 0) (K 0) I ();
  val thd = @{code thd} zeros;
  val ttl = @{code ttl} zeros;
  val ttl' = @{code force} ttl;
  
  val tdropn = @{code tdropn} (@{code Suc} @{code "0::nat"}) zeros;
  
  val tfilter = @{code tfilter} 1 (K false) zeros;
\<close>

hide_const (open) force

end
