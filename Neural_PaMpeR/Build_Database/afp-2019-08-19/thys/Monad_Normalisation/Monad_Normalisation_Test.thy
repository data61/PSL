(*  Title:      Monad_Normalisation_Test.thy
    Author:     Manuel Eberl, TU München
    Author:     Andreas Lochbihler, ETH Zurich
    Author:     Joshua Schneider, ETH Zurich
*)

theory Monad_Normalisation_Test
imports Monad_Normalisation
begin

section \<open>Tests and examples\<close>

context includes monad_normalisation
begin

lemma
  assumes "f = id"
  shows
    "do {x \<leftarrow> B; z \<leftarrow> C x; d \<leftarrow> E z x; a \<leftarrow> D z x; y \<leftarrow> A; return_pmf (x,y)} =
     do {y \<leftarrow> A; x \<leftarrow> B; z \<leftarrow> C x; a \<leftarrow> D z x; d \<leftarrow> E z x; return_pmf (f (x,y))}"
apply (simp)
apply (simp add: assms)
done

lemma "(do {a \<leftarrow> E; b \<leftarrow> E; w \<leftarrow> B b a; z \<leftarrow> B a b; return_pmf (w,z)}) =
       (do {a \<leftarrow> E; b \<leftarrow> E; z \<leftarrow> B a b; w \<leftarrow> B b a; return_pmf (w,z)})"
by (simp)

lemma "(do {a \<leftarrow> E; b \<leftarrow> E; w \<leftarrow> B b a; z \<leftarrow> B a b; return_pmf (w,z)}) =
       (do {a \<leftarrow> E; b \<leftarrow> E; z \<leftarrow> B a b; w \<leftarrow> B b a; return_pmf (w,z)})"
by (simp)

lemma "do {y \<leftarrow> A; x \<leftarrow> A; z \<leftarrow> B x y y; w \<leftarrow> B x x y; Some (x,y)} =
       do {x \<leftarrow> A; y \<leftarrow> A; z \<leftarrow> B x x y; w \<leftarrow> B x y y; Some (x,y)}"
by (simp)

lemma "do {y \<leftarrow> A; x \<leftarrow> A; z \<leftarrow> B x y y; w \<leftarrow> B x x y; {x,y}} =
       do {x \<leftarrow> A; y \<leftarrow> A; z \<leftarrow> B x x y; w \<leftarrow> B x y y; {x,y}}"
by (simp)

lemma "do {y \<leftarrow> A; x \<leftarrow> A; z \<leftarrow> B x y y; w \<leftarrow> B x x y; return_pmf (x,y)} =
       do {x \<leftarrow> A; y \<leftarrow> A; z \<leftarrow> B x x y; w \<leftarrow> B x y y; return_pmf (x,y)}"
by (simp)

lemma "do {x \<leftarrow> A 0; y \<leftarrow> A x; w \<leftarrow> B y y; z \<leftarrow> B x y; a \<leftarrow> C; Predicate.single (a,a)} =
       do {x \<leftarrow> A 0; y \<leftarrow> A x; z \<leftarrow> B x y; w \<leftarrow> B y y; a \<leftarrow> C; Predicate.single (a,a)}"
by (simp)

lemma "do {x \<leftarrow> A 0; y \<leftarrow> A x; z \<leftarrow> B x y; w \<leftarrow> B y y; a \<leftarrow> C; return_pmf (a,a)} =
       do {x \<leftarrow> A 0; y \<leftarrow> A x; z \<leftarrow> B y y; w \<leftarrow> B x y; a \<leftarrow> C; return_pmf (a,a)}"
by (simp)

lemma "do {x \<leftarrow> B; z \<leftarrow> C x; d \<leftarrow> E z x; a \<leftarrow> D z x; y \<leftarrow> A; return_pmf (x,y)} =
       do {y \<leftarrow> A; x \<leftarrow> B; z \<leftarrow> C x; a \<leftarrow> D z x; d \<leftarrow> E z x; return_pmf (x,y)}"
by (simp)


no_adhoc_overloading Monad_Syntax.bind bind_pmf

context
  fixes \<A>1 :: "'a \<Rightarrow> (('a \<times> 'a) \<times> 'b) spmf"
  and \<A>2 :: "'a \<times> 'a \<Rightarrow> 'b \<Rightarrow> bool spmf"
  and sample_uniform :: "nat \<Rightarrow> nat spmf"
  and order :: "'a \<Rightarrow> nat"
begin

lemma 
  "do {
      x \<leftarrow> sample_uniform (order \<G>);
      y \<leftarrow> sample_uniform (order \<G>);
      z \<leftarrow> sample_uniform (order \<G>);
      b \<leftarrow> coin_spmf;
      ((msg1, msg2), \<sigma>) \<leftarrow> \<A>1 (f x);
      _ :: unit \<leftarrow> assert_spmf (valid_plain msg1 \<and> valid_plain msg2);
      guess \<leftarrow> \<A>2 (f y, xor (f z) (if b then msg1 else msg2)) \<sigma>;
      return_spmf (guess \<longleftrightarrow> b)
    } = do {
      x \<leftarrow> sample_uniform (order \<G>);
      y \<leftarrow> sample_uniform (order \<G>);
      ((msg1, msg2), \<sigma>) \<leftarrow> \<A>1 (f x);
      _ :: unit \<leftarrow> assert_spmf (valid_plain msg1 \<and> valid_plain msg2);
      b \<leftarrow> coin_spmf;
      x \<leftarrow> sample_uniform (order \<G>);
      guess \<leftarrow> \<A>2 (f y, xor (f x) (if b then msg1 else msg2)) \<sigma>;
      return_spmf (guess \<longleftrightarrow> b)
    }"
by (simp add: split_def)

lemma
  "do {
      x \<leftarrow> sample_uniform (order \<G>);
      xa \<leftarrow> sample_uniform (order \<G>);
      x \<leftarrow> \<A>1 (f x);
      case x of
      (x, xb) \<Rightarrow>
        (case x of
         (msg1, msg2) \<Rightarrow>
           \<lambda>\<sigma>. do {
                a \<leftarrow> assert_spmf (valid_plain msg1 \<and> valid_plain msg2);
                x \<leftarrow> coin_spmf;
                xaa \<leftarrow> map_spmf f (sample_uniform (order \<G>));
                guess \<leftarrow> \<A>2 (f xa, xaa) \<sigma>;
                return_spmf (guess \<longleftrightarrow> x)
              })
         xb
    } = do {
      x \<leftarrow> sample_uniform (order \<G>);
      xa \<leftarrow> sample_uniform (order \<G>);
      x \<leftarrow> \<A>1 (f x);
      case x of
      (x, xb) \<Rightarrow>
        (case x of
         (msg1, msg2) \<Rightarrow>
           \<lambda>\<sigma>. do {
                a \<leftarrow> assert_spmf (valid_plain msg1 \<and> valid_plain msg2);
                z \<leftarrow> map_spmf f (sample_uniform (order \<G>));
                guess \<leftarrow> \<A>2 (f xa, z) \<sigma>;
                map_spmf ((\<longleftrightarrow>) guess) coin_spmf
              })
         xb
    }"
by (simp add: map_spmf_conv_bind_spmf)

lemma elgamal_step3:
  "do {
      x \<leftarrow> sample_uniform (order \<G>);
      y \<leftarrow> sample_uniform (order \<G>);
      b \<leftarrow> coin_spmf;
      p \<leftarrow> \<A>1 (f x);
      _ \<leftarrow> assert_spmf (valid_plain (fst (fst p)) \<and> valid_plain (snd (fst p)));
      guess \<leftarrow>
        \<A>2 (f y, xor (f (x * y)) (if b then fst (fst p) else snd (fst p)))
         (snd p);
      return_spmf (guess \<longleftrightarrow> b)
    }  = do {
      y \<leftarrow> sample_uniform (order \<G>);
      b \<leftarrow> coin_spmf;
      p \<leftarrow> \<A>1 (f y);
      _ \<leftarrow> assert_spmf (valid_plain (fst (fst p)) \<and> valid_plain (snd (fst p)));
      ya \<leftarrow> sample_uniform (order \<G>);
      b' \<leftarrow> \<A>2 (f ya,
                 xor (f (y * ya)) (if b then fst (fst p) else snd (fst p)))
             (snd p);
      return_spmf (b' \<longleftrightarrow> b)
    }"
by (simp)

end

text \<open>Distributivity\<close>

lemma
  "do {
      x \<leftarrow> A :: nat spmf;
      a \<leftarrow> B;
      b \<leftarrow> B;
      if a = b then do {
        return_spmf x
      } else do {
        y \<leftarrow> C;
        return_spmf (x + y)
      }
   } = do {
      a \<leftarrow> B;
      b \<leftarrow> B;
      if b = a then A else do {
        y \<leftarrow> C;
        x \<leftarrow> A;
        return_spmf (y + x)
      }
   }"
by (simp add: add.commute cong: if_cong)

lemma
  "do {
      x \<leftarrow> A :: nat spmf;
      p \<leftarrow> do {
        a \<leftarrow> B;
        b \<leftarrow> B;
        return_spmf (a, b)
      };
      q \<leftarrow> coin_spmf;
      if q then do {
        return_spmf (x + fst p)
      } else do {
        y \<leftarrow> C;
        return_spmf (y + snd p)
      }
   } = do {
      q \<leftarrow> coin_spmf;
      if q then do {
        x \<leftarrow> A;
        a \<leftarrow> B;
        _ \<leftarrow> B;
        return_spmf (x + a)
      } else do {
        y \<leftarrow> C;
        a \<leftarrow> B;
        _ \<leftarrow> B;
        _ \<leftarrow> A;
        return_spmf (y + a)
      }
   }"
by (simp cong: if_cong)

lemma
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> nat + nat"
  shows
  "do {
      x \<leftarrow> (A::nat set);
      a \<leftarrow> B;
      b \<leftarrow> B;
      case f a b of
        Inl c \<Rightarrow> {x}
      | Inr c \<Rightarrow> do {
          y \<leftarrow> C x;
          {(x + y + c)}
        }
   } = do {
      a \<leftarrow> B;
      b \<leftarrow> B;
      case f b a of
        Inl c \<Rightarrow> A
      | Inr c \<Rightarrow> do {
          x \<leftarrow> A;
          y \<leftarrow> C x;
          {(y + c + x)}
      }
   }"
by (simp add: add.commute add.left_commute cong: sum.case_cong)


section \<open>Limits\<close>

text \<open>
  The following example shows that the combination of monad normalisation and regular ordered
  rewriting is not necessarily confluent.
\<close>

lemma "do {a \<leftarrow> A; b \<leftarrow> A; Some (a \<and> b, b)} =
       do {a \<leftarrow> A; b \<leftarrow> A; Some (a \<and> b, a)}"
apply (simp add: conj_comms)?       \<comment> \<open>no progress made\<close>
apply (rewrite option_bind_commute) \<comment> \<open>force a particular binder order\<close>
apply (simp only: conj_comms)
done

text \<open>
  The next example shows that even monad normalisation alone is not confluent because 
  the term ordering prevents the reordering of \<open>f A\<close> with \<open>f B\<close>.
  But if we change \<open>A\<close> to \<open>E\<close>, then the reordering works as expected.
\<close>

lemma
  "do {a \<leftarrow> f A; b \<leftarrow> f B; c \<leftarrow> D b; d \<leftarrow> f C; F a c d} = 
   do {b \<leftarrow> f B; c \<leftarrow> D b; a \<leftarrow> f A; d \<leftarrow> f C; F a c d}"
  for f :: "'b \<Rightarrow> 'a option" and D :: "'a \<Rightarrow> 'a option"
  apply(simp)? \<comment> \<open>no progress made\<close>
  apply(subst option_bind_commute, subst (2) option_bind_commute, rule refl)
  done

lemma
  "do {a \<leftarrow> f E; b \<leftarrow> f B; c \<leftarrow> D b; d \<leftarrow> f C; F a c d} = 
   do {b \<leftarrow> f B; c \<leftarrow> D b; a \<leftarrow> f E; d \<leftarrow> f C; F a c d}"
  for f :: "'b \<Rightarrow> 'a option" and D :: "'a \<Rightarrow> 'a option"
  by simp

end

end
