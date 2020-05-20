section \<open>Multiset\<close>

text \<open>
  \file{Multiset} contains a minimal multiset structure.
\<close>

theory Multiset
imports Main
begin

subsection \<open>A minimal multiset theory\<close>

text \<open>
  Völzer, p. 84, does specify that messages in transit are modelled using
  multisets.
  
  We decided to implement a tiny structure for multisets, just fitting our needs.
  These multisets allow to add new values to them, to check for elements existing
  in a certain multiset, filter elements according to boolean predicates, remove
  elements and to create a new multiset from a single element.
\<close>

text \<open>
  A multiset for a type is a mapping from the elements of the type to natural
  numbers. So, we record how often a message has to be processed in the future.
\<close>

type_synonym 'a multiset = "'a \<Rightarrow> nat"

abbreviation mElem ::
  "'a \<Rightarrow> 'a multiset \<Rightarrow> bool" ("_ \<in># _" 60)
where 
  "mElem a ms \<equiv> 0 < ms a"

text \<open>
  Hence the union of two multisets is the addition of the number of the
  elements and therefore the associative and the commutative laws holds for
  the union.
\<close>

abbreviation mUnion ::
  "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" ("_ \<union># _" 70)
where
  "mUnion msA msB v \<equiv> msA v + msB v"

text \<open>
  Correspondingly the subtraction is defined and the commutative law holds.
\<close>
abbreviation mRm ::
  "'a multiset \<Rightarrow> 'a \<Rightarrow> 'a multiset" ("_ -# _" 65)
where
  "mRm ms rm v \<equiv> if v = rm then ms v - 1 else ms v"

abbreviation mSingleton ::
  "'a \<Rightarrow> 'a multiset"          ("{# _ }")
where
  "mSingleton a v \<equiv> if a = v then 1 else 0"

text \<open>
  The lemma \isb{AXc} adds just the fact we need for our proofs about
  the commutativity of the union of multisets while elements are removed.
\<close>
lemma AXc:
assumes 
  "c1 \<noteq> c2" and 
  "c1 \<in># X" and
  "c2 \<in># X"
shows "(A1 \<union># ((A2 \<union># (X -# c2)) -# c1)) 
      = (A2 \<union># ((A1 \<union># (X -# c1)) -# c2))"
proof- 
  have 
    "(A2 \<union># ((A1 \<union># (X -# c1)) -# c2)) 
         = (A2 \<union># (A1 \<union># ((X -# c1) -# c2)))" 
    using assms by auto
  also have
    "... = (A1 \<union># ((A2 \<union># (X -# c2)) -# c1)) "
    using assms by auto
  finally show ?thesis by auto
qed

end
