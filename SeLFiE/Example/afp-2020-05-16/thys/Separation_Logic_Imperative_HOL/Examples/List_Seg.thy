section \<open>Singly Linked List Segments\<close>
theory List_Seg
imports "../Sep_Main"
begin

subsection \<open>Nodes\<close>
text \<open>
  We define a node of a list to contain a data value and a next pointer.
  As Imperative HOL does not support null-pointers, we make the next-pointer
  an optional value, \<open>None\<close> representing a null pointer.

  Unfortunately, Imperative HOL requires some boilerplate code to define 
  a datatype.
\<close>
setup \<open>Sign.add_const_constraint 
  (@{const_name Ref}, SOME @{typ "nat \<Rightarrow> 'a::type ref"})\<close>

datatype 'a node = Node "'a" "'a node ref option"

setup \<open>Sign.add_const_constraint 
  (@{const_name Ref}, SOME @{typ "nat \<Rightarrow> 'a::heap ref"})\<close>

setup \<open>Sign.add_const_constraint (@{const_name Node}, 
  SOME @{typ "'a::heap \<Rightarrow> 'a node ref option \<Rightarrow> 'a node"})\<close>

text \<open>Selector Functions\<close>
primrec val :: "'a::heap node \<Rightarrow> 'a" where
  [sep_dflt_simps]: "val (Node x _) = x"

primrec "next" :: "'a::heap node \<Rightarrow> 'a node ref option" where
  [sep_dflt_simps]: "next (Node _ r) = r"

text \<open>Encoding to natural numbers, as required by Imperative/HOL\<close>
fun
  node_encode :: "'a::heap node \<Rightarrow> nat"
where
  "node_encode (Node x r) = to_nat (x, r)"

instance node :: (heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "node_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

subsection \<open>List Segment Assertion\<close>
text \<open>
  Intuitively, \<open>lseg l p s\<close> describes a list starting at \<open>p\<close> and
  ending with a pointer \<open>s\<close>. The content of the list are \<open>l\<close>.
  Note that the pointer \<open>s\<close> may also occur earlier in the list, in which
  case it is handled as a usual next-pointer.
\<close>
fun lseg 
  :: "'a::heap list \<Rightarrow> 'a node ref option \<Rightarrow> 'a node ref option \<Rightarrow> assn"
  where
  "lseg [] p s = \<up>(p=s)"
| "lseg (x#l) (Some p) s = (\<exists>\<^sub>Aq. p \<mapsto>\<^sub>r Node x q * lseg l q s)"
| "lseg (_#_) None _ = false"

lemma lseg_if_splitf1[simp, sep_dflt_simps]: 
  "lseg l None None = \<up>(l=[])"
  apply (cases l, simp_all)
  done

lemma lseg_if_splitf2[simp, sep_dflt_simps]: 
  "lseg (x#xs) p q 
    = (\<exists>\<^sub>App n. pp \<mapsto>\<^sub>r (Node x n) * lseg xs n q * \<up>(p=Some pp))"
  apply (cases p, simp_all)
  (* TODO: One-point simproc for assertions! *)
  apply (rule ent_iffI)
  apply solve_entails
  apply solve_entails
  done


subsection \<open>Lemmas\<close>

subsubsection \<open>Concatenation\<close>
lemma lseg_prepend: 
  "p\<mapsto>\<^sub>rNode x q * lseg l q s \<Longrightarrow>\<^sub>A lseg (x#l) (Some p) s"
  by sep_auto

lemma lseg_append: 
  "lseg l p (Some s) * s\<mapsto>\<^sub>rNode x q \<Longrightarrow>\<^sub>A lseg (l@[x]) p q"
proof (induction l arbitrary: p)
  case Nil thus ?case by sep_auto
next
  case (Cons y l)
  show ?case
    apply (cases p)
    apply simp
    apply (sep_auto)
    apply (rule ent_frame_fwd[OF Cons.IH])
    apply frame_inference
    apply solve_entails
    done
qed

lemma lseg_conc: "lseg l1 p q * lseg l2 q r \<Longrightarrow>\<^sub>A lseg (l1@l2) p r"
proof (induct l1 arbitrary: p)
  case Nil thus ?case by simp
next
  case (Cons x l1)
  show ?case
    apply simp
    apply sep_auto
    apply (rule ent_frame_fwd[OF Cons.hyps])
    apply frame_inference
    apply solve_entails
    done
qed

subsubsection \<open>Splitting\<close>
lemma lseg_split: 
  "lseg (l1@l2) p r \<Longrightarrow>\<^sub>A \<exists>\<^sub>Aq. lseg l1 p q * lseg l2 q r"
proof (induct l1 arbitrary: p)
  case Nil thus ?case by sep_auto
next
  case (Cons x l1)

  have "lseg ((x # l1) @ l2) p r 
    \<Longrightarrow>\<^sub>A \<exists>\<^sub>App n. pp \<mapsto>\<^sub>r Node x n * lseg (l1 @ l2) n r * \<up> (p = Some pp)"
    by simp
  also have "\<dots> \<Longrightarrow>\<^sub>A 
    \<exists>\<^sub>App n q. pp \<mapsto>\<^sub>r Node x n 
      * lseg l1 n q 
      * lseg l2 q r 
      * \<up>(p = Some pp)"
    apply (intro ent_ex_preI)
    apply clarsimp
    apply (rule ent_frame_fwd[OF Cons.hyps])
    apply frame_inference
    apply sep_auto
    done
  also have "\<dots> \<Longrightarrow>\<^sub>A \<exists>\<^sub>Aq. lseg (x#l1) p q * lseg l2 q r"
    by sep_auto
  finally show ?case .
qed

subsubsection \<open>Precision\<close>
lemma lseg_prec1: 
  "\<forall>l l'. (h\<Turnstile>
      (lseg l p (Some q) * q \<mapsto>\<^sub>r x * F1) 
       \<and>\<^sub>A (lseg l' p (Some q) * q \<mapsto>\<^sub>r x * F2)) 
    \<longrightarrow> l=l'"
  apply (intro allI)
  subgoal for l l'
  proof (induct l arbitrary: p l' F1 F2)
    case Nil thus ?case
      apply simp_all
      apply (cases l')
      apply simp
      apply auto
      done
  next
    case (Cons y l)
    from Cons.prems show ?case
      apply (cases l')
      apply auto []
      apply (cases p)
      apply simp
      
      apply (clarsimp)

      apply (subgoal_tac "y=a \<and> na=n", simp)

      using Cons.hyps apply (erule prec_frame')
      apply frame_inference
      apply frame_inference

      apply (drule_tac p=aa in prec_frame[OF sngr_prec])
      apply frame_inference
      apply frame_inference
      apply simp
      done
  qed
  done

lemma lseg_prec2: 
  "\<forall>l l'. (h\<Turnstile>
      (lseg l p None * F1) \<and>\<^sub>A (lseg l' p None * F2)) 
    \<longrightarrow> l=l'"
  apply (intro allI)
  subgoal for l l'
  proof (induct l arbitrary: p l' F1 F2)
    case Nil thus ?case
      apply simp_all
      apply (cases l')
      apply simp
      apply (cases p)
      apply auto
      done
  next
    case (Cons y l)
    from Cons.prems show ?case
      apply (cases p)
      apply simp
      apply (cases l')
      apply (auto) []
      
      apply (clarsimp)

      apply (subgoal_tac "y=aa \<and> na=n", simp)

      using Cons.hyps apply (erule prec_frame')
      apply frame_inference
      apply frame_inference

      apply (drule_tac p=a in prec_frame[OF sngr_prec])
      apply frame_inference
      apply frame_inference
      apply simp
      done
  qed
  done

lemma lseg_prec3: 
  "\<forall>q q'. h \<Turnstile> (lseg l p q * F1) \<and>\<^sub>A (lseg l p q' * F2) \<longrightarrow> q=q'"
  apply (intro allI)
proof (induct l arbitrary: p F1 F2)
  case Nil thus ?case by auto
next
  case (Cons x l)
  show ?case
    apply auto

    apply (subgoal_tac "na=n")
    using Cons.hyps apply (erule prec_frame')
    apply frame_inference
    apply frame_inference

    apply (drule prec_frame[OF sngr_prec])
    apply frame_inference
    apply frame_inference
    apply simp
    done
qed

end
