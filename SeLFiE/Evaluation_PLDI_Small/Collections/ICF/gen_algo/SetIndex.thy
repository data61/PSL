(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section \<open>\isaheader{Indices of Sets}\<close>
theory SetIndex
imports 
  "../spec/MapSpec"
  "../spec/SetSpec"
begin
text_raw \<open>\label{thy:SetIndex}\<close>

text \<open>
  This theory defines an indexing operation that builds an index from a set 
  and an indexing function. 

  Here, index is a map from indices to all values of the set with that index.
\<close>

subsection "Indexing by Function"

definition index :: "('a \<Rightarrow> 'i) \<Rightarrow> 'a set \<Rightarrow> 'i \<Rightarrow> 'a set"
  where "index f s i == { x\<in>s . f x = i }"

lemma indexI: "\<lbrakk> x\<in>s; f x = i \<rbrakk> \<Longrightarrow> x\<in>index f s i" by (unfold index_def) auto
lemma indexD: 
  "x\<in>index f s i \<Longrightarrow> x\<in>s"
  "x\<in>index f s i \<Longrightarrow> f x = i"
  by (unfold index_def) auto

lemma index_iff[simp]: "x\<in>index f s i \<longleftrightarrow> x\<in>s \<and> f x = i" by (simp add: index_def)
 
subsection "Indexing by Map"

definition index_map :: "('a \<Rightarrow> 'i) \<Rightarrow> 'a set \<Rightarrow> 'i \<rightharpoonup> 'a set"
  where "index_map f s i == let s=index f s i in if s={} then None else Some s"

definition im_\<alpha> where "im_\<alpha> im i == case im i of None \<Rightarrow> {} | Some s \<Rightarrow> s"

lemma index_map_correct: "im_\<alpha> (index_map f s) = index f s"
  apply (rule ext)
  apply (unfold index_def index_map_def im_\<alpha>_def)
  apply auto
  done

subsection "Indexing by Maps and Sets from the Isabelle Collections Framework"
text \<open>
  In this theory, we define the generic algorithm as constants outside any locale,
  but prove the correctness lemmas inside a locale that assumes correctness of all
  prerequisite functions.
  Finally, we export the correctness lemmas from the locale.
\<close>

locale index_loc = 
  m: StdMap m_ops +
  s: StdSet s_ops
  for m_ops :: "('i,'s,'m,'more1) map_ops_scheme"
  and s_ops :: "('x,'s,'more2) set_ops_scheme"
begin
  \<comment> \<open>Mapping indices to abstract indices\<close>
  definition ci_\<alpha>' where
    "ci_\<alpha>' ci i == case m.\<alpha> ci i of None \<Rightarrow> None | Some s \<Rightarrow> Some (s.\<alpha> s)"

  definition "ci_\<alpha> == im_\<alpha> \<circ> ci_\<alpha>'"

  definition ci_invar where
    "ci_invar ci == m.invar ci \<and> (\<forall>i s. m.\<alpha> ci i = Some s \<longrightarrow> s.invar s)"

  lemma ci_impl_minvar: "ci_invar m \<Longrightarrow> m.invar m" by (unfold ci_invar_def) auto

  definition is_index :: "('x \<Rightarrow> 'i) \<Rightarrow> 'x set \<Rightarrow> 'm \<Rightarrow> bool"
  where
    "is_index f s idx == ci_invar idx \<and> ci_\<alpha>' idx = index_map f s"

  lemma is_index_invar: "is_index f s idx \<Longrightarrow> ci_invar idx" 
    by (simp add: is_index_def)

  lemma is_index_correct: "is_index f s idx \<Longrightarrow> ci_\<alpha> idx = index f s"
    by (simp only: is_index_def index_map_def ci_\<alpha>_def)
       (simp add: index_map_correct)

  definition lookup :: "'i \<Rightarrow> 'm \<Rightarrow> 's" where
    "lookup i m == case m.lookup i m of None \<Rightarrow> (s.empty ()) | Some s \<Rightarrow> s"

  lemma lookup_invar': "ci_invar m \<Longrightarrow> s.invar (lookup i m)"
    apply (unfold ci_invar_def lookup_def)
    apply (auto split: option.split simp add: m.lookup_correct s.empty_correct)
    done

  lemma lookup_correct:
    assumes I[simp, intro!]: "is_index f s idx"
    shows 
      "s.\<alpha> (lookup i idx) = index f s i"
      "s.invar (lookup i idx)"
  proof goal_cases
    case 2 thus ?case using I by (simp add: is_index_def lookup_invar')
  next
    case 1 
    have [simp, intro!]: "m.invar idx" 
      using ci_impl_minvar[OF is_index_invar[OF I]] 
      by simp
    thus ?case 
    proof (cases "m.lookup i idx")
      case None
      hence [simp]: "m.\<alpha> idx i = None" by (simp add: m.lookup_correct)
      from is_index_correct[OF I] have "index f s i = ci_\<alpha> idx i" by simp
      also have "\<dots> = {}" by (simp add: ci_\<alpha>_def ci_\<alpha>'_def im_\<alpha>_def)
      finally show ?thesis by (simp add: lookup_def None s.empty_correct)
    next
      case (Some si)
      hence [simp]: "m.\<alpha> idx i = Some si" by (simp add: m.lookup_correct)
      from is_index_correct[OF I] have "index f s i = ci_\<alpha> idx i" by simp
      also have "\<dots> = s.\<alpha> si" by (simp add: ci_\<alpha>_def ci_\<alpha>'_def im_\<alpha>_def)
      finally show ?thesis by (simp add: lookup_def Some s.empty_correct)
    qed
  qed

end

locale build_index_loc = index_loc m_ops s_ops +
  t: StdSet t_ops
  for m_ops :: "('i,'s,'m,'more1) map_ops_scheme"
  and s_ops :: "('x,'s,'more3) set_ops_scheme"
  and t_ops :: "('x,'t,'more2) set_ops_scheme"
begin

  text "Building indices"
  definition idx_build_stepfun :: "('x \<Rightarrow> 'i) \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> 'm" where
    "idx_build_stepfun f x m == 
      let i=f x in
        (case m.lookup i m of
          None \<Rightarrow> m.update i (s.ins x (s.empty ())) m |
          Some s \<Rightarrow> m.update i (s.ins x s) m
      )"

  definition idx_build :: "('x \<Rightarrow> 'i) \<Rightarrow> 't \<Rightarrow> 'm" where
    "idx_build f t == t.iterate t (idx_build_stepfun f) (m.empty ())"

  lemma idx_build_correct:
    assumes I: "t.invar t"
    shows "ci_\<alpha>' (idx_build f t) = index_map f (t.\<alpha> t)" (is ?T1) and
    [simp]: "ci_invar (idx_build f t)" (is ?T2)
  proof -
    have "t.invar t \<Longrightarrow> 
      ci_\<alpha>' (idx_build f t) = index_map f (t.\<alpha> t) \<and> ci_invar (idx_build f t)"
      apply (unfold idx_build_def)
      apply (rule_tac 
          I="\<lambda>it m. ci_\<alpha>' m = index_map f (t.\<alpha> t - it) \<and> ci_invar m" 
          in t.iterate_rule_P)
      apply assumption
      apply (simp add: ci_invar_def m.empty_correct)
      apply (rule ext)
      apply (unfold ci_\<alpha>'_def index_map_def index_def)[1]
      apply (simp add: m.empty_correct)
      defer
      apply simp
      apply (rule conjI)
      defer
      apply (unfold idx_build_stepfun_def)[1]
      apply (auto 
        simp add: ci_invar_def m.update_correct m.lookup_correct 
                  s.empty_correct s.ins_correct Let_def 
        split: option.split) [1]
        
      apply (rule ext)
    proof goal_cases
      case prems: (1 x it m i)
      hence INV[simp, intro!]: "m.invar m" by (simp add: ci_invar_def)
      from prems have 
        INVS[simp, intro]: "!!q s. m.\<alpha> m q = Some s \<Longrightarrow> s.invar s" 
        by (simp add: ci_invar_def)
      
      show ?case proof (cases "i=f x")
        case [simp]: True
        show ?thesis proof (cases "m.\<alpha> m (f x)")
          case [simp]: None
          hence "idx_build_stepfun f x m = m.update i (s.ins x (s.empty ())) m"
            apply (unfold idx_build_stepfun_def) 
            apply (simp add: m.update_correct m.lookup_correct s.empty_correct)
            done
          hence "ci_\<alpha>' (idx_build_stepfun f x m) i = Some {x}"
            by (simp add: m.update_correct 
                          s.ins_correct s.empty_correct ci_\<alpha>'_def)
          also {
            have "None = ci_\<alpha>' m (f x)" 
              by (simp add: ci_\<alpha>'_def)
            also from prems(4) have "\<dots> = index_map f (t.\<alpha> t - it) i" by simp
            finally have E: "{xa \<in> t.\<alpha> t - it. f xa = i} = {}" 
              by (simp add: index_map_def index_def split: if_split_asm)
            moreover have 
              "{xa \<in> t.\<alpha> t - (it - {x}). f xa = i} 
               = {xa \<in> t.\<alpha> t - it. f xa = i} \<union> {x}"
              using prems(2,3) by auto
            ultimately have "Some {x} = index_map f (t.\<alpha> t - (it - {x})) i"
              by (unfold index_map_def index_def) auto
          } finally show ?thesis .
        next
          case [simp]: (Some ss)
          hence [simp, intro!]: "s.invar ss" by (simp del: Some)
          hence "idx_build_stepfun f x m = m.update (f x) (s.ins x ss) m"
            by (unfold idx_build_stepfun_def) 
               (simp add: m.update_correct m.lookup_correct)
          hence "ci_\<alpha>' (idx_build_stepfun f x m) i = Some (insert x (s.\<alpha> ss))"
            by (simp add: m.update_correct s.ins_correct ci_\<alpha>'_def)
          also {
              have "Some (s.\<alpha> ss) = ci_\<alpha>' m (f x)" 
                by (simp add: ci_\<alpha>'_def)
            also from prems(4) have "\<dots> = index_map f (t.\<alpha> t - it) i" by simp
            finally have E: "{xa \<in> t.\<alpha> t - it. f xa = i} = s.\<alpha> ss" 
              by (simp add: index_map_def index_def split: if_split_asm)
            moreover have 
              "{xa \<in> t.\<alpha> t - (it - {x}). f xa = i} 
               = {xa \<in> t.\<alpha> t - it. f xa = i} \<union> {x}"
              using prems(2,3) by auto
            ultimately have 
              "Some (insert x (s.\<alpha> ss)) = index_map f (t.\<alpha> t - (it - {x})) i"
              by (unfold index_map_def index_def) auto
          }
          finally show ?thesis .
        qed
      next
        case False hence C: "i\<noteq>f x" "f x\<noteq>i" by simp_all
        have "ci_\<alpha>' (idx_build_stepfun f x m) i = ci_\<alpha>' m i"
          apply (unfold ci_\<alpha>'_def idx_build_stepfun_def)
          apply (simp 
            split: option.split_asm option.split 
            add: Let_def m.lookup_correct m.update_correct 
                 s.ins_correct s.empty_correct C)
          done
        also from prems(4) have "ci_\<alpha>' m i = index_map f (t.\<alpha> t - it) i" 
          by simp
        also have 
          "{xa \<in> t.\<alpha> t - (it - {x}). f xa = i} = {xa \<in> t.\<alpha> t - it. f xa = i}"
          using prems(2,3) C by auto
        hence "index_map f (t.\<alpha> t - it) i = index_map f (t.\<alpha> t - (it-{x})) i"
          by (unfold index_map_def index_def) simp
        finally show ?thesis .
      qed
    qed
    with I show ?T1 ?T2 by auto
  qed

  lemma idx_build_is_index: 
    "t.invar t \<Longrightarrow> is_index f (t.\<alpha> t) (idx_build f t)"
    by (simp add: idx_build_correct index_map_correct ci_\<alpha>_def is_index_def)

end

end
