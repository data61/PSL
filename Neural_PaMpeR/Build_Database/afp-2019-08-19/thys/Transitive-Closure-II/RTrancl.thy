(*  Title:       Executable Transitive Closures 
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2012 Christian Sternagel, René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

section \<open>A work-list algorithm for reflexive-transitive closures\<close>


theory RTrancl
imports "Regular-Sets.Regexp_Method"
begin

text \<open>In previous work \cite{rtrancl_fin} we described a generic work-list
algorithm to compute reflexive-transitive closures for \emph{finite} relations:
given a finite relation $r$, it computed $@{term "r^*"}$. 

In the following, we develop a similar, though different work-list algorithm
for reflexive-transitive closures, it computes @{term "r^* `` init"} for a given
relation $r$ and finite set @{term "init"}.
The main differences are that
\begin{itemize}
\item The relation $r$ does not have to be finite, only @{term "{b. (a,b) \<in> r^* }"} has to be finite
  for each $a$. Moreover, it is no longer required that $r$ is given 
  explicitly as a list of pairs.
 Instead $r$ must be provided in the form of a function which computes 
  for each element the
  set of one-step successors.
\item One can use a subsumption relation to indicate which elements to no longer
  have to be explored.
\end{itemize}

These new features have been essential to certify size-change termination 
proofs \cite{sct} where the transitive closure of all size-change graphs 
has to be computed. Here, the relation is size-change graph composition.
\begin{itemize}
\item Given an initial set of size-change graphs with $n$ arguments, 
  there are roughly $N := 3^{n^2}$ many potential size-change graphs that
  have to be considered as left-hand sides of the composition relation. 
  Since the composition relation is even larger than $N$,
  an explicit representation of the composition relation would have been 
  too expensive. However, using the new algorithm the number of generated
  graphs is usually far below the theoretical upper bound.
\item Subsumption was useful to generate even fewer elements.
\end{itemize}

\<close>

subsection \<open>The generic case\<close>

text \<open>
  Let $r$ be some finite relation.

  We present a standard work-list algorithm to compute all elements
  that are reachable from some initial set. 
  The algorithm is generic in the sense that the
  underlying data structure can freely be chosen, you just have to provide
  certain operations like union, selection of an element. 

  In contrast to \cite{rtrancl_fin}, the algorithm does not demand that $r$ is finite
  and that $r$ is explicitly provided (e.g., as a list of pairs).
  Instead, it suffices that for every element, only finitely many 
  elements can be reached via $r$, and $r$ can be provided as a function which
  computes for every element $a$ all one-step successors w.r.t.\ $r$. 
  Hence, $r$ can in particular be any 
  well-founded and finitely branching relation. 
  
  The algorithm can further be parametrized by a subsumption relation 
  which allows for early pruning. 
\<close>

text \<open>In the following locales, $r$ is a relation of type @{typ "'a \<Rightarrow> 'a"},
  the successors of an element are represented by some collection 
  type @{typ 'b} which size can be measured using the @{term size} function. 
  The selection function @{term sel} is used to meant to split a non-empty
  collection into one element and a remaining collection. The union on
  @{typ 'b} is given by @{term un}.
\<close> 

locale subsumption = 
  fixes r :: "'a \<Rightarrow> 'b"
   and subsumes :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
   and set_of :: "'b \<Rightarrow> 'a set"
  assumes 
       subsumes_refl: "\<And> a. subsumes a a"
   and subsumes_trans: "\<And> a b c. subsumes a b \<Longrightarrow> subsumes b c \<Longrightarrow> subsumes a c"
   and subsumes_step: "\<And> a b c. subsumes a b \<Longrightarrow> c \<in> set_of (r b) \<Longrightarrow> \<exists> d \<in> set_of (r a). subsumes d c"
begin
abbreviation R where "R \<equiv> { (a,b). b \<in> set_of (r a) }"
end

locale subsumption_impl = subsumption r subsumes set_of
  for r :: "'a \<Rightarrow> 'b"
  and subsumes :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and set_of :: "'b \<Rightarrow> 'a set" +
  fixes 
      sel :: "'b \<Rightarrow> 'a \<times> 'b" 
   and un :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
   and size :: "'b \<Rightarrow> nat"
  assumes set_of_fin: "\<And> b. finite (set_of b)"
   and sel: "\<And> b a c. set_of b \<noteq> {} \<Longrightarrow> sel b = (a,c) \<Longrightarrow> set_of b = insert a (set_of c) \<and> size b > size c"
   and un: "set_of (un a b) = set_of a \<union> set_of b"

locale relation_subsumption_impl = subsumption_impl r subsumes set_of sel un size
  for r subsumes set_of sel un size +
  assumes rtrancl_fin: "\<And> a. finite {b. (a,b) \<in> { (a,b) . b \<in> set_of (r a)}^*}"
begin


lemma finite_Rs: assumes init: "finite init"
  shows "finite (R^* `` init)"
proof -
  let ?R = "\<lambda> a. {b . (a,b) \<in> R^*}"
  let ?S = "{ ?R a | a . a \<in> init}"
  have id: "R^* `` init = \<Union> ?S" by auto
  show ?thesis unfolding id
  proof (rule)
    fix M
    assume "M \<in> ?S"
    then obtain a where M: "M = ?R a" by auto
    show "finite M" unfolding M by (rule rtrancl_fin)
  next
    show "finite {{b. (a, b) \<in> R^*} | a. a \<in> init}"
      using init by auto
  qed
qed

text \<open>a standard work-list algorithm with subsumption\<close>
function mk_rtrancl_main where 
  "mk_rtrancl_main todo fin = (if set_of todo = {} then fin
      else (let (a,tod) = sel todo
             in (if (\<exists> b \<in> fin. subsumes b a) then mk_rtrancl_main tod fin
                 else mk_rtrancl_main (un (r a) tod) (insert a fin))))" 
  by pat_completeness auto


termination mk_rtrancl_main 
proof -
  let ?r1 = "\<lambda> (todo, fin). card (R^* `` (set_of todo) - fin)"
  let ?r2 = "\<lambda> (todo, fin). size todo"
  show ?thesis
  proof
    show "wf (measures [?r1,?r2])" by simp
  next
    fix todo fin pair tod a
    assume nempty: "set_of todo \<noteq> {}" and pair1: "pair = sel todo" and pair2: "(a,tod) = pair"
    from pair1 pair2 have pair: "sel todo = (a,tod)" by simp
    from set_of_fin have fin: "finite (set_of todo)" by auto
    note sel = sel[OF nempty pair]
    show "((tod,fin),(todo,fin)) \<in> measures [?r1,?r2]"
    proof (rule measures_lesseq[OF _ measures_less], unfold split)
      from sel 
      show "size tod < size todo" by simp
    next
      from sel have subset: "R^* `` set_of tod - fin \<subseteq> R^* `` set_of todo - fin" (is "?l \<subseteq> ?r") by auto
      show "card ?l \<le> card ?r"
        by (rule card_mono[OF _ subset], rule finite_Diff, rule finite_Rs[OF fin])
    qed
  next
    fix todo fin a tod pair
    assume nempty: "set_of todo \<noteq> {}" and pair1: "pair = sel todo" and pair2: "(a,tod) = pair" and nmem: "\<not> (\<exists> b \<in> fin. subsumes b a)"
    from pair1 pair2 have pair: "sel todo = (a,tod)" by auto
    from nmem subsumes_refl[of a] have nmem: "a \<notin> fin" by auto
    from set_of_fin have fin: "finite (set_of todo)" by auto
    note sel = sel[OF nempty pair]
    show "((un (r a) tod,insert a fin),(todo,fin)) \<in> measures [?r1,?r2]"
    proof (rule measures_less, unfold split, 
        rule psubset_card_mono[OF finite_Diff[OF finite_Rs[OF fin]]])
      let ?l = "R^* `` set_of (un (r a) tod) - insert a fin"
      let ?r = "R^* `` set_of todo - fin"
      from sel have at: "a \<in> set_of todo" by auto
      have ar: "a \<in> ?r" using nmem at by auto
      show "?l \<subset> ?r"
      proof
        show "?l \<noteq> ?r" using ar by auto
      next
        have "R^* `` set_of (r a) \<subseteq> R^* `` set_of todo"
        proof
          fix b
          assume "b \<in> R^* `` set_of (r a)"
          then obtain c where cb: "(c,b) \<in> R^*" and ca: "c \<in> set_of (r a)" by blast
          hence ab: "(a,b) \<in> R O R^*" by auto
          have "(a,b) \<in> R^*" 
            by (rule subsetD[OF _ ab], regexp)
          with at show "b \<in> R^* `` set_of todo" by auto
        qed
        thus "?l \<subseteq> ?r" using sel unfolding un by auto
      qed
    qed
  qed
qed
      
declare mk_rtrancl_main.simps[simp del]

lemma mk_rtrancl_main_sound: "set_of todo \<union> fin \<subseteq> R^* `` init \<Longrightarrow> mk_rtrancl_main todo fin \<subseteq> R^* `` init"
proof (induct todo fin rule: mk_rtrancl_main.induct)
  case (1 todo fin)
  note simp = mk_rtrancl_main.simps[of todo fin]
  show ?case
  proof (cases "set_of todo = {}")
    case True
    show ?thesis unfolding simp using True 1(3) by auto
  next
    case False
    hence nempty: "(set_of todo = {}) = False" by auto
    obtain a tod where selt: "sel todo = (a,tod)" by force
    note sel = sel[OF False selt]
    note IH1 = 1(1)[OF False refl selt[symmetric]]
    note IH2 = 1(2)[OF False refl selt[symmetric]]
    note simp = simp nempty if_False Let_def selt
    show ?thesis 
    proof (cases "\<exists> b \<in> fin. subsumes b a")
      case True
      hence "mk_rtrancl_main todo fin = mk_rtrancl_main tod fin"
        unfolding simp by simp
      with IH1[OF True] 1(3) show ?thesis using sel by auto
    next
      case False
      hence id: "mk_rtrancl_main todo fin = mk_rtrancl_main (un (r a) tod) (insert a fin)" unfolding simp by simp
      show ?thesis unfolding id
      proof (rule IH2[OF False])
        from sel 1(3) have subset: "set_of todo \<union> insert a fin \<subseteq> R^* `` init" by auto
        {
          fix b
          assume b: "b \<in> set_of (r a)"
          hence ab: "(a,b) \<in> R" by auto
          from sel 1(3) have "a \<in> R^* `` init" by auto
          then obtain c where c: "c \<in> init" and ca: "(c,a) \<in> R^*" by blast
          from ca ab have cb: "(c,b) \<in> R^* O R" by auto
          have "(c,b) \<in> R^*" 
            by (rule subsetD[OF _ cb], regexp)
          with c have "b \<in> R^* `` init" by auto
        }
        with subset
        show "set_of (un (r a) tod) \<union> (insert a fin) \<subseteq> R^* `` init" 
          unfolding un using sel by auto
      qed
    qed
  qed
qed

lemma mk_rtrancl_main_complete: 
  "\<lbrakk>\<And> a. a \<in> init \<Longrightarrow> \<exists> b. b \<in> set_of todo \<union> fin \<and> subsumes b a\<rbrakk> 
  \<Longrightarrow> \<lbrakk> \<And> a b . a \<in> fin \<Longrightarrow> b \<in> set_of (r a) \<Longrightarrow> \<exists> c. c \<in> set_of todo \<union> fin \<and> subsumes c b\<rbrakk> 
  \<Longrightarrow> c \<in> R^* `` init 
  \<Longrightarrow> \<exists> b. b \<in> mk_rtrancl_main todo fin \<and> subsumes b c"
proof (induct todo fin rule: mk_rtrancl_main.induct)
  case (1 todo fin)
  from 1(5) have c: "c \<in> R^* `` init" .
  note finr = 1(4)
  note init = 1(3)
  note simp = mk_rtrancl_main.simps[of todo fin]
  show ?case
  proof (cases "set_of todo = {}")
    case True
    hence id: "mk_rtrancl_main todo fin = fin" unfolding simp by simp
    from c obtain a where a: "a \<in> init" and ac: "(a,c) \<in> R^*" by blast
    show ?thesis unfolding id using ac
    proof (induct rule: rtrancl_induct)
      case base
      from init[OF a] show ?case unfolding True by auto
    next
      case (step b c)
      from step(3) obtain d where d: "d \<in> fin" and db: "subsumes d b" by auto
      from step(2) have cb: "c \<in> set_of (r b)" by auto
      from subsumes_step[OF db cb] obtain a where a: "a \<in> set_of (r d)" and ac: "subsumes a c" by auto
      from finr[OF d a] obtain e where e: "e \<in> fin" and ea: "subsumes e a" unfolding True by auto
      from subsumes_trans[OF ea ac] e
      show ?case by auto
    qed
  next
    case False
    hence nempty: "(set_of todo = {}) = False" by simp
    obtain A tod where selt: "sel todo = (A,tod)" by force
    note simp = nempty simp if_False Let_def selt
    note sel = sel[OF False selt]
    note IH1 = 1(1)[OF False refl selt[symmetric] _ _ _ c]
    note IH2 = 1(2)[OF False refl selt[symmetric] _ _ _ c]
    show ?thesis 
    proof (cases "\<exists> b \<in> fin. subsumes b A")
      case True note oTrue = this
      hence id: "mk_rtrancl_main todo fin = mk_rtrancl_main tod fin"
        unfolding simp by simp
      from True obtain b where b: "b \<in> fin" and ba: "subsumes b A" by auto
      show ?thesis unfolding id
      proof (rule IH1[OF True])
        fix a 
        assume a: "a \<in> init"
        from init[OF a] obtain c where c: "c \<in> set_of todo \<union> fin" and ca: "subsumes c a" by blast        
        show "\<exists> b. b \<in> set_of tod \<union> fin \<and> subsumes b a"
        proof (cases "c = A")
          case False
          thus ?thesis using c ca sel by auto
        next
          case True
          show ?thesis using b subsumes_trans[OF ba, of a] ca unfolding True[symmetric] by auto
        qed
      next
        fix a c
        assume a: "a \<in> fin" and c: "c \<in> set_of (r a)"
        from finr[OF a c] obtain e where e: "e \<in> set_of todo \<union> fin" and ec: "subsumes e c" by auto
        show "\<exists> d. d \<in> set_of tod \<union> fin \<and> subsumes d c"
        proof (cases "A = e")
          case False
          with e ec show ?thesis using sel by auto
        next
          case True
          from subsumes_trans[OF ba[unfolded True] ec] 
          show ?thesis using b by auto
        qed
      qed
    next
      case False
      hence id: "mk_rtrancl_main todo fin = mk_rtrancl_main (un (r A) tod) (insert A fin)" unfolding simp by simp
      show ?thesis unfolding id
      proof (rule IH2[OF False])
        fix a
        assume a: "a \<in> init"
        from init[OF a]
        show "\<exists> b. b \<in> set_of (un (r A) (tod)) \<union> insert A fin \<and> subsumes b a" 
          using sel unfolding un by auto
      next
        fix a b
        assume a: "a \<in> insert A fin" and b: "b \<in> set_of (r a)"
        show "\<exists> c. c \<in> set_of (un (r A) tod) \<union> insert A fin \<and> subsumes c b"
        proof (cases "a \<in> fin")
          case True
          from finr[OF True b] show ?thesis using sel unfolding un by auto
        next
          case False
          with a have a: "A = a" by simp
          show ?thesis unfolding a un using b subsumes_refl[of b] by blast
        qed
      qed
    qed
  qed
qed

definition mk_rtrancl where "mk_rtrancl init \<equiv> mk_rtrancl_main init {}"

lemma mk_rtrancl_sound: "mk_rtrancl init \<subseteq> R^* `` set_of init"
  unfolding mk_rtrancl_def
  by (rule mk_rtrancl_main_sound, auto)

lemma mk_rtrancl_complete: assumes a: "a \<in> R^* `` set_of init"
  shows "\<exists> b. b \<in> mk_rtrancl init \<and> subsumes b a"
  unfolding mk_rtrancl_def
proof (rule mk_rtrancl_main_complete[OF _ _ a])
  fix a 
  assume a: "a \<in> set_of init"
  thus "\<exists> b. b \<in> set_of init \<union> {} \<and> subsumes b a" using subsumes_refl[of a] by blast
qed auto

lemma mk_rtrancl_no_subsumption: assumes "subsumes = (=)"
  shows "mk_rtrancl init = R^* `` set_of init"
  using mk_rtrancl_sound[of init] mk_rtrancl_complete[of _ init] assms
  by auto
end

subsection \<open>Instantiation using list operations\<close>

text \<open>It follows an implementation based on lists. 
 Here, the working list algorithm is implemented outside the locale so that
 it can be used for code generation. In general, it is not terminating, 
 therefore we use partial\_function instead of function.\<close>

partial_function(tailrec) mk_rtrancl_list_main where 
 [code]:  "mk_rtrancl_list_main subsumes r todo fin = (case todo of [] \<Rightarrow> fin
     | Cons a tod \<Rightarrow> 
             (if (\<exists> b \<in> set fin. subsumes b a) then mk_rtrancl_list_main subsumes r tod fin
                 else mk_rtrancl_list_main subsumes r (r a @ tod) (a # fin)))" 

definition mk_rtrancl_list where 
  "mk_rtrancl_list subsumes r init \<equiv> mk_rtrancl_list_main subsumes r init []"

locale subsumption_list = subsumption r subsumes set
  for r :: "'a \<Rightarrow> 'a list" and subsumes :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

locale relation_subsumption_list = subsumption_list r subsumes for r subsumes +
  assumes rtrancl_fin: "\<And> a. finite {b. (a,b) \<in> { (a,b) . b \<in> set (r a)}^*}"

abbreviation(input) sel_list where "sel_list x \<equiv> case x of Cons h t \<Rightarrow> (h,t)"

sublocale subsumption_list \<subseteq> subsumption_impl r subsumes set sel_list append length 
proof(unfold_locales, rule finite_set)
  fix b a c
  assume "set b \<noteq> {}" and "sel_list b = (a,c)"
  thus "set b = insert a (set c) \<and> length c < length b" 
    by (cases b, auto)
qed auto

sublocale relation_subsumption_list \<subseteq> relation_subsumption_impl r subsumes set sel_list append length 
  by (unfold_locales, rule rtrancl_fin)

context relation_subsumption_list
begin

text \<open>The main equivalence proof between the generic work list algorithm
and the one operating on lists\<close>
lemma mk_rtrancl_list_main: "fin = set finl \<Longrightarrow> set (mk_rtrancl_list_main subsumes r todo finl) = mk_rtrancl_main todo fin"
proof (induct todo fin arbitrary: finl rule: mk_rtrancl_main.induct)
  case (1 todo fin finl)
  note simp = mk_rtrancl_list_main.simps[of _ _ todo finl] mk_rtrancl_main.simps[of todo fin] 
  show ?case (is "?l = ?r")
  proof (cases todo)
    case Nil
    show ?thesis unfolding simp unfolding Nil 1(3) by simp
  next
    case (Cons a tod)
    show ?thesis 
    proof (cases "\<exists> b \<in> fin. subsumes b a")
      case True
      from True have l: "?l = set (mk_rtrancl_list_main subsumes r tod finl)" 
        unfolding simp unfolding Cons 1(3) by simp
      from True have r: "?r = mk_rtrancl_main tod fin" 
        unfolding simp unfolding Cons by auto
      show ?thesis unfolding l r
        by (rule 1(1)[OF _ refl _ True], insert 1(3) Cons, auto)
    next
      case False
      from False have l: "?l = set (mk_rtrancl_list_main subsumes r (r a @ tod) (a # finl))" 
        unfolding simp unfolding Cons 1(3) by simp
      from False have r: "?r = mk_rtrancl_main (r a @ tod) (insert a fin)" 
        unfolding simp unfolding Cons by auto
      show ?thesis unfolding l r
        by (rule 1(2)[OF _ refl _ False], insert 1(3) Cons, auto)
    qed
  qed
qed

lemma mk_rtrancl_list: "set (mk_rtrancl_list subsumes r init) = mk_rtrancl init"
  unfolding mk_rtrancl_list_def mk_rtrancl_def
  by (rule mk_rtrancl_list_main, simp)
  
end



end
