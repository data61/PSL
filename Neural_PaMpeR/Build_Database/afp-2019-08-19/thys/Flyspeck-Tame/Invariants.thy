(*  Author:     Gertrud Bauer, Tobias Nipkow
*)

section\<open>Invariants of (Plane) Graphs\<close>

theory Invariants
imports FaceDivisionProps
begin

subsection\<open>Rotation of face into normal form\<close>

definition minVertex :: "face \<Rightarrow> vertex" where
"minVertex f \<equiv> min_list (vertices f)"

(* FIXME define normFace via rotate_min *)
definition normFace :: "face \<Rightarrow> vertex list" where
"normFace \<equiv> \<lambda>f. verticesFrom f (minVertex f)"

definition normFaces :: "face list \<Rightarrow> vertex list list" where
"normFaces fl \<equiv> map normFace fl"

lemma normFaces_distinct:  "distinct (normFaces fl) \<Longrightarrow> distinct fl"
apply (induct fl) by (auto simp: normFace_def normFaces_def)


(***********************************************************************)

subsection \<open>Minimal (plane) graph properties\<close>

definition minGraphProps' :: "graph \<Rightarrow> bool" where
  "minGraphProps' g \<equiv> \<forall>f \<in> \<F> g. 2 < |vertices f| \<and> distinct (vertices f)"

definition edges_sym :: "graph \<Rightarrow> bool" where
"edges_sym g \<equiv> \<forall> a b. (a,b) \<in> edges g \<longrightarrow> (b,a) \<in> edges g"

definition faceListAt_len :: "graph \<Rightarrow> bool" where
"faceListAt_len g \<equiv> (length (faceListAt g) = countVertices g)"

definition facesAt_eq :: "graph \<Rightarrow> bool" where
"facesAt_eq g \<equiv> \<forall>v \<in> \<V> g. set(facesAt g v) = {f. f \<in> \<F> g \<and> v \<in> \<V> f}"

definition facesAt_distinct :: "graph \<Rightarrow> bool" where
"facesAt_distinct g \<equiv> \<forall>v \<in> \<V> g. distinct (normFaces (facesAt g  v))"

definition faces_distinct :: "graph \<Rightarrow> bool" where
"faces_distinct g \<equiv> distinct (normFaces (faces g))"

definition faces_subset :: "graph \<Rightarrow> bool" where
"faces_subset g \<equiv> \<forall>f \<in> \<F> g. \<V> f \<subseteq> \<V> g"

definition edges_disj :: "graph \<Rightarrow> bool" where
"edges_disj g \<equiv>
 \<forall>f \<in> \<F> g. \<forall>f' \<in> \<F> g. f \<noteq> f' \<longrightarrow> \<E> f \<inter> \<E> f' = {}"

definition face_face_op :: "graph \<Rightarrow> bool" where
"face_face_op g \<equiv> |faces g| \<noteq> 2 \<longrightarrow>
 (\<forall>f\<in>\<F> g. \<forall>f'\<in>\<F> g. f \<noteq> f' \<longrightarrow> \<E> f \<noteq> (\<E> f')\<inverse>)"

definition one_final_but :: "graph \<Rightarrow> (vertex \<times> vertex)set \<Rightarrow> bool" where
"one_final_but g E \<equiv>
 \<forall>f \<in> \<F> g. \<not> final f \<longrightarrow>
   (\<forall>(a,b)\<in>\<E> f - E. (b,a) : E \<or> (\<exists>f'\<in>\<F> g. final f' \<and> (b,a) \<in> \<E> f'))"

definition one_final :: "graph \<Rightarrow> bool" where
"one_final g \<equiv> one_final_but g {}"


definition minGraphProps :: "graph \<Rightarrow> bool" where
"minGraphProps g \<equiv> minGraphProps' g \<and> facesAt_eq g \<and> faceListAt_len g \<and> facesAt_distinct g \<and> faces_distinct g \<and> faces_subset g \<and> edges_sym g \<and> edges_disj g \<and> face_face_op g"

definition inv :: "graph \<Rightarrow> bool" where
"inv g \<equiv> minGraphProps g \<and> one_final g \<and> |faces g| \<ge> 2"


lemma facesAt_distinctI:
  "(\<And>v. v \<in> \<V> g \<Longrightarrow> distinct (normFaces (facesAt g  v))) \<Longrightarrow> facesAt_distinct g"
 by (simp add: facesAt_distinct_def)

(* minGraphProps' *)
lemma minGraphProps2:
  "minGraphProps g \<Longrightarrow> f \<in> \<F> g \<Longrightarrow> 2 < |vertices f|"
by (unfold minGraphProps_def minGraphProps'_def) auto

lemma mgp_vertices3:
  "minGraphProps g \<Longrightarrow> f \<in> \<F> g \<Longrightarrow> |vertices f| \<ge> 3"
by(auto dest:minGraphProps2)

lemma mgp_vertices_nonempty:
  "minGraphProps g \<Longrightarrow> f \<in> \<F> g \<Longrightarrow> vertices f \<noteq> []"
by(auto dest:minGraphProps2)

lemma minGraphProps3:
  "minGraphProps g \<Longrightarrow> f \<in> \<F> g \<Longrightarrow>  distinct (vertices f)"
by (unfold minGraphProps_def minGraphProps'_def) auto

(* faceListAt_len *)
lemma minGraphProps4:
  "minGraphProps g \<Longrightarrow> (length (faceListAt g) = countVertices g)"
by (unfold minGraphProps_def faceListAt_len_def) simp

(* facesAt_eq*)
lemma minGraphProps5:
  "\<lbrakk>minGraphProps g; v : \<V> g; f \<in> set (facesAt g v)\<rbrakk> \<Longrightarrow> f \<in> \<F> g"
by(auto simp: facesAt_def facesAt_eq_def minGraphProps_def minGraphProps'_def
              faceListAt_len_def split:if_split_asm)

lemma minGraphProps6:
  "minGraphProps g \<Longrightarrow> v : \<V> g \<Longrightarrow> f \<in> set (facesAt g v) \<Longrightarrow> v \<in> \<V> f"
by(auto simp: facesAt_def facesAt_eq_def minGraphProps_def minGraphProps'_def
              faceListAt_len_def split:if_split_asm)

(* faces_subset *)
lemma minGraphProps9:
  "minGraphProps g \<Longrightarrow> f \<in> \<F> g \<Longrightarrow> v \<in> \<V> f \<Longrightarrow> v \<in> \<V> g"
by (unfold minGraphProps_def faces_subset_def) auto

lemma minGraphProps7:
  "minGraphProps g \<Longrightarrow> f \<in> \<F> g \<Longrightarrow> v \<in> \<V> f \<Longrightarrow>  f \<in> set (facesAt g v)"
apply(frule (2) minGraphProps9)
by (unfold minGraphProps_def facesAt_eq_def) simp

lemma minGraphProps_facesAt_eq: "minGraphProps g \<Longrightarrow>
  v \<in> \<V> g \<Longrightarrow> set (facesAt g v) = {f \<in> \<F> g. v \<in> \<V> f}"
by (simp add: minGraphProps_def facesAt_eq_def)

(* facesAt_distinct *)
lemma mgp_dist_facesAt[simp]:
  "minGraphProps g \<Longrightarrow> v : \<V> g \<Longrightarrow> distinct (facesAt g v)"
by(auto simp: facesAt_def minGraphProps_def minGraphProps'_def facesAt_distinct_def dest:normFaces_distinct)

lemma minGraphProps8:
  "minGraphProps g \<Longrightarrow> v : \<V> g \<Longrightarrow> distinct (normFaces (facesAt g v))"
by(auto simp: facesAt_def minGraphProps_def minGraphProps'_def facesAt_distinct_def normFaces_def)

lemma minGraphProps8a:
  "minGraphProps g \<Longrightarrow> v \<in> \<V> g \<Longrightarrow> distinct (normFaces (faceListAt g ! v))"
apply (frule (1) minGraphProps8[where v=v]) by (simp add: facesAt_def)

lemma minGraphProps8a': "minGraphProps g \<Longrightarrow>
  v < countVertices g \<Longrightarrow> distinct (normFaces (faceListAt g ! v))"
by (simp add: minGraphProps8a vertices_graph)

lemma minGraphProps9':
  "minGraphProps g \<Longrightarrow> f \<in> \<F> g \<Longrightarrow> v \<in> \<V> f \<Longrightarrow> v < countVertices g"
by (simp add: minGraphProps9 in_vertices_graph[symmetric])

lemma minGraphProps10:
  "minGraphProps g \<Longrightarrow> (a, b) \<in> edges g \<Longrightarrow> (b, a) \<in> edges g"
apply (unfold minGraphProps_def edges_sym_def)
apply (elim conjE allE impE)
by simp+

(* faces_distinct *)
lemma minGraphProps11:
  "minGraphProps g \<Longrightarrow> distinct (normFaces (faces g))"
by (unfold minGraphProps_def faces_distinct_def) simp

lemma minGraphProps11':
  "minGraphProps g \<Longrightarrow> distinct (faces g)"
by(simp add: minGraphProps11 normFaces_distinct)

lemma minGraphProps12:
  "minGraphProps g \<Longrightarrow> f \<in> \<F> g \<Longrightarrow> (a,b) \<in> \<E> f \<Longrightarrow> (b,a) \<notin> \<E> f"
apply (subgoal_tac "distinct (vertices f)") apply (simp add: is_nextElem_def)
 apply (case_tac "vertices f = []")
  apply (drule minGraphProps2)
   apply simp
  apply simp
 apply simp
 apply (case_tac "a = last (vertices f) \<and> b = hd (vertices f)")
  apply (case_tac "vertices f") apply simp
  apply (case_tac "list" rule: rev_exhaust)
   apply (drule minGraphProps2) apply simp
   apply simp
  apply (case_tac "ys")
   apply (drule minGraphProps2) apply simp apply simp
  apply (simp del: distinct_append distinct.simps)
  apply (rule conjI)
   apply (rule ccontr) apply (simp del: distinct_append distinct.simps)
   apply (drule is_sublist_distinct_prefix) apply simp
   apply (simp add: is_prefix_def)
  apply simp
 apply (rule conjI)
  apply (simp add: is_sublist_def) apply (elim exE) apply (intro allI) apply (rule ccontr)
  apply (simp del: distinct_append distinct.simps)
  apply (subgoal_tac "asa = as @ [a]") apply simp
  apply (rule dist_at1) apply assumption apply force apply (rule sym) apply simp
 apply (subgoal_tac "is_sublist [a, b] (vertices f)")
  apply (rule impI) apply (rule ccontr)
  apply (simp add: is_sublist_def del: distinct_append distinct.simps)
  apply (subgoal_tac "last (vertices f) = b \<and> hd (vertices f) = a")
   apply (thin_tac "a = hd (vertices f)") apply (thin_tac "b = last (vertices f)") apply (elim conjE)
   apply (elim exE)
   apply (case_tac "as")
    apply (case_tac "bs" rule: rev_exhaust) apply (drule minGraphProps2) apply simp apply simp
    apply simp+
apply (rule minGraphProps3) by simp+

lemma minGraphProps7': "minGraphProps g \<Longrightarrow>
  f \<in> \<F> g \<Longrightarrow> v \<in> \<V> f \<Longrightarrow>  f \<in> set (faceListAt g ! v)"
apply (frule minGraphProps7) apply assumption+
by (simp add: facesAt_def split: if_split_asm)

(* edges_disj *)
lemma mgp_edges_disj:
 "\<lbrakk> minGraphProps g; f \<noteq> f'; f \<in> \<F> g; f' \<in> \<F> g \<rbrakk> \<Longrightarrow>
  uv \<in> \<E> f \<Longrightarrow> uv \<notin> \<E> f'"
by (simp add:minGraphProps_def edges_disj_def) blast

(* one_final *)
lemma one_final_but_antimono:
  "one_final_but g E \<Longrightarrow> E \<subseteq> E' \<Longrightarrow> one_final_but g E'"
apply(unfold one_final_but_def)
apply blast
done

lemma one_final_antimono: "one_final g \<Longrightarrow> one_final_but g E"
apply(unfold one_final_def one_final_but_def)
apply blast
done

lemma inv_two_faces: "inv g \<Longrightarrow> |faces g| \<ge> 2"
by(simp add:inv_def)

lemma inv_mgp[simp]: "inv g \<Longrightarrow> minGraphProps g"
by(simp add:inv_def)

lemma makeFaceFinal_id[simp]: "final f \<Longrightarrow> makeFaceFinal f g = g"
apply(cases g)
apply (simp add:makeFaceFinal_def makeFaceFinalFaceList_def
                setFinal_eq_iff[THEN iffD2])
done

lemma inv_one_finalD':
 "\<lbrakk> inv g; f \<in> \<F> g; \<not> final f; (a,b) \<in> \<E> f \<rbrakk> \<Longrightarrow>
  \<exists>f' \<in> \<F> g. final f' \<and> f' \<noteq> f \<and> (b,a) \<in> \<E> f'"
apply(unfold inv_def one_final_def one_final_but_def)
apply blast
done

lemmas minGraphProps =
  minGraphProps2 minGraphProps3 minGraphProps4
  minGraphProps5 minGraphProps6 minGraphProps7 minGraphProps8
  minGraphProps9

lemma mgp_no_loop[simp]:
  "minGraphProps g \<Longrightarrow> f \<in> \<F> g \<Longrightarrow> v \<in> \<V> f \<Longrightarrow> f \<bullet> v \<noteq> v"
apply(frule (1) mgp_vertices3)
apply(frule (1) minGraphProps3)
apply(simp add: distinct_no_loop1)
done

lemma mgp_facesAt_no_loop:
  "minGraphProps g \<Longrightarrow> v : \<V> g \<Longrightarrow> f \<in> set (facesAt g v) \<Longrightarrow> f \<bullet> v \<noteq> v"
by(blast dest:mgp_no_loop minGraphProps5 minGraphProps6)

lemma edge_pres_faceAt:
 "\<lbrakk> minGraphProps g; u : \<V> g; f \<in> set(facesAt g u); (u,v) \<in> \<E> f \<rbrakk> \<Longrightarrow>
  f \<in> set(facesAt g v)"
apply(auto simp:edges_face_eq)
apply(rule minGraphProps7, assumption)
 apply(blast intro:minGraphProps)
apply(simp)
done

lemma in_facesAt_nextVertex:
 "minGraphProps g \<Longrightarrow> v : \<V> g \<Longrightarrow> f \<in> set(facesAt g v) \<Longrightarrow> f \<in> set(facesAt g (f \<bullet> v))"
apply(subgoal_tac "(v,f \<bullet> v) \<in> \<E> f")
 apply(blast intro:edge_pres_faceAt)
by(blast intro: nextVertex_in_edges minGraphProps)


lemma mgp_edge_face_ex:
assumes [intro]: "minGraphProps g" "v : \<V> g"
and fv: "f \<in> set(facesAt g v)" and uv: "(u,v) \<in> \<E> f"
shows "\<exists>f' \<in> set(facesAt g v). (v,u) \<in> \<E> f'"
proof -
  from fv have "f \<in> \<F> g" by(blast intro:minGraphProps)
  with uv have "(u,v) \<in> \<E> g" by(auto simp:edges_graph_def)
  hence "(v,u) \<in> \<E> g" by(blast intro:minGraphProps10)
  then obtain f' where f': "f' \<in> \<F> g" and vu: "(v,u) \<in> \<E> f'"
    by(auto simp:edges_graph_def)
  from vu have "v \<in> \<V> f'" by(auto simp:edges_face_eq)
  with f' have "f' \<in> set(facesAt g v)" by(blast intro:minGraphProps)
  with vu show ?thesis by blast
qed

lemma nextVertex_in_graph:
  "minGraphProps g \<Longrightarrow> v : \<V> g \<Longrightarrow> f \<in> set(facesAt g v) \<Longrightarrow> f \<bullet> v : \<V> g"
by(blast intro: minGraphProps9 minGraphProps5 minGraphProps6 nextVertex_in_face)

lemma mgp_nextVertex_face_ex2:
assumes mgp[intro]: "minGraphProps g" "v : \<V> g" and f: "f \<in> set(facesAt g v)"
shows "\<exists>f' \<in> set(facesAt g (f \<bullet> v)). f' \<bullet> (f \<bullet> v) = v"
proof -
  from f have "(v,f \<bullet> v) \<in> \<E> f"
    by(blast intro: nextVertex_in_edges minGraphProps)
  with in_facesAt_nextVertex[OF mgp f]
    mgp_edge_face_ex[OF mgp(1) nextVertex_in_graph[OF mgp f]]
  obtain f' :: face where "f' \<in> set(facesAt g (f \<bullet> v))"
    and "(f \<bullet> v,v) \<in> \<E> f'"
    by(blast)
  thus ?thesis by (auto simp: edges_face_eq)
qed


lemma inv_finals_nonempty: "inv g \<Longrightarrow> finals g \<noteq> []"
apply(frule inv_two_faces)
apply(clarsimp simp:filter_empty_conv finals_def)
apply(subgoal_tac "faces g \<noteq> []")
 prefer 2 apply clarsimp
apply(simp add:neq_Nil_conv)
apply clarify
apply(rename_tac f fs)
apply(case_tac "final f")
 apply simp
apply(frule mgp_vertices_nonempty[OF inv_mgp])
 apply fastforce
apply(clarsimp simp:neq_Nil_conv)
apply(rename_tac v vs)
apply(subgoal_tac "v \<in> \<V> f")
 prefer 2 apply simp
apply(drule nextVertex_in_edges)
apply(drule inv_one_finalD')
   prefer 2 apply assumption
  apply simp
 apply assumption
apply(auto)
done


subsection \<open>@{const containsDuplicateEdge}\<close>

definition
 containsUnacceptableEdgeSnd' :: "(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> bool" where
"containsUnacceptableEdgeSnd' N is \<equiv>
 (\<exists>k < |is| - 2. let i0 = is!k; i1 = is!(k+1); i2 = is!(k+2) in
 N i1 i2 \<and> (i0 < i1) \<and> (i1 < i2))"

lemma containsUnacceptableEdgeSnd_eq:
  "containsUnacceptableEdgeSnd N v is = containsUnacceptableEdgeSnd' N (v#is)"
proof (induct "is" arbitrary: v)
  case Nil then show ?case by (simp add: containsUnacceptableEdgeSnd'_def)
next
  case (Cons i "is") then show ?case
    proof (rule_tac iffI)
      assume vors: "containsUnacceptableEdgeSnd N v (i # is)"
      then show "containsUnacceptableEdgeSnd' N (v # i # is)"
        apply (cases "is") apply simp apply simp
        apply (simp split: if_split_asm del: containsUnacceptableEdgeSnd.simps)
         apply (simp add: containsUnacceptableEdgeSnd'_def) apply force
        apply (subgoal_tac "a # list = is") apply (thin_tac "is = a # list") apply (simp add: Cons)
         apply (simp add: containsUnacceptableEdgeSnd'_def) apply (elim exE)
         apply (rule exI) apply (subgoal_tac "Suc k < |is|") apply (rule conjI) apply assumption by auto
    next
      assume vors: "containsUnacceptableEdgeSnd' N (v # i # is)"
      then show "containsUnacceptableEdgeSnd N v (i # is)"
        apply simp apply (cases "is") apply (simp add: containsUnacceptableEdgeSnd'_def)
        apply (simp del:  containsUnacceptableEdgeSnd.simps)
        apply (subgoal_tac "a # list = is") apply (thin_tac "is = a # list")
         apply (simp add: Cons)
         apply (subgoal_tac "is = a # list") apply (thin_tac "a # list = is")
          apply (simp add: containsUnacceptableEdgeSnd'_def)
          apply (elim exE) apply (case_tac "k") apply simp apply simp apply (intro impI exI)
          apply (rule conjI) apply (elim conjE) apply assumption by auto
    qed
qed

lemma containsDuplicateEdge_eq1:
  "containsDuplicateEdge g f v is = containsDuplicateEdge' g f v is"
apply (simp add: containsDuplicateEdge_def)
apply (cases "is") apply (simp add: containsDuplicateEdge'_def)
apply simp
apply (case_tac "list") apply (simp add: containsDuplicateEdge'_def)
apply (simp add: containsUnacceptableEdgeSnd_eq del: containsUnacceptableEdgeSnd.simps)
apply (rule conjI) apply (simp add: containsDuplicateEdge'_def)
apply (rule impI)
apply (case_tac "a < aa")
 by (simp_all add: containsDuplicateEdge'_def containsUnacceptableEdgeSnd'_def)

lemma containsDuplicateEdge_eq:
  "containsDuplicateEdge = containsDuplicateEdge'"
apply (rule ext)+
by (simp add: containsDuplicateEdge_eq1)


declare Nat.diff_is_0_eq' [simp del]


(********************************* replaceFacesAt ****************************)
subsection\<open>@{const replacefacesAt}\<close>

primrec replacefacesAt2 ::
  "nat list \<Rightarrow> face \<Rightarrow> face list \<Rightarrow> face list list \<Rightarrow> face list list" where
"replacefacesAt2 [] f fs F = F" |
"replacefacesAt2 (n#ns) f fs F =
 (if n < |F|
  then replacefacesAt2 ns f fs (F [n:=replace f fs (F!n)])
  else replacefacesAt2 ns f fs F)"


lemma replacefacesAt_eq[THEN eq_reflection]:
  "replacefacesAt ns oldf newfs F =  replacefacesAt2 ns oldf newfs F"
by (induct ns arbitrary: F) (auto simp add: replacefacesAt_def)


lemma replacefacesAt2_notin:
  "i \<notin> set is \<Longrightarrow> (replacefacesAt2 is olfF newFs Fss)!i = Fss!i"
proof (induct "is" arbitrary: Fss)
  case Nil then show ?case by (simp)
next
  case (Cons j js) then show ?case
    by (cases "j < |Fss|") (auto)
qed


lemma replacefacesAt2_in:
  "i \<in> set is \<Longrightarrow> distinct is \<Longrightarrow> i < |Fss| \<Longrightarrow>
  (replacefacesAt2 is olfF newFs Fss)!i = replace olfF newFs (Fss !i)"
proof (induct "is" arbitrary: Fss)
  case Nil then show ?case by simp
next
  case (Cons j js)
  then have "j = i \<and> i \<notin> set js \<or> i \<noteq> j \<and> i \<in> set js" by auto
  then show ?case
  proof (elim disjE conjE)
    assume "j = i" "i \<notin> set js" with Cons show ?thesis
    by (auto simp add: replacefacesAt2_notin)
  next
    assume "i \<in> set js" "i \<noteq> j" with Cons show ?thesis by simp
  qed
qed


lemma distinct_replacefacesAt21:
  "i < |Fss| \<Longrightarrow> i \<in> set is \<Longrightarrow> distinct is \<Longrightarrow> distinct (Fss!i) \<Longrightarrow> distinct newFs \<Longrightarrow>
  set (Fss ! i) \<inter> set newFs \<subseteq> {olfF} \<Longrightarrow>
  distinct ((replacefacesAt2 is olfF newFs Fss)! i)"
proof (induct "is")
  case Nil then show ?case by simp
next
  case (Cons j js)
  then have "j = i \<and> i \<notin> set js \<or> i \<noteq> j \<and> i \<in> set js" by auto
  then show ?case
  proof (elim disjE conjE)
    assume "j = i" "i \<notin> set js" with Cons show ?thesis
     by (simp add: replacefacesAt2_notin distinct_replace)
  next
    assume "i \<in> set js" "i \<noteq> j" with Cons show ?thesis
     by (simp add: replacefacesAt2_in distinct_replace)
  qed
qed

lemma distinct_replacefacesAt22:
  "i < |Fss| \<Longrightarrow> i \<notin> set is \<Longrightarrow> distinct is \<Longrightarrow> distinct (Fss!i) \<Longrightarrow> distinct newFs \<Longrightarrow>
  set (Fss ! i) \<inter> set newFs \<subseteq> {olfF} \<Longrightarrow>
  distinct ((replacefacesAt2 is olfF newFs Fss)! i)"
proof (induct "is")
  case Nil then show ?case by simp
next
  case (Cons j js)
  then have "i \<noteq> j" by auto
  with Cons show ?case
    by (simp add: replacefacesAt2_notin distinct_replace)
qed

lemma distinct_replacefacesAt2_2:
  "i < |Fss| \<Longrightarrow> distinct is \<Longrightarrow> distinct (Fss!i) \<Longrightarrow> distinct newFs \<Longrightarrow>
  set (Fss ! i) \<inter> set newFs \<subseteq> {olfF} \<Longrightarrow>
  distinct ((replacefacesAt2 is olfF newFs Fss)! i)"
by (cases "i \<in> set is")
   (auto intro: distinct_replacefacesAt21 distinct_replacefacesAt22)

lemma replacefacesAt2_nth1:
  "k \<notin> set ns \<Longrightarrow> (replacefacesAt2 ns oldf newfs F) ! k  =  F ! k"
by (induct ns arbitrary: F) auto

lemma  replacefacesAt2_nth1': "k \<in> set ns \<Longrightarrow> k < |F| \<Longrightarrow> distinct ns \<Longrightarrow>
  (replacefacesAt2 ns oldf newfs F) ! k  =  (replace oldf newfs (F!k))"
apply (induct ns arbitrary: F)
 apply auto
 apply (simp add: replacefacesAt2_nth1)+
by (case_tac "a = k") auto


lemma replacefacesAt2_nth2: "k < |F| \<Longrightarrow>
  (replacefacesAt2 [k] oldf newfs F) ! k = replace oldf newfs (F!k)"
by (auto)

lemma replacefacesAt2_length[simp]:
  "|replacefacesAt2 nvs f' f'' vs| = |vs|"
by (induct nvs arbitrary: vs) simp_all

lemma replacefacesAt2_nth: "k \<in>  set ns \<Longrightarrow> k < |F| \<Longrightarrow> oldf \<notin> set newfs  \<Longrightarrow>
  distinct (F!k) \<Longrightarrow> distinct newfs \<Longrightarrow> oldf \<in> set (F!k) \<longrightarrow> set newfs \<inter> set (F!k) \<subseteq> {oldf} \<Longrightarrow>
  (replacefacesAt2 ns oldf newfs F) ! k  =  (replace  oldf newfs (F!k))"
proof (induct ns arbitrary: F)
  case Nil then show ?case by simp
next
  case (Cons n ns) then show ?case
    apply (simp only: replacefacesAt2.simps)
    apply simp apply (case_tac "n = k")
     apply (simp)
     apply (subgoal_tac "replacefacesAt2 ns oldf newfs (F[k := replace  oldf newfs (F ! k)])  ! k =
    replace oldf newfs ((F[k := replace oldf newfs (F ! k)]) ! k)")
      apply simp
     apply (case_tac "k \<in> set ns")  apply (rule Cons) apply simp+
        apply (rule replace_distinct) apply simp  apply simp
        apply simp
       apply simp
      apply (simp add:distinct_set_replace)
     apply (simp add:  replacefacesAt2_nth1)
    by simp
qed


lemma replacefacesAt_notin:
  "i \<notin> set is \<Longrightarrow> (replacefacesAt is olfF newFs Fss)!i = Fss!i"
by (simp add: replacefacesAt_eq replacefacesAt2_notin)

lemma replacefacesAt_in:
  "i \<in> set is \<Longrightarrow> distinct is \<Longrightarrow> i < |Fss| \<Longrightarrow>
  (replacefacesAt is olfF newFs Fss)!i = replace olfF newFs (Fss !i)"
by (simp add: replacefacesAt_eq replacefacesAt2_in)

lemma replacefacesAt_length[simp]: "|replacefacesAt nvs f' [f''] vs| = |vs|"
by (simp add: replacefacesAt_eq)

lemma replacefacesAt_nth2: "k < |F| \<Longrightarrow>
  (replacefacesAt [k] oldf newfs F) ! k = replace oldf newfs (F!k)"
by (simp add: replacefacesAt_eq replacefacesAt2_nth2)

lemma replacefacesAt_nth: "k \<in>  set ns \<Longrightarrow> k < |F| \<Longrightarrow> oldf \<notin> set newfs  \<Longrightarrow>
  distinct (F!k) \<Longrightarrow> distinct newfs \<Longrightarrow> oldf \<in> set (F!k) \<longrightarrow> set newfs \<inter> set (F!k) \<subseteq> {oldf} \<Longrightarrow>
  (replacefacesAt ns oldf newfs F) ! k  =  (replace  oldf newfs (F!k))"
by (simp add: replacefacesAt_eq replacefacesAt2_nth)

lemma replacefacesAt2_5: "x \<in> set (replacefacesAt2 ns oldf newfs F ! k) \<Longrightarrow> x \<in> set (F!k) \<or> x \<in> set newfs"
proof (induct ns arbitrary: F)
  case Nil then show ?case by simp
next
  case (Cons n ns)
  then show ?case
    apply(simp add: split: if_split_asm ) apply (frule Cons)
    apply (thin_tac "\<And>F. x \<in> set (replacefacesAt2 ns oldf newfs F ! k) \<Longrightarrow> x \<in> set (F ! k) \<or> x \<in> set newfs")
    apply (case_tac "x \<in> set newfs")  apply simp apply simp
    apply (case_tac "k = n") apply simp apply (frule replace5) apply simp by simp
qed


lemma replacefacesAt_Nil[simp]: "replacefacesAt [] f fs F = F"
by (simp add: replacefacesAt_eq)

lemma replacefacesAt_Cons[simp]:
 "replacefacesAt (n # ns) f fs F =
  (if n < |F| then replacefacesAt ns f fs (F[n := replace f fs (F!n)])
   else replacefacesAt ns f fs F)"
by (simp add: replacefacesAt_eq)

lemmas replacefacesAt_simps = replacefacesAt_Nil replacefacesAt_Cons

lemma len_nth_repAt[simp]:
"\<And>xs. i < |xs| \<Longrightarrow> |replacefacesAt is x [y] xs ! i| = |xs!i|"
by (induct "is") (simp_all add: add:nth_list_update)


subsection\<open>@{const normFace}\<close>

(************************** min_list & minVertex **********************)

lemma minVertex_in: "vertices f \<noteq> [] \<Longrightarrow> minVertex f \<in> \<V> f"
by (simp add: minVertex_def)


lemma minVertex_eq_if_vertices_eq:
 "\<V> f = \<V> f' \<Longrightarrow> minVertex f = minVertex f'"
apply(cases f)
apply(cases f')
apply(rename_tac vs ft vs' ft')
apply(case_tac "vs = []")
 apply(simp add:vertices_face_def minVertex_def)
apply(subgoal_tac "vs' \<noteq> []")
 prefer 2 apply clarsimp
apply(simp add:vertices_face_def minVertex_def min_list_conv_Min
               insert_absorb del:Min_insert)
done


(************** normFace ***************************)


lemma normFace_replace_in:
 "normFace a \<in> set (normFaces (replace oldF newFs fs)) \<Longrightarrow>
  normFace a \<in> set (normFaces newFs) \<or> normFace a \<in> set (normFaces fs)"
apply (induct fs) apply simp
apply (auto simp add: normFaces_def split:if_split_asm)
done

lemma distinct_replace_norm:
  "distinct (normFaces fs) \<Longrightarrow>  distinct (normFaces newFs) \<Longrightarrow>
   set (normFaces fs) \<inter> set (normFaces newFs) \<subseteq> {} \<Longrightarrow> distinct (normFaces (replace oldF newFs fs))"
apply (induct fs) apply simp
apply simp
apply (case_tac "a = oldF") apply (simp add: normFaces_def) apply blast
apply (simp add: normFaces_def) apply (rule ccontr)
apply (subgoal_tac "normFace a \<in> set(normFaces (replace oldF newFs fs))")
apply (frule normFace_replace_in)
 by (simp add: normFaces_def)+


lemma distinct_replacefacesAt1_norm:
  "i < |Fss| \<Longrightarrow> i \<in> set is \<Longrightarrow> distinct is \<Longrightarrow> distinct (normFaces (Fss!i)) \<Longrightarrow> distinct (normFaces newFs) \<Longrightarrow>
  set (normFaces (Fss ! i)) \<inter> set (normFaces newFs) \<subseteq> {} \<Longrightarrow>
  distinct (normFaces ((replacefacesAt is oldF newFs Fss)! i))"
proof (induct "is")
  case Nil then show ?case by simp
next
  case (Cons j js)
  then have "j = i \<and> i \<notin> set js \<or> i \<noteq> j \<and> i \<in> set js" by auto
  then show ?case
  proof (elim disjE conjE)
    assume "j = i" "i \<notin> set js" with Cons show ?thesis
     by (simp add: replacefacesAt_notin distinct_replace_norm)
  next
    assume "i \<in> set js" "i \<noteq> j" with Cons show ?thesis
     by (simp add: replacefacesAt_in distinct_replace_norm)
  qed
qed

lemma distinct_replacefacesAt2_norm:
  "i < |Fss| \<Longrightarrow> i \<notin> set is \<Longrightarrow> distinct is \<Longrightarrow> distinct (normFaces (Fss!i)) \<Longrightarrow> distinct (normFaces newFs) \<Longrightarrow>
  set (normFaces (Fss ! i)) \<inter> set (normFaces newFs) \<subseteq> {} \<Longrightarrow>
  distinct (normFaces ((replacefacesAt is oldF newFs Fss)! i))"
proof (induct "is")
  case Nil then show ?case by simp
next
  case (Cons j js)
  then have "i \<noteq> j" by auto
  with Cons show ?case
    by (simp add: replacefacesAt_notin distinct_replace_norm)
qed

lemma distinct_replacefacesAt_norm:
  "i < |Fss| \<Longrightarrow> distinct is \<Longrightarrow> distinct (normFaces (Fss!i)) \<Longrightarrow> distinct (normFaces newFs) \<Longrightarrow>
  set (normFaces (Fss ! i)) \<inter> set (normFaces newFs) \<subseteq> {} \<Longrightarrow>
  distinct (normFaces ((replacefacesAt is olfF newFs Fss)! i))"
by (cases "i \<in> set is")
   (auto intro: distinct_replacefacesAt1_norm distinct_replacefacesAt2_norm)


lemma normFace_in_cong:
 "vertices f \<noteq> [] \<Longrightarrow> minGraphProps g \<Longrightarrow> normFace f \<in> set (normFaces (faces g))
  \<Longrightarrow> \<exists> f' \<in> set (faces g). f \<cong> f'"
apply (simp add: normFace_def normFaces_def)
apply (erule imageE)
apply(rename_tac f')
apply (rule bexI)
 defer apply assumption
apply (simp add: cong_face_def)
 apply (rule congs_trans) apply (rule verticesFrom_congs)
 apply (rule minVertex_in) apply simp
apply (rule congs_sym) apply (simp add: normFace_def)
apply (rule verticesFrom_congs) apply (rule minVertex_in)
apply (subgoal_tac "2 < | vertices f'|") apply force
by (simp add: minGraphProps2)

lemma normFace_neq:
  "a \<in> \<V> f \<Longrightarrow> a \<notin> \<V> f' \<Longrightarrow> vertices f' \<noteq> [] \<Longrightarrow> normFace f \<noteq> normFace f'"
apply (simp add: normFace_def)
apply (subgoal_tac "a \<in> set (verticesFrom f (minVertex f))")
 apply (subgoal_tac "a \<notin> set (verticesFrom f' (minVertex f'))") apply force
 apply (subgoal_tac "(vertices f') \<cong> (verticesFrom f' (minVertex f'))") apply (simp add: congs_pres_nodes)
 apply (rule verticesFrom_congs) apply (rule minVertex_in) apply simp
apply (subgoal_tac "(vertices f) \<cong> (verticesFrom f (minVertex f))") apply (simp add: congs_pres_nodes)
apply (rule verticesFrom_congs) apply (rule minVertex_in) by auto

lemma split_face_f12_f21_neq_norm:
  "pre_split_face oldF ram1 ram2 vs \<Longrightarrow>
  2 < |vertices oldF| \<Longrightarrow> 2 < |vertices f12| \<Longrightarrow> 2 < |vertices f21| \<Longrightarrow>
  (f12, f21) = split_face oldF ram1 ram2 vs \<Longrightarrow> normFace f12 \<noteq> normFace f21"
proof -
  assume split: "(f12, f21) = split_face oldF ram1 ram2 vs"
  "pre_split_face oldF ram1 ram2 vs"
    and minlen: "2 < |vertices oldF|"  "2 < | vertices f12|"  "2 < | vertices f21|"
  from split have dist_f12: "distinct (vertices f12)" by (rule split_face_distinct1)
  from split have dist_f21: "distinct (vertices f21)" by (rule split_face_distinct2)

  from split dist_f12 dist_f21 minlen show ?thesis
    apply (simp add: split_face_def)
    apply (case_tac "between (vertices oldF) ram2 ram1")
     apply (case_tac "between (vertices oldF) ram1 ram2")
      apply simp apply (subgoal_tac "|vertices oldF| = 2")
       apply simp apply (frule verticesFrom_ram1)
      apply (subgoal_tac "distinct (vertices oldF)") apply (drule verticesFrom_length)
        apply (subgoal_tac "ram1 \<in> \<V> oldF") apply assumption apply (simp add: pre_split_face_def) apply simp
       apply (simp add: pre_split_face_def)
      apply (rule normFace_neq)
        apply (subgoal_tac "a \<in> \<V> (Face (rev vs @ ram1 # between (vertices oldF) ram1 ram2 @ [ram2]) Nonfinal)")
         apply assumption apply simp apply force  apply simp
    apply (rule not_sym)
    apply (rule normFace_neq)
      apply (subgoal_tac "a \<in> \<V> (Face (ram2 # between (vertices oldF) ram2 ram1 @ ram1 # vs) Nonfinal)")
       apply assumption apply simp
     apply (frule verticesFrom_ram1)
     apply (subgoal_tac "distinct (verticesFrom oldF ram1)") apply clarsimp
     apply (rule verticesFrom_distinct)
      by (simp add: pre_split_face_def)+
qed


lemma normFace_in: "f \<in> set fs \<Longrightarrow> normFace f \<in> set (normFaces fs)"
by (simp add: normFaces_def)



subsection\<open>Invariants of @{const splitFace}\<close>
(********************************** splitFace & minGraphProps *************************************)

lemma splitFace_holds_minGraphProps':
  "pre_splitFace g' v a f' vs \<Longrightarrow> minGraphProps' g' \<Longrightarrow>
  minGraphProps' (snd (snd (splitFace g' v a f' vs)))"
apply (simp add: minGraphProps'_def)
apply safe
 apply (simp add: splitFace_def split_def)
 apply (case_tac "f \<in> \<F> g'") apply simp
 apply safe
  apply (simp add: split_face_def) apply safe apply simp apply (drule pre_FaceDiv_between1) apply simp
 apply (frule_tac replace1)
  apply simp_all
 apply (simp add: split_face_def) apply safe apply simp
 apply (drule pre_FaceDiv_between2) apply simp
apply (drule splitFace_split)
apply safe
  apply simp
 apply (subgoal_tac "pre_splitFace g' v a f' vs")
  apply (drule splitFace_distinct2)+ apply simp+
apply (subgoal_tac "pre_splitFace g' v a f' vs")
 apply (drule splitFace_distinct1)+
 by simp+


lemma splitFace_holds_faceListAt_len:
  "pre_splitFace g' v a f' vs \<Longrightarrow> minGraphProps g' \<Longrightarrow>
   faceListAt_len (snd (snd (splitFace g' v a f' vs)))"
by (simp add: minGraphProps_def faceListAt_len_def splitFace_def split_def)


lemma splitFace_new_f12:
assumes pre: "pre_splitFace g ram1 ram2 oldF newVs"
    and props: "minGraphProps g"
    and spl: "(f12, f21, newGraph) = splitFace g ram1 ram2 oldF newVs"
shows "f12 \<notin> \<F> g"
proof (cases newVs)
  case Nil with pre have "(ram2, ram1) \<notin> edges g"
    by (unfold pre_splitFace_def) auto
  moreover from Nil pre
  have "(ram2, ram1) \<in> edges f12"
    apply (rule_tac splitFace_empty_ram2_ram1_in_f12)
     apply (auto simp: Nil[symmetric])
    apply (rule spl)
    done
  ultimately show ?thesis by (auto simp add: edges_graph_def)
next
  case (Cons v vs)
  with pre have "v \<notin> \<V> g"
    by (auto simp: pre_splitFace_def)
  moreover from Cons spl have "v \<in> \<V> f12"
    by (simp add: splitFace_f12_new_vertices)
  moreover note props
  ultimately show ?thesis by (auto dest: minGraphProps)
qed

lemma splitFace_new_f12_norm:
assumes pre: "pre_splitFace g ram1 ram2 oldF newVs"
and props: "minGraphProps g"
and spl: "(f12, f21, newGraph) = splitFace g ram1 ram2 oldF newVs"
shows "normFace f12 \<notin> set (normFaces (faces g))"
proof (cases newVs)
  case Nil with pre have "(ram2, ram1) \<notin> edges g"
    by (auto simp: pre_splitFace_def)
  moreover
  from pre spl [symmetric] have dist_f12: "distinct (vertices f12)"
    apply (drule_tac splitFace_distinct2) by simp                  
  moreover
  from Nil pre
  have "(ram2, ram1) \<in> edges f12"
    apply (rule_tac splitFace_empty_ram2_ram1_in_f12)
     apply (auto simp: Nil[symmetric])
    apply (rule spl)
    done
  moreover
  with dist_f12 have "vertices f12 \<noteq> []"
    apply (simp add: is_nextElem_def) apply (case_tac "vertices f12") apply (simp add: is_sublist_def)
    by simp
  ultimately show ?thesis
    apply (auto simp add: edges_graph_def) apply (frule normFace_in_cong)
      apply (rule props)
     apply assumption
    apply (elim bexE)
    apply (subgoal_tac "(ram2, ram1) \<in> edges f'") apply simp
    apply (subgoal_tac "(vertices f12) \<cong> (vertices f')")  apply (frule congs_distinct)
     apply (simp add: cong_face_def is_nextElem_congs_eq)+
    done
next
  case (Cons v vs)
  with pre have "v \<notin> \<V> g" by (auto simp: pre_splitFace_def)
  moreover from Cons spl have "v \<in> \<V> f12"
    by (simp add: splitFace_f12_new_vertices)
  moreover note props
  ultimately show ?thesis
    apply auto
    apply (subgoal_tac "(vertices f12) \<noteq> []")
     apply (frule normFace_in_cong) apply assumption+ apply (erule bexE)
     apply (subgoal_tac "v \<in> \<V> f'") apply (simp add: minGraphProps9)
     apply (simp add: congs_pres_nodes cong_face_def) by auto
qed

lemma splitFace_new_f21:
assumes pre: "pre_splitFace g ram1 ram2 oldF newVs"
and props: "minGraphProps g"
and spl: "(f12, f21, newGraph) = splitFace g ram1 ram2 oldF newVs"
shows "f21 \<notin> \<F> g"
proof (cases newVs)
  case Nil with pre have "(ram1, ram2) \<notin> edges g"
    by (auto simp: pre_splitFace_def)
  moreover from Nil pre
  have "(ram1, ram2) \<in> edges f21"
    apply (rule_tac splitFace_empty_ram1_ram2_in_f21)
     apply (auto simp: Nil[symmetric])
    apply (rule spl)
    done
  ultimately show ?thesis by (auto simp add: edges_graph_def)
next
  case (Cons v vs)
  with pre have "v \<notin> \<V> g" by (auto simp: pre_splitFace_def)
  moreover from Cons spl have "v \<in> \<V> f21"
    by (simp add: splitFace_f21_new_vertices)
  moreover note props
  ultimately show ?thesis by (auto dest: minGraphProps)
qed

lemma splitFace_new_f21_norm:
assumes pre: "pre_splitFace g ram1 ram2 oldF newVs"
and props: "minGraphProps g"
and spl: "(f12, f21, newGraph) = splitFace g ram1 ram2 oldF newVs"
shows "normFace f21 \<notin> set (normFaces (faces g))"
proof (cases newVs)
  case Nil with pre have "(ram1, ram2) \<notin> edges g"
    by (auto simp: pre_splitFace_def)
  moreover
  from pre spl [symmetric] have dist_f21: "distinct (vertices f21)"
    apply (drule_tac splitFace_distinct1) by simp
  moreover
  from Nil pre
  have "(ram1, ram2) \<in> edges f21"
    apply (rule_tac splitFace_empty_ram1_ram2_in_f21)
     apply (auto simp: Nil[symmetric])
    apply (rule spl)
    done
  moreover
  with dist_f21 have "vertices f21 \<noteq> []"
    apply (simp add: is_nextElem_def) apply (case_tac "vertices f21") apply (simp add: is_sublist_def)
    by simp
  ultimately show ?thesis apply (auto simp add: edges_graph_def) apply (frule normFace_in_cong)
      apply (rule props)
     apply assumption
    apply (elim bexE)
    apply (subgoal_tac "(ram1, ram2) \<in> edges f'") apply simp
    apply (subgoal_tac "(vertices f21) \<cong> (vertices f')")  apply (frule congs_distinct)
     apply (simp add: cong_face_def is_nextElem_congs_eq)+
    done
next
  case (Cons v vs)
  with pre have "v \<notin> \<V> g" by (auto simp: pre_splitFace_def)
  moreover from Cons spl have "v \<in> \<V> f21"
    by (simp add: splitFace_f21_new_vertices)
  moreover note props
  ultimately show ?thesis apply auto
    apply (subgoal_tac "(vertices f21) \<noteq> []")
     apply (frule normFace_in_cong) apply assumption+ apply (erule bexE)
     apply (subgoal_tac "v \<in> \<V> f'") apply (simp add: minGraphProps9)
     apply (simp add: congs_pres_nodes cong_face_def) by auto
qed

lemma splitFace_f21_oldF_neq:
 "pre_splitFace g ram1 ram2 oldF newVs \<Longrightarrow>
  minGraphProps g \<Longrightarrow>
 (f12, f21, newGraph) = splitFace g ram1 ram2 oldF newVs \<Longrightarrow>
  oldF \<noteq> f21"
by (frule splitFace_new_f21) (auto)

lemma splitFace_f12_oldF_neq:
 "pre_splitFace g ram1 ram2 oldF newVs \<Longrightarrow>
  minGraphProps g \<Longrightarrow>
 (f12, f21, newGraph) = splitFace g ram1 ram2 oldF newVs \<Longrightarrow>
  oldF \<noteq> f12"
by (frule splitFace_new_f12) (auto)


lemma splitFace_f12_f21_neq_norm:
 "pre_splitFace g ram1 ram2 oldF vs \<Longrightarrow> minGraphProps g \<Longrightarrow>
 (f12, f21, newGraph) = splitFace g ram1 ram2 oldF vs \<Longrightarrow>
  normFace f12 \<noteq> normFace f21"
apply (subgoal_tac "minGraphProps' newGraph")
 apply (subgoal_tac "f12 \<in> \<F> newGraph \<and> f21 \<in> \<F> newGraph")
  apply (subgoal_tac "pre_split_face oldF ram1 ram2 vs")
   apply (frule split_face_f12_f21_neq_norm) apply (rule minGraphProps2) apply simp apply(erule pre_splitFace_oldF)
      apply (subgoal_tac "2 < | vertices f12 |") apply assumption apply (force simp: minGraphProps'_def)
     apply (subgoal_tac "2 < | vertices f21 |") apply assumption apply (force simp: minGraphProps'_def)
    apply (simp add: splitFace_def split_def)
   apply simp
  apply force
 apply (simp add: splitFace_def split_def)
 apply (rule disjI2)
 apply (erule replace3[OF pre_splitFace_oldF])
 apply simp
apply (frule splitFace_holds_minGraphProps') apply (simp add: minGraphProps_def minGraphProps'_def)
by (simp add: splitFace_def split_def)


lemma set_faces_splitFace:
"\<lbrakk> minGraphProps g; f \<in> \<F> g; pre_splitFace g v1 v2 f vs;
  (f1, f2, g') = splitFace g v1 v2 f vs \<rbrakk>
  \<Longrightarrow> \<F> g' = {f1,f2} \<union> (\<F> g - {f})"
apply(frule minGraphProps11')
apply(blast dest:splitFace_new_f21 splitFace_new_f12
                 splitFace_faces_1 splitFace_delete_oldF)
done


declare minGraphProps8 minGraphProps8a minGraphProps8a' [intro]

lemma splitFace_holds_facesAt_distinct:
assumes pre: "pre_splitFace g v w f [countVertices g..<countVertices g + n]"
    and mgp: "minGraphProps g"
shows "facesAt_distinct (snd (snd (splitFace g v w f [countVertices g..<countVertices g + n])))"
proof -
  define ws where "ws = [countVertices g..<countVertices g + n]"
  define f21 where "f21 = snd (split_face f v w ws)"
  with pre ws_def have dist_f21: "distinct (vertices f21)" by (auto intro: split_face_distinct2)
  define f12 where "f12 = fst (split_face f v w ws)"
  with pre ws_def have dist_f12: "distinct (vertices f12)" by (auto intro: split_face_distinct1)
  define vs1 where "vs1 = between (vertices f) v w"
  define vs2 where "vs2 = between (vertices f) w v"
  define g' where "g' = snd (snd (splitFace g v w f [countVertices g..<countVertices g + n]))"
  from f12_def f21_def ws_def g'_def
  have fdg: "(f12, f21, g') = splitFace g v w f [countVertices g..<countVertices g + n]"
    by (simp add: splitFace_def split_def)
  from pre mgp fdg have new_f12: "f12 \<notin> \<F> g"
    apply (rule_tac splitFace_new_f12)  by simp_all
  from pre mgp fdg have new_f21: "f21 \<notin> \<F> g"
    apply (rule_tac splitFace_new_f21) by simp_all
  from pre mgp fdg have new_f12_norm: "normFace f12 \<notin> set (normFaces (faces g))"
    apply (rule_tac splitFace_new_f12_norm)  by simp_all
  from pre mgp fdg have new_f21_norm: "normFace f21 \<notin> set (normFaces (faces g))"
    apply (rule_tac splitFace_new_f21_norm) by simp_all


  have "facesAt_distinct g'"
  proof (rule facesAt_distinctI)
    fix x assume x: "x \<in> \<V> g'"
    show "distinct (normFaces (facesAt g' x))"
      proof -
      from mgp pre have a: "v < |faceListAt g|" "w < |faceListAt g|"
        apply (unfold pre_splitFace_def)
        apply (simp_all add: minGraphProps4)
        by (auto intro: minGraphProps9')
      then show ?thesis
      proof (cases "x = w")
        case True
        moreover with pre have "v \<noteq> w"
          by (unfold pre_splitFace_def) simp
        moreover note a x pre mgp
        ultimately show ?thesis
          apply -
          apply (unfold pre_splitFace_def)
          apply (unfold g'_def splitFace_def facesAt_def)
          apply (simp add: split_def nth_append)
          apply (rule distinct_replace_norm)
            apply (rule distinct_replacefacesAt_norm)
                apply simp
               apply (rule between_distinct)
               apply simp
              apply (rule distinct_replacefacesAt_norm)
                  apply assumption
                 apply (rule between_distinct)
                 apply simp
                apply (rule minGraphProps8a') apply assumption+  apply (simp add: minGraphProps4)
               apply (simp add: normFaces_def)

              apply (subgoal_tac "set (faceListAt g ! w) = {f \<in> \<F> g. w \<in> \<V> f}") apply simp
               apply (subgoal_tac "set (normFaces (faces g)) \<inter> {normFace f12} = {}")
                apply (simp add: f12_def ws_def normFaces_def) apply blast
               apply (simp add: new_f12_norm)

              apply (frule minGraphProps_facesAt_eq)
               apply (subgoal_tac "w \<in> \<V> g") apply assumption
               apply (rule minGraphProps9) apply assumption apply blast apply simp
              apply (simp add: facesAt_def split: if_split_asm)

             apply (simp add: normFaces_def)

            apply (subgoal_tac "w \<notin> set (between (vertices f) v w)")
             apply (simp add: replacefacesAt_notin)
             apply (subgoal_tac "set (faceListAt g ! w) = {f \<in> \<F> g. w \<in> \<V> f}")
              apply (subgoal_tac "set (normFaces (faces g)) \<inter> {normFace f21} = {}")
               apply (simp add: f21_def ws_def normFaces_def) apply blast
              apply (simp add: new_f21_norm)

             apply (frule minGraphProps_facesAt_eq)
              apply (subgoal_tac "w \<in> \<V> g") apply assumption
              apply (rule minGraphProps9) apply assumption apply blast apply simp
             apply (simp add: facesAt_def minGraphProps4 vertices_graph)
            apply (rule between_not_r2) apply simp
        
           apply (simp add: normFaces_def) apply (rule splitFace_f12_f21_neq_norm)
             apply (rule pre) apply simp
           apply (subgoal_tac "(f12, f21, g') = splitFace g v w f [countVertices g..<countVertices g + n]")
            apply (simp add: f12_def f21_def g'_def ws_def)
           apply (rule fdg)

          apply (subgoal_tac "w \<notin> set (between (vertices f) w v)")
           apply (simp add: replacefacesAt_notin)
           apply (subgoal_tac "w \<notin> set (between (vertices f) v w)")
            apply (simp add: replacefacesAt_notin)
            apply (subgoal_tac "set (faceListAt g ! w) = {f \<in> \<F> g. w \<in> \<V> f}")
             apply (subgoal_tac "set (normFaces (faces g)) \<inter> {normFace f12,normFace f21} = {}")
              apply (simp add: f12_def f21_def ws_def normFaces_def) apply blast
             apply (simp add: new_f21_norm new_f12_norm)
            apply (frule minGraphProps_facesAt_eq)
             apply (subgoal_tac "w \<in> \<V> g") apply assumption
             apply (rule minGraphProps9) apply assumption apply blast apply simp
            apply (simp add: facesAt_def minGraphProps4 vertices_graph)
           apply (rule between_not_r2) apply simp
          apply (rule between_not_r1) by simp
      next
        from pre have vw_neq: "v \<noteq> w"
          by (unfold pre_splitFace_def) simp
        case False then show ?thesis
          proof (cases "x = v")
            case True
              with a x pre mgp vw_neq
              show ?thesis
                apply -
                apply (unfold pre_splitFace_def)
                apply (unfold g'_def splitFace_def facesAt_def)
                apply (simp add: split_def nth_append)
                apply (rule distinct_replace_norm)
                  apply (rule distinct_replacefacesAt_norm)
                      apply simp
                     apply (rule between_distinct)
                     apply simp
                    apply (rule distinct_replacefacesAt_norm)
                        apply assumption
                       apply (rule between_distinct)
                       apply simp
                      apply (rule minGraphProps8a) apply assumption+ apply (simp add: minGraphProps4 vertices_graph)

                     apply (simp add:normFaces_def)

                    apply (subgoal_tac "set (faceListAt g ! v) = {f \<in> \<F> g. v \<in> \<V> f}")
                     apply (subgoal_tac "set (normFaces (faces g)) \<inter> {normFace f12} = {}")
                      apply (simp add: f12_def ws_def normFaces_def) apply blast
                     apply (simp add: new_f12_norm)

                    apply (frule minGraphProps_facesAt_eq)
                     apply (subgoal_tac "v \<in> \<V> g") apply assumption
                     apply (rule minGraphProps9) apply assumption apply blast apply simp
                    apply (simp add: facesAt_def split: if_split_asm)

                   apply (simp add: normFaces_def)

                  apply (subgoal_tac "v \<notin> set (between (vertices f) v w)")
                   apply (simp add: replacefacesAt_notin)
                   apply (subgoal_tac "set (faceListAt g ! v) = {f \<in> \<F> g. v \<in> \<V> f}")
                    apply (subgoal_tac "set (normFaces (faces g)) \<inter> {normFace f21} = {}")
                     apply (simp add: f21_def ws_def normFaces_def) apply blast
                    apply (simp add: new_f21_norm)

                   apply (frule minGraphProps_facesAt_eq)
                    apply (subgoal_tac "v \<in> \<V> g") apply assumption
                    apply (rule minGraphProps9) apply assumption apply blast apply simp
                   apply (simp add: facesAt_def split: if_split_asm)
                  apply (rule between_not_r1) apply simp
                 apply (simp add: normFaces_def) apply (rule not_sym)
                 apply (rule splitFace_f12_f21_neq_norm) apply (rule pre) apply simp
                 apply (subgoal_tac "(f12, f21, g') = splitFace g v w f [countVertices g..<countVertices g + n]")
                  apply (simp add: f12_def f21_def ws_def g'_def)  apply (rule fdg)

                apply (subgoal_tac "v \<notin> set (between (vertices f) w v)")
                 apply (simp add: replacefacesAt_notin)
                 apply (subgoal_tac "v \<notin> set (between (vertices f) v w)")
                  apply (simp add: replacefacesAt_notin)
                  apply (subgoal_tac "set (faceListAt g ! v) = {f \<in> \<F> g. v \<in> \<V> f}")
                   apply (subgoal_tac "set (normFaces (faces g)) \<inter> {normFace f21,normFace f12} = {}")
                    apply (simp add: f12_def f21_def ws_def normFaces_def) apply blast
                   apply (simp add: new_f21_norm new_f12_norm)
                  apply (subgoal_tac "set (normFaces (faces g)) \<inter> {normFace f21} = {}")
                   apply (simp add: new_f21_norm)
                   apply (frule minGraphProps_facesAt_eq)
                    apply (subgoal_tac "v \<in> \<V> g") apply assumption
                    apply (rule minGraphProps9) apply assumption apply blast apply simp
                   apply (simp add: facesAt_def minGraphProps4 vertices_graph)
                  apply (simp add: new_f21_norm)
                 apply (rule between_not_r1) apply simp
                apply (rule between_not_r2) by simp
              next
                assume xw_neq: "x \<noteq> w"
                case False
                with a x pre mgp vw_neq xw_neq
                show ?thesis
                  apply -
                  apply (unfold pre_splitFace_def g'_def splitFace_def facesAt_def)
                  apply (simp add: split_def nth_append)
                  apply (case_tac "x < |faceListAt g|")
                   apply simp
                   apply (subgoal_tac "x \<in> \<V> g")
                    apply (rule distinct_replacefacesAt_norm)
                        apply simp
                       apply (rule between_distinct)
                       apply simp
                      apply (rule distinct_replacefacesAt_norm) apply assumption
                         apply (rule between_distinct)
                         apply simp
                        apply (rule minGraphProps8a) apply assumption apply (simp add: minGraphProps4)

                       apply (simp add: normFaces_def)

                      apply (subgoal_tac "set (faceListAt g ! x) = {f \<in> \<F> g. x \<in> \<V> f}")
                       apply (subgoal_tac "set (normFaces (faces g)) \<inter> {normFace f12} = {}")
                        apply (simp add: f12_def ws_def normFaces_def) apply blast
                       apply (simp add: new_f12_norm)

                      apply (frule minGraphProps_facesAt_eq) apply assumption
                      apply (simp add: facesAt_def split: if_split_asm)
                     apply (simp add: normFaces_def)

                    apply (case_tac "x \<notin> set (between (vertices f) v w)")
                     apply (simp add: replacefacesAt_notin)
                     apply (subgoal_tac "set (faceListAt g ! x) = {f \<in> \<F> g. x \<in> \<V> f}")
                      apply (subgoal_tac "set (normFaces (faces g)) \<inter> {normFace f21} = {}")
                       apply (simp add: f21_def ws_def normFaces_def) apply blast
                      apply (simp add: new_f21_norm)

                     apply (frule minGraphProps_facesAt_eq) apply assumption
                     apply (simp add: facesAt_def split: if_split_asm)
                    apply (simp add: normFaces_def)
                    apply (drule replacefacesAt_nth) apply assumption
                        apply (subgoal_tac "f \<notin> set [fst (split_face f v w [countVertices g..<countVertices g + n])]")
                         apply assumption apply simp
                        apply (rule splitFace_f12_oldF_neq)
                          apply (subgoal_tac "pre_splitFace g v w f [countVertices g..<countVertices g + n]")
                           apply assumption apply (simp add: pre) apply assumption+
                        apply (simp add: splitFace_def split_def)
                       apply (rule normFaces_distinct)
                       apply (rule minGraphProps8a) apply assumption apply (simp add: minGraphProps4 vertices_graph)
                      apply (simp add: normFaces_def)
                     apply (rule impI) apply simp
                     apply (subgoal_tac "set (faceListAt g ! x) = {f \<in> \<F> g. x \<in> \<V> f}")
                      apply (subgoal_tac "\<F> g \<inter> {f12} = {}")
                       apply (simp add: f12_def ws_def)
                      apply (simp add: new_f12)
                     apply (frule minGraphProps_facesAt_eq)
                      apply (subgoal_tac "x \<in> \<V> g") apply assumption
                      apply (simp add: minGraphProps4 vertices_graph)
                     apply (simp add:facesAt_def minGraphProps4 vertices_graph)
                    apply (frule replacefacesAt_nth) apply assumption

                        apply (subgoal_tac "f \<notin> set [fst (split_face f v w [countVertices g..<countVertices g + n])]")
                         apply assumption apply simp apply (rule splitFace_f12_oldF_neq)
                          apply (subgoal_tac "pre_splitFace g v w f [countVertices g..<countVertices g + n]") apply assumption
                          apply (simp add: pre) apply assumption apply (simp add: splitFace_def split_def)
                       apply (rule normFaces_distinct)
                       apply (rule minGraphProps8a') apply assumption apply (simp add: minGraphProps4)
                      apply simp
                     apply (rule impI) apply simp
                     apply (subgoal_tac "set (faceListAt g ! x) = {f \<in> \<F> g. x \<in> \<V> f}")
                      apply (subgoal_tac "\<F> g \<inter> {f12} = {}")
                       apply (simp add: f12_def ws_def)
                      apply (simp add: new_f12)
                     apply (frule minGraphProps_facesAt_eq)
                      apply (subgoal_tac "x \<in> \<V> g") apply assumption
                      apply (simp add: minGraphProps4 vertices_graph)
                     apply (simp add:facesAt_def minGraphProps4 vertices_graph)
                    apply (simp add: f12_def [symmetric] f21_def [symmetric] ws_def [symmetric])
                    apply (subgoal_tac "normFace f21 \<notin> set (normFaces (replace f [f12] (faceListAt g ! x)))")
                     apply (simp add: normFaces_def)
                    apply (rule ccontr) apply simp
                    apply (frule normFace_replace_in)
                    apply (subgoal_tac "normFace f12 \<noteq> normFace f21")
                     apply (subgoal_tac "normFace f21 \<notin> set (normFaces (faceListAt g ! x))")
                      apply (simp add: normFaces_def)
                     apply (rule ccontr) apply simp
                     apply (subgoal_tac "normFace f21 \<notin> set (normFaces (facesAt g x))")
                      apply (simp add: facesAt_def)(*
                      apply (subgoal_tac "x \<in> \<V> g") apply (simp add: normFaces_def)
                      apply (simp add: minGraphProps4 vertices_graph)*)
                     apply (subgoal_tac "normFace f21 \<notin> set (normFaces (faces g))") apply (frule minGraphProps_facesAt_eq)
                       apply (subgoal_tac "x \<in> \<V> g") apply assumption apply (simp add: minGraphProps4 vertices_graph)
                      apply (simp add: normFaces_def) apply (rule ccontr)  apply simp
                      apply blast
                     apply (rule new_f21_norm)
                    apply (rule splitFace_f12_f21_neq_norm) apply (rule pre) apply simp apply (rule fdg)
                   apply (simp add: minGraphProps4 vertices_graph)

(* zweite große Implikation *)
                  apply (simp add: normFaces_def)
                  apply (subgoal_tac "(x - |faceListAt g | ) < n") apply simp
                   apply (rule splitFace_f12_f21_neq_norm) apply (rule pre) apply simp
                   apply (simp add: f12_def [symmetric] f21_def [symmetric]  ws_def [symmetric]) apply (simp add: ws_def) apply (rule fdg)
                by (simp add: minGraphProps4)
              qed
            qed
          qed
        qed
  then show ?thesis by (simp add: g'_def)
qed


lemma splitFace_holds_facesAt_eq:
assumes pre_F: "pre_splitFace g' v a f' [countVertices g'..<countVertices g' + n]"
and mgp: "minGraphProps g'"
and g'': "g'' = (snd (snd (splitFace g' v a f' [countVertices g'..<countVertices g' + n])))"
shows "facesAt_eq g''"
proof -
  have "[0..<countVertices g''] = [0..<countVertices g' + n]"
    apply (simp add: g'') by (simp add: splitFace_def split_def)
  hence vg'': "vertices g'' = [0..<countVertices g' + n]" by (simp add:vertices_graph)

  define ws where "ws = [countVertices g'..<countVertices g' + n]"
  define f21 where "f21 = snd (split_face f' v a ws)"
  define f12 where "f12 = fst (split_face f' v a ws)"
  define vs1 where "vs1 = between (vertices f') v a"
  define vs2 where "vs2 = between (vertices f') a v"
  from ws_def [symmetric] f21_def [symmetric] f12_def [symmetric] g'' have fdg: "(f12, f21, g'') = splitFace g' v a f' ws"
    by (simp add: splitFace_def split_def)
  from pre_F have pre_F': "pre_splitFace g' v a f' ws" apply (unfold pre_splitFace_def ws_def) by force

  from pre_F' mgp fdg have f'_f21: "f' \<noteq> f21" apply (rule_tac splitFace_f21_oldF_neq) apply assumption by simp+
  from pre_F' mgp fdg have f'_f12: "f' \<noteq> f12" apply (rule_tac splitFace_f12_oldF_neq) apply assumption by simp+

  from f12_def vs1_def have vert_f12: "vertices f12 = rev ws @ v # vs1 @ [a]" by (simp add: split_face_def)
  from f21_def vs2_def have vert_f21: "vertices f21 = a # vs2 @ v # ws" by (simp add: split_face_def)
  from vs1_def vs2_def pre_F have vertFrom_f': "verticesFrom f' v =
    v # vs1 @ a # vs2" apply simp
    apply (rule_tac verticesFrom_ram1) by (rule pre_splitFace_pre_split_face)
  from vs1_def vs2_def pre_F vertFrom_f' have vert_f': "\<V> f' =  set vs1 \<union> set vs2 \<union> {a,v}"
    apply (subgoal_tac "(vertices f') \<cong> (verticesFrom f' v)") apply (drule congs_pres_nodes)
    apply (simp add: congs_pres_nodes) apply blast
    apply (rule verticesFrom_congs) by (simp only: pre_splitFace_def)
  from pre_F have dist_vertFrom_f': "distinct (verticesFrom f' v)" apply (rule_tac verticesFrom_distinct)
    by (simp only: pre_splitFace_def)+
  then have vs1_vs2_empty: "set vs1 \<inter> set vs2 = {}" by (simp add: vertFrom_f')

  from ws_def f21_def f12_def have "faces g'' = (replace f' [f21]  (faces g')) @ [f12]"
    apply (simp add: g'') by (simp add: splitFace_def split_def)

  from mgp have dist_all: "\<And>x. x \<in> \<V> g' \<Longrightarrow> distinct (faceListAt g' ! x)"
    apply (rule_tac normFaces_distinct)
    by (simp add: minGraphProps_def facesAt_distinct_def facesAt_def)

  from mgp have fla: "|faceListAt g'| = countVertices g'"
    by (simp add: minGraphProps_def faceListAt_len_def)

  from ws_def [symmetric] f21_def [symmetric] f12_def [symmetric]
    vs1_def [symmetric] vs2_def [symmetric] pre_F mgp vert_f'
show ?thesis
apply (simp add: g'')
apply (unfold splitFace_def facesAt_eq_def facesAt_def)
apply (rule ballI)
apply (simp only: split_def Let_def)
apply (simp only: snd_conv)
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp only: faceListAt.simps vertices_graph.simps split:if_split_asm)
 apply (case_tac "v < |faceListAt g'| \<and> a < | faceListAt g'|")
  apply (simp only: nth_append split: if_split_asm)
   apply (case_tac "va < | faceListAt g' |")
    apply (subgoal_tac "va \<in> \<V> g'")
     apply (subgoal_tac "distinct vs1 \<and> distinct vs2 \<and>
       v \<notin> set vs1 \<and> v \<notin> set vs2 \<and> a \<notin> set vs1 \<and> a \<notin> set vs2 \<and> a \<noteq> v \<and> v \<noteq> a \<and> set vs1 \<inter> set vs2 = {}" )
      apply (case_tac "a = va")
       apply (simp add:replacefacesAt_nth2 replacefacesAt_notin)
       apply (subgoal_tac "distinct (faceListAt g' ! va)")
        apply (subgoal_tac "distinct (faces g')")
         apply (simp add: replace6)
         apply (case_tac "x = f12") apply (simp add: vert_f12) apply simp
         apply (case_tac "x = f'") apply (simp add: vert_f21) apply(simp)
         apply (case_tac "x = f21") apply (simp add: vert_f21) apply (simp)
         apply (rule conjI)
          apply (rule minGraphProps5) apply assumption apply assumption apply (fastforce simp: facesAt_def)
         apply (rule minGraphProps6) apply assumption apply assumption apply (simp add: facesAt_def)
        apply (rule minGraphProps11') apply simp
       apply (subgoal_tac "distinct (facesAt g' va)") apply (simp add: facesAt_def)
       apply (rule normFaces_distinct) apply (rule minGraphProps8) apply simp apply simp apply simp
      apply (case_tac "v = va")
       apply (simp add:replacefacesAt_nth2 replacefacesAt_notin)
       apply (subgoal_tac "distinct (faceListAt g' ! va)")
        apply (subgoal_tac "distinct (faces g')")
         apply (simp add: replace6)
         apply (case_tac "x = f12") apply (simp add: vert_f12) apply simp
         apply (case_tac "x = f'") apply (simp add: vert_f21) apply simp
         apply (case_tac "x = f21") apply (simp add: vert_f21) apply simp
         apply (rule conjI)
          apply (rule minGraphProps5) apply assumption apply assumption apply (fastforce simp: facesAt_def)
         apply (rule minGraphProps6) apply assumption apply assumption apply(fastforce simp: facesAt_def)
        apply (rule minGraphProps11') apply simp
       apply (subgoal_tac "distinct (facesAt g' va)") apply (simp add: facesAt_def)
       apply (rule normFaces_distinct) apply (rule minGraphProps8) apply simp apply simp apply simp
      apply (case_tac "va \<in> set vs1")
       apply (subgoal_tac "va \<notin> set vs2")
        apply (simp add:replacefacesAt_nth2 replacefacesAt_notin replacefacesAt_in)
        apply (subgoal_tac "distinct (faceListAt g' ! va)")
         apply (subgoal_tac "distinct (faces g')")
          apply (simp add: replace6)
          apply (case_tac "x = f12") apply (simp add: vert_f12) apply simp
          apply (case_tac "x = f'") apply (simp add: vert_f21) apply simp
          apply (rule conjI)
           apply (rule disjI2)
           apply (rule minGraphProps5) apply assumption apply assumption apply (fastforce simp: facesAt_def)
          apply (rule minGraphProps6) apply assumption apply assumption apply (fastforce simp: facesAt_def)
         apply (rule minGraphProps11') apply simp
        apply (subgoal_tac "distinct (facesAt g' va)") apply (simp add: facesAt_def)
        apply (rule normFaces_distinct) apply (rule minGraphProps8) apply assumption apply assumption
       apply blast
      apply (case_tac "va \<in> set vs2")
       apply (simp add:replacefacesAt_nth2 replacefacesAt_notin replacefacesAt_in)
       apply (subgoal_tac "distinct (faceListAt g' ! va)")
        apply (subgoal_tac "distinct (faces g')")
         apply (simp add: replace6)
         apply (case_tac "x = f21") apply (simp add: vert_f21) apply simp
         apply (case_tac "x = f'") apply (simp add: vert_f21) apply simp
         apply (rule conjI)
          apply (rule disjI2)
          apply (rule minGraphProps5) apply assumption apply assumption apply (fastforce simp: facesAt_def)
         apply (rule minGraphProps6) apply assumption apply assumption apply (fastforce simp: facesAt_def)
        apply (rule minGraphProps11') apply simp
       apply (subgoal_tac "distinct (facesAt g' va)") apply (simp add: facesAt_def)
       apply (rule normFaces_distinct) apply (rule minGraphProps8) apply assumption apply assumption
    (* case else *)
      apply (simp add:replacefacesAt_nth2 replacefacesAt_notin replacefacesAt_in)
      apply (subgoal_tac "distinct (faceListAt g' ! va)")
       apply (subgoal_tac "distinct (faces g')")
        apply (simp add: replace6)
        apply (case_tac "x = f'")
         apply (subgoal_tac "va \<in> \<V> f'") apply simp
         apply (rule minGraphProps6) apply simp apply (simp add: fla)
         apply (simp add: facesAt_def)
        apply simp
        apply (rule conjI)
         apply (rule disjI2) apply (rule disjI2)
         apply (rule minGraphProps5) apply assumption apply assumption apply (fastforce simp: facesAt_def)
        apply (rule minGraphProps6) apply assumption apply assumption apply(fastforce simp: facesAt_def)
       apply (rule minGraphProps11') apply assumption
      apply (subgoal_tac "distinct (facesAt g' va)") apply (simp add: facesAt_def)
      apply (rule normFaces_distinct) apply (rule minGraphProps8) apply assumption apply assumption apply simp
     apply (subgoal_tac "distinct (vertices f12) \<and> distinct (vertices f21)")
      apply (simp add: vert_f12 vert_f21)
      apply (rule vs1_vs2_empty)
     apply (subgoal_tac "pre_split_face f' v a ws")
      apply (simp add: f12_def f21_def split_face_distinct1' split_face_distinct2')
     apply simp
    apply (simp add: vertices_graph fla)
    (* va in ws *)
   apply simp
  apply (subgoal_tac "distinct (faces g')")
   apply (simp add: replace6)
   apply (thin_tac "[countVertices g'..<countVertices g' + n] = ws")
   apply (subgoal_tac "(va - |faceListAt g'| ) < | ws |") apply simp apply (rule conjI) apply blast
    apply (subgoal_tac "va \<in> set ws")
     apply (case_tac "x = f12") apply (simp add: vert_f12) apply (simp add: vert_f21)
    apply (simp add: ws_def fla)
   apply (simp add: ws_def fla)
  apply (rule minGraphProps11') apply assumption
 apply (subgoal_tac "v \<in> \<V> g' \<and> a \<in> \<V> g'")
  apply (simp only: fla in_vertices_graph)
 apply (subgoal_tac "f' \<in> \<F> g'")
  apply (subgoal_tac "v \<in> \<V> f' \<and> a \<in> \<V> f'") apply (simp only: minGraphProps9) apply force
  apply (subgoal_tac "pre_split_face f' v a ws") apply (simp only: pre_split_face_def) apply force
  apply (rule pre_splitFace_pre_split_face) apply assumption
 apply (simp only: pre_splitFace_def)

(* Rückrichtung *)
apply (rule subsetI)
apply (case_tac "v < |faceListAt g'| \<and> a < | faceListAt g'|")
 apply (case_tac "va < | faceListAt g' |")
  apply (subgoal_tac "va \<in> \<V> g'")
   apply (subgoal_tac "distinct vs1 \<and> distinct vs2 \<and>
       v \<notin> set vs1 \<and> v \<notin> set vs2 \<and> a \<notin> set vs1 \<and> a \<notin> set vs2 \<and> a \<noteq> v \<and> v \<noteq> a \<and> set vs1 \<inter> set vs2 = {}" )
    apply (simp del: replacefacesAt_simps add: nth_append)
    apply (case_tac "a = va")
     apply (simp add:replacefacesAt_nth2 replacefacesAt_notin)
     apply (subgoal_tac "distinct (faceListAt g' ! va)")
      apply (subgoal_tac "distinct (faces g')")
       apply (simp add: replace6)
       apply (case_tac "x = f12") apply simp apply (rule disjI1) apply (rule minGraphProps7') apply simp  apply simp apply simp
       apply (case_tac "x = f21") apply simp apply (rule disjI1) apply (rule minGraphProps7') apply simp  apply simp apply simp
       apply simp apply (rule minGraphProps7') apply simp apply simp apply  simp
      apply (rule minGraphProps11') apply simp
     apply (rule normFaces_distinct) apply (rule minGraphProps8a) apply simp apply assumption
    apply simp
    apply (case_tac "v = va")
     apply (simp add:replacefacesAt_nth2 replacefacesAt_notin)
     apply (subgoal_tac "distinct (faceListAt g' ! va)")
      apply (subgoal_tac "distinct (faces g')")
       apply (simp add: replace6)
       apply (case_tac "x = f12") apply simp apply (rule disjI1) apply (rule minGraphProps7') apply simp  apply simp apply simp
       apply (case_tac "x = f21") apply simp apply (rule disjI1) apply (rule minGraphProps7') apply simp  apply simp apply simp
       apply simp apply (rule minGraphProps7') apply simp apply simp apply  simp
      apply (rule minGraphProps11') apply simp apply (rule normFaces_distinct)      apply (rule minGraphProps8a) apply simp apply simp     apply (case_tac "va \<in> set vs1")
     apply (subgoal_tac "va \<notin> set vs2")
      apply (simp add:replacefacesAt_nth2 replacefacesAt_notin replacefacesAt_in)
      apply (subgoal_tac "distinct (faceListAt g' ! va)")
       apply (subgoal_tac "distinct (faces g')")
        apply (simp add: replace6)
        apply (case_tac "x = f12") apply simp apply (rule disjI1) apply (rule minGraphProps7') apply simp  apply simp apply simp
        apply (case_tac "x = f'")
         apply (subgoal_tac "f' \<noteq> f21") apply simp apply (rule splitFace_f21_oldF_neq)
           apply (rule pre_F')
          apply simp
         apply (rule fdg)
        apply (case_tac "x = f21") apply (simp add: vert_f21 fla) apply (thin_tac "[countVertices g'..<countVertices g' + n] = ws")
         apply (simp add: ws_def)
        apply simp apply (rule minGraphProps7') apply simp  apply simp apply simp
       apply (rule minGraphProps11') apply simp
      apply (rule normFaces_distinct) apply (rule minGraphProps8a) apply simp apply simp
     apply blast
    apply (case_tac "va \<in> set vs2")
     apply (simp add:replacefacesAt_nth2 replacefacesAt_notin replacefacesAt_in)
     apply (subgoal_tac "distinct (faceListAt g' ! va)")
      apply (subgoal_tac "distinct (faces g')")
       apply (simp add: replace6)
       apply (case_tac "x = f21") apply simp apply (rule disjI1) apply (rule minGraphProps7') apply simp  apply simp apply simp
       apply (case_tac "x = f'")
        apply (subgoal_tac "f' \<noteq> f12") apply simp apply (rule splitFace_f12_oldF_neq)
          apply (rule pre_F') apply simp  apply (rule fdg)
       apply (case_tac "x = f12") apply (simp add: vert_f12 fla) apply (thin_tac "[countVertices g'..<countVertices g' + n] = ws")
        apply (simp add: ws_def)
       apply simp apply (rule minGraphProps7') apply simp  apply simp apply simp
      apply (rule minGraphProps11') apply simp apply (rule normFaces_distinct) apply (rule minGraphProps8a) apply simp apply simp
    apply (simp add:replacefacesAt_nth2 replacefacesAt_notin replacefacesAt_in)
    apply (subgoal_tac "distinct (faces g')")
     apply (simp add: replace6)
     apply (rule minGraphProps7') apply simp
      apply (case_tac "x = f21") apply (simp add: vert_f21) apply (thin_tac "[countVertices g'..<countVertices g' + n] = ws")
       apply (simp add: ws_def vertices_graph)
      apply (case_tac "x = f12") apply (simp add: vert_f12) apply (thin_tac "[countVertices g'..<countVertices g' + n] = ws")
       apply (simp add: ws_def vertices_graph)
      apply simp
     apply simp
    apply (rule minGraphProps11') apply simp
   apply (subgoal_tac "distinct (vertices f12) \<and> distinct (vertices f21)")
    apply (simp add: vert_f12 vert_f21)
    apply (rule vs1_vs2_empty)
   apply (subgoal_tac "pre_split_face f' v a ws")
    apply (simp add: f12_def f21_def split_face_distinct1' split_face_distinct2')
   apply (simp add: pre_splitFace_pre_split_face[OF pre_F'])
  apply (simp add: vertices_graph fla)
 apply (simp add: nth_append del:replacefacesAt_simps)
 apply (subgoal_tac "distinct (faces g')")
  apply (simp add: replace6)
  apply (thin_tac "[countVertices g'..<countVertices g' + n] = ws")
  apply (subgoal_tac "(va - |faceListAt g'| ) < |ws|") apply simp
   apply (rule ccontr) apply simp
   apply (case_tac "x = f'") apply simp apply simp
   apply (subgoal_tac "va \<in> \<V> g'") apply (simp add: fla vertices_graph)
   apply (rule minGraphProps9) apply simp apply force
   apply (simp add: fla) apply (metis minGraphProps9')
  apply (simp add: ws_def fla)
 apply (rule minGraphProps11') apply simp
apply (subgoal_tac "v \<in> \<V> g' \<and> a \<in> \<V> g'")
 apply (simp only: fla in_vertices_graph)
apply (subgoal_tac "f' \<in> \<F> g'")
 apply (subgoal_tac "v \<in> \<V> f' \<and> a \<in> \<V> f'") apply (simp only: minGraphProps9) apply force
by force
qed

lemma splitFace_holds_faces_subset:
assumes pre_F: "pre_splitFace g' v a f' [countVertices g'..<countVertices g' + n]"
and mgp: "minGraphProps g'"
shows "faces_subset (snd (snd (splitFace g' v a f' [countVertices g'..<countVertices g' + n])))"
proof -
  define g'' where "g'' = (snd (snd (splitFace g' v a f' [countVertices g'..<countVertices g' + n])))"
  define ws where "ws = [countVertices g'..<countVertices g' + n]"
  define f21 where "f21 = snd (split_face f' v a ws)"
  define f12 where "f12 = fst (split_face f' v a ws)"
  define vs1 where "vs1 = between (vertices f') v a"
  define vs2 where "vs2 = between (vertices f') a v"
  from ws_def [symmetric] f21_def [symmetric] f12_def [symmetric] g''_def
    have fdg: "(f12, f21, g'') = splitFace g' v a f' ws"
      by (simp add: splitFace_def split_def)
  from pre_F have pre_F': "pre_splitFace g' v a f' ws" apply (unfold pre_splitFace_def ws_def) by force

  from f12_def vs1_def have vert_f12: "vertices f12 = rev ws @ v # vs1 @ [a]" by (simp add: split_face_def)
  from f21_def vs2_def have vert_f21: "vertices f21 = a # vs2 @ v # ws" by (simp add: split_face_def)
  from vs1_def vs2_def pre_F have vertFrom_f': "verticesFrom f' v =
    v # vs1 @ a # vs2" apply simp
    apply (rule_tac verticesFrom_ram1) by (rule pre_splitFace_pre_split_face)
  from vs1_def vs2_def pre_F vertFrom_f' have vert_f': "\<V> f' =  set vs1 \<union> set vs2 \<union> {a,v}"
    apply (subgoal_tac "(vertices f') \<cong> (verticesFrom f' v)") apply (drule congs_pres_nodes)
    apply (simp add: congs_pres_nodes) apply blast
    apply (rule verticesFrom_congs) by (simp only: pre_splitFace_def)

  from ws_def f21_def f12_def have faces:"faces g'' = (replace f' [f21]  (faces g')) @ [f12]"
    apply (simp add: g''_def) by (simp add: splitFace_def split_def)

  from ws_def have vertices:"vertices g'' = vertices g' @ ws" by (simp add: g''_def)

  from ws_def [symmetric] f21_def [symmetric] f12_def [symmetric]
    vs1_def [symmetric] vs2_def [symmetric] pre_F mgp  g''_def [symmetric] show ?thesis
    apply (simp add: faces_subset_def) apply (rule ballI)  apply (simp add: faces vertices)
    apply (subgoal_tac "\<V> f' \<subseteq> \<V> g'")
    apply (case_tac "f = f12") apply (simp add: vert_f12 vert_f') apply force
    apply simp apply (drule replace5)
    apply (case_tac "f = f21") apply (simp add: vert_f21 vert_f') apply force
    apply simp apply (rule subsetI) apply (frule minGraphProps9) apply assumption+ apply simp
    apply (rule subsetI) apply (rule minGraphProps9) by auto
qed


lemma splitFace_holds_edges_sym:
assumes pre_F: "pre_splitFace g' v a f' ws"
and mgp: "minGraphProps g'"
shows "edges_sym (snd (snd (splitFace g' v a f' ws)))"
proof -
  define g'' where "g'' = (snd (snd (splitFace g' v a f' ws)))"
  define f21 where "f21 = snd (split_face f' v a ws)"
  define f12 where "f12 = fst (split_face f' v a ws)"
  define vs1 where "vs1 = between (vertices f') v a"
  define vs2 where "vs2 = between (vertices f') a v"
  from f21_def [symmetric] f12_def [symmetric] g''_def
    have fdg: "(f12, f21, g'') = splitFace g' v a f' ws"
      by (simp add: splitFace_def split_def)
  from pre_F have pre_F': "pre_splitFace g' v a f' ws" apply (unfold pre_splitFace_def) by force

  from f21_def f12_def have faces:"faces g'' = (replace f' [f21]  (faces g')) @ [f12]"
    apply (simp add: g''_def) by (simp add: splitFace_def split_def)

  from f12_def f21_def have split: "(f12, f21) = split_face f' v a ws" by simp

  from pre_F mgp  g''_def [symmetric] split show ?thesis
    apply (simp add: edges_sym_def edges_graph_def f21_def [symmetric] f12_def [symmetric]
    vs1_def [symmetric] vs2_def [symmetric])
    apply (intro allI impI) apply (elim bexE) apply (simp add: faces)
    apply (case_tac "x = f12 \<or> x = f21")
     apply (subgoal_tac "(aa,b) \<in> edges f'  \<or> ((b,aa) \<in> (edges f12 \<union> edges f21) \<and> (aa,b) \<in> (edges f12 \<union> edges f21))") apply simp
      apply (case_tac "(aa, b) \<in> edges f'")
       apply (subgoal_tac "(b,aa) \<in> edges g'")
        apply (simp add: edges_graph_def) apply (elim bexE) apply (rule disjI2) apply (rule bexI)
         apply simp
        apply (subgoal_tac "xa \<noteq> f'") apply (rule replace4) apply simp apply force
        apply (drule minGraphProps12) apply simp apply simp
        apply (rule ccontr) apply simp
       apply (rule minGraphProps10) apply simp apply (simp add: edges_graph_def)
       apply (rule bexI)  apply (thin_tac "(aa, b) \<in> edges x") apply simp
       apply simp
      apply simp
      apply (case_tac "(b, aa) \<in> edges f12") apply simp apply simp
      apply (case_tac "(b, aa) \<in> edges f21") apply (rule bexI)
        apply simp
       apply (rule replace3) apply simp
       apply simp
      apply simp
     apply (subgoal_tac "
     ((aa,b) \<in> edges f'  \<or> ((b,aa) \<in> (edges f12 \<union> edges f21) \<and> (aa,b) \<in> (edges f12 \<union> edges f21))) = ((aa,b) \<in> edges f12 \<or> (aa,b) \<in> edges f21)") apply force
     apply (rule sym) apply simp
     apply (rule split_face_edges_f12_f21_sym) apply (erule pre_splitFace_oldF)
      apply (subgoal_tac "pre_split_face f' v a ws") apply assumption  apply simp
     apply (rule split)
    apply simp
    apply (subgoal_tac "distinct (faces g')") apply (simp add: replace6)
     apply (case_tac "x = f'") apply simp apply simp
     apply (subgoal_tac "(b,aa) \<in> edges g'")
      apply (simp add: edges_graph_def) apply (elim bexE)
      apply (case_tac "xa = f'")
       apply simp apply (frule split_face_edges_or) apply simp apply simp
       apply (case_tac "(b, aa) \<in> edges f12") apply simp apply simp
       apply (rule bexI) apply (thin_tac "(b, aa) \<in> edges f'")
        apply simp
       apply (rule replace3) apply simp apply simp
      apply (rule disjI2) apply (rule bexI) apply simp
      apply (rule replace4) apply simp
      apply force
     apply (rule minGraphProps10) apply simp
     apply (simp add: edges_graph_def)
     apply (rule bexI)  apply simp apply simp
    apply (rule minGraphProps11') by simp
qed


lemma splitFace_holds_faces_distinct:
assumes pre_F: "pre_splitFace g' v a f' [countVertices g'..<countVertices g' + n]"
and mgp: "minGraphProps g'"
shows "faces_distinct (snd (snd (splitFace g' v a f' [countVertices g'..<countVertices g' + n])))"
proof -
  define g'' where "g'' = snd (snd (splitFace g' v a f' [countVertices g'..<countVertices g' + n]))"
  define ws where "ws \<equiv> [countVertices g'..<countVertices g' + n]"
  define f21 where "f21 = snd (split_face f' v a ws)"
  define f12 where "f12 = fst (split_face f' v a ws)"
  define vs1 where "vs1 = between (vertices f') v a"
  define vs2 where "vs2 = between (vertices f') a v"
  from ws_def [symmetric] f21_def [symmetric] f12_def [symmetric] g''_def
  have fdg: "(f12, f21, g'') = splitFace g' v a f' ws"
    by (simp add: splitFace_def split_def)
  from pre_F have pre_F': "pre_splitFace g' v a f' ws" apply (unfold pre_splitFace_def ws_def) by force

  from ws_def f21_def f12_def have faces:"faces g'' = (replace f' [f21]  (faces g')) @ [f12]"
    apply (simp add: g''_def) by (simp add: splitFace_def split_def)
  from f12_def f21_def have split: "(f12, f21) = split_face f' v a ws" by simp

  from ws_def [symmetric] pre_F mgp  g''_def [symmetric] split show ?thesis
    apply (simp add: faces_distinct_def faces)
    apply (subgoal_tac "distinct (normFaces (replace f' [f21] (faces g')))")
     apply (simp add: normFaces_def)
     apply safe
     apply (subgoal_tac "distinct (faces g')") apply (simp add: replace6)
      apply (case_tac "x = f'") apply simp
       apply (subgoal_tac "f' \<noteq> f21") apply simp
       apply (rule splitFace_f21_oldF_neq)
         apply (rule pre_F') apply simp
       apply (rule fdg)
      apply simp
      apply (case_tac "x = f21") apply simp
       apply (subgoal_tac "normFace f12 \<noteq> normFace f21") apply simp
       apply (rule splitFace_f12_f21_neq_norm) apply force apply simp
       apply (simp add: fdg) apply (rule fdg)
      apply simp
      apply (subgoal_tac "normFace f12 \<notin> set (normFaces (faces g'))")
       apply (simp add: normFaces_def)
      apply (rule splitFace_new_f12_norm) apply (rule pre_F')  apply simp
      apply (rule fdg)
     apply (rule minGraphProps11') apply simp
    apply (rule distinct_replace_norm) apply (rule minGraphProps11) apply simp
     apply (simp add: normFaces_def)
    apply (subgoal_tac "normFace f21 \<notin> set (normFaces (faces g'))")
     apply (simp add: normFaces_def)
    apply (rule splitFace_new_f21_norm) apply (rule pre_F')  apply simp
    by (rule fdg)
qed


lemma "help":
shows "xs \<noteq> [] \<Longrightarrow> x \<notin> set xs \<Longrightarrow>  x \<noteq> hd xs" and
      "xs \<noteq> [] \<Longrightarrow> x \<notin> set xs \<Longrightarrow>  x \<noteq> last xs" and
      "xs \<noteq> [] \<Longrightarrow> x \<notin> set xs \<Longrightarrow>  hd xs \<noteq> x" and
      "xs \<noteq> [] \<Longrightarrow> x \<notin> set xs \<Longrightarrow>  last xs \<noteq> x"
by(auto)

lemma split_face_edge_disj:
 "\<lbrakk> pre_split_face f a b vs; (f\<^sub>1, f\<^sub>2) = split_face f a b vs; |vertices f| \<ge> 3;
    vs = [] \<longrightarrow> (a,b) \<notin> edges f \<and> (b,a) \<notin> edges f \<rbrakk>
    \<Longrightarrow> \<E> f\<^sub>1 \<inter> \<E> f\<^sub>2 = {}"
apply(frule pre_split_face_p_between[THEN between_inter_empty])
apply(unfold pre_split_face_def)
apply clarify
apply(subgoal_tac "\<And>x y. x \<in> set vs \<Longrightarrow> y \<in> \<V> f \<Longrightarrow> x \<noteq> y")
 prefer 2 apply blast
apply(subgoal_tac "\<And>x y. x \<in> set vs \<Longrightarrow> y \<in> \<V> f \<Longrightarrow> y \<noteq> x")
 prefer 2 apply blast
apply(subgoal_tac "a \<notin> set vs")
 prefer 2 apply blast
apply(subgoal_tac "b \<notin> set vs")
 prefer 2 apply blast
apply(subgoal_tac "distinct(vs @ a # between (vertices f) a b @ [b])")
 prefer 2 apply(simp add:between_not_r1 between_not_r2 between_distinct)
 apply(blast dest:inbetween_inset)
apply(subgoal_tac "distinct(b # between (vertices f) b a @ a # rev vs)")
 prefer 2 apply(simp add:between_not_r1 between_not_r2 between_distinct)
 apply(blast dest:inbetween_inset)
apply(subgoal_tac "vs = [] \<Longrightarrow> between (vertices f) a b \<noteq> []")
 prefer 2 apply clarsimp apply(frule (4) is_nextElem_between_empty')apply blast
apply(subgoal_tac "vs = [] \<Longrightarrow> between (vertices f) b a \<noteq> []")
 prefer 2 apply clarsimp
apply(frule (3) is_nextElem_between_empty')apply simp apply blast
apply(subgoal_tac "vs \<noteq> [] \<Longrightarrow> hd vs \<notin> \<V> f")
 prefer 2 apply(drule hd_in_set) apply blast
apply(subgoal_tac "vs \<noteq> [] \<Longrightarrow> last vs \<notin> \<V> f")
 prefer 2 apply(drule last_in_set) apply blast
apply(subgoal_tac "\<And>u v. between (vertices f) u v \<noteq> [] \<Longrightarrow> hd(between (vertices f) u v) \<in> \<V> f")
 prefer 2 apply(drule hd_in_set)apply(drule inbetween_inset) apply blast
apply(subgoal_tac "\<And>u v. between (vertices f) u v \<noteq> [] \<Longrightarrow> last (between (vertices f) u v) \<in> \<V> f")
 prefer 2 apply(drule last_in_set) apply(drule inbetween_inset) apply blast
apply(simp add:split_face_def edges_conv_Edges Edges_append Edges_Cons
 last_rev notinset_notinEdge1 notinset_notinEdge2 notinset_notinbetween
 between_not_r1 between_not_r2 "help" Edges_rev_disj disj_sets_disj_Edges
 Int_Un_distrib Int_Un_distrib2)
apply clarify
apply(rule conjI)
 apply clarify
 apply(rule disj_sets_disj_Edges)
 apply simp
 apply(blast dest:inbetween_inset)
apply clarify
apply(rule conjI)
 apply clarify
 apply(rule disj_sets_disj_Edges)
 apply simp
 apply(blast dest:inbetween_inset)
apply clarify
apply(rule conjI)
 apply(rule disj_sets_disj_Edges)
 apply simp
 apply(blast dest:inbetween_inset)
apply(rule disj_sets_disj_Edges)
apply(blast dest:inbetween_inset)
done


lemma splitFace_edge_disj:
assumes mgp: "minGraphProps g" and pre: "pre_splitFace g u v f vs"
and FDG: "(f\<^sub>1,f\<^sub>2,g') = splitFace g u v f vs"
shows "edges_disj g'"
proof -
  from mgp have disj: "edges_disj g" by(simp add:minGraphProps_def)
  have "\<V> g \<inter> set vs = {}" using pre
    by (simp add: pre_splitFace_def)
  hence gvs: "\<forall>f \<in> \<F> g. \<V> f \<inter> set vs = {}"
    by (clarsimp simp:edges_graph_def edges_face_def)
       (blast dest: minGraphProps9[OF mgp])
  have f: "f \<in> \<F> g" by (rule pre_splitFace_oldF[OF pre])
  note split_face = splitFace_split_face[OF f FDG]
  note pre_split_face = pre_splitFace_pre_split_face[OF pre]
  have "\<E> f\<^sub>1 \<inter> \<E> f\<^sub>2 = {}"
    apply(rule split_face_edge_disj[OF pre_split_face split_face mgp_vertices3[OF mgp f]])
    using pre
    apply(simp add:pre_splitFace_def del: pre_splitFace_oldF)
    apply clarify
    by(simp) (* loops if combined *)
  moreover
  { fix f' assume f': "f' \<in> \<F> g" "f' \<noteq> f"
    have "(\<E> f\<^sub>1 \<union> \<E> f\<^sub>2) \<inter> \<E> f' = {}"
    proof cases
      assume vs: "vs = []"
      have "(u,v) \<notin> \<E> g \<and> (v,u) \<notin> \<E> g" using pre vs
        by(simp add:pre_splitFace_def)
      with split_face_edges_f12_f21_vs[OF pre_split_face[simplified vs] split_face[simplified vs]]
      show ?thesis using f f' disj
        by(simp add:is_duplicateEdge_def edges_graph_def edges_disj_def)
    next
      assume vs: "vs \<noteq> []"
      have f12: "vs \<noteq> [] \<Longrightarrow> \<E> f\<^sub>1 \<union> \<E> f\<^sub>2 \<subseteq>
            \<E> f \<union> UNIV \<times> set vs \<union> set vs \<times> UNIV"
        using split_face_edges_f12_f21[OF pre_split_face split_face]
        by simp (fastforce dest:in_Edges_in_set)
      have "\<And>x y. (y,x) \<in> \<E> f' \<Longrightarrow> x \<notin> set vs \<and> y \<notin> set vs"
        using f' gvs by(blast dest:in_edges_in_vertices)
      then show ?thesis using f f' f12 disj vs
        by(simp add: edges_graph_def edges_disj_def) blast
    qed }
  ultimately show ?thesis using disj
    by(simp add:edges_disj_def set_faces_splitFace[OF mgp f pre FDG])
      blast
qed

lemma splitFace_edges_disj2:
 "minGraphProps g \<Longrightarrow> pre_splitFace g u v f vs
 \<Longrightarrow> edges_disj(snd(snd(splitFace g u v f vs)))"
apply(subgoal_tac "pre_splitFace g u v f vs")
 prefer 2 apply(simp)
by(drule (1) splitFace_edge_disj[where f\<^sub>1 = "fst(splitFace g u v f vs)" and f\<^sub>2 = "fst(snd(splitFace g u v f vs))"], auto)


lemma vertices_conv_Union_edges2:
 "distinct(vertices f) \<Longrightarrow> \<V>(f::face) = (\<Union>(a,b)\<in>\<E> f. {b})"
apply auto
apply(fast intro: prevVertex_in_edges)
done

lemma splitFace_face_face_op:
assumes mgp: "minGraphProps g" and pre: "pre_splitFace g u v f vs"
and fdg: "(f\<^sub>1,f\<^sub>2,g') = splitFace g u v f vs"
shows "face_face_op g'"
proof -
  have f12: "(f\<^sub>1, f\<^sub>2) = split_face f u v vs"
   and Fg': "\<F> g' = {f\<^sub>1} \<union> set(replace f [f\<^sub>2] (faces g))"
   and g': "g' = snd (snd (splitFace g u v f vs))" using fdg
    by(auto simp add:splitFace_def split_def)
  have f\<^sub>1: "f\<^sub>1= fst(split_face f u v vs)" and f\<^sub>2: "f\<^sub>2 = snd(split_face f u v vs)"
    using f12[symmetric] by simp_all
  note distF = minGraphProps11'[OF mgp]
  note pre_split = pre_splitFace_pre_split_face[OF pre]
  note distf\<^sub>1 = split_face_distinct1[OF f12 pre_split]
  note distf\<^sub>2 = split_face_distinct2[OF f12 pre_split]
  from pre have nf: "\<not> final f" and fg: "f \<in> \<F> g" and nuv: "u \<noteq> v"
    and uinf: "u \<in> \<V> f"and vinf: "v \<in> \<V> f"
    and distf: "distinct(vertices f)" and new: "\<V> g \<inter> set vs = {}"
    by(unfold pre_splitFace_def, simp)+
  let ?fuv = "between (vertices f) u v" and ?fvu = "between (vertices f) v u"
  have E\<^sub>1: "\<E> f\<^sub>1 = Edges (v # rev vs @ [u]) \<union> Edges (u # ?fuv @ [v])"
    using f\<^sub>1 by(simp add:edges_split_face1[OF pre_split])
  have E\<^sub>2: "\<E> f\<^sub>2 = Edges (u # vs @ [v]) \<union> Edges (v # ?fvu @ [u])"
    using f\<^sub>2 by(simp add:edges_split_face2[OF pre_split])
  have vf\<^sub>1: "vertices f\<^sub>1 = rev vs @ u # ?fuv @ [v]"
    using f\<^sub>1 by(simp add:split_face_def)
  have vf\<^sub>2: "vertices f\<^sub>2 = [v] @ ?fvu @ u # vs"
    using f\<^sub>2 by(simp add:split_face_def)
  have V\<^sub>1: "\<V> f\<^sub>1 = {u,v} \<union> set(?fuv) \<union> set(vs)" using vf\<^sub>1 by auto
  have V\<^sub>2: "\<V> f\<^sub>2 = {u,v} \<union> set(?fvu) \<union> set(vs)" using vf\<^sub>2 by auto
  have 2: "(v,u) \<in> \<E> f\<^sub>1 \<and> (u,v) \<in> \<E> f\<^sub>2 \<and> vs = [] \<or>
           (\<exists>v \<in> \<V> f\<^sub>1 \<inter> \<V> f\<^sub>2. v \<notin> \<V> g)"
    using E\<^sub>1 E\<^sub>2 V\<^sub>1 V\<^sub>2 new by(cases vs)(simp_all add:Edges_Cons)
  have "\<V> f\<^sub>1 \<noteq> \<V> f\<^sub>2"
  proof cases
    assume A: "?fvu = []"
    have "?fuv \<noteq> []"
    proof
      assume "?fuv = []"
      with A have "\<E> f = {(v,u),(u,v)}"
        using edges_conv_Un_Edges[OF distf uinf vinf nuv]
        by(simp add:Edges_Cons)
      hence "\<V> f = {u,v}" by(simp add:vertices_conv_Union_edges)
      hence "card(\<V> f) \<le> 2" by(simp add:card_insert_if)
      thus False
        using mgp_vertices3[OF mgp fg] by(simp add:distinct_card[OF distf])
    qed
    moreover have "set ?fuv \<inter> set vs = {}"
      using new minGraphProps9[OF mgp fg inbetween_inset] by blast
    moreover have "{u,v} \<inter> set ?fuv = {}"
      using between_not_r1[OF distf] between_not_r2[OF distf] by blast
    ultimately show ?thesis using V\<^sub>1 V\<^sub>2 A by (auto simp:neq_Nil_conv)
  next
    assume "?fvu \<noteq> []"
    moreover have "{u,v} \<inter> set ?fvu = {}"
      using between_not_r1[OF distf] between_not_r2[OF distf] by blast
    moreover have "set ?fuv \<inter> set ?fvu = {}"
      by(simp add:pre_between_def between_inter_empty distf uinf vinf nuv)
    moreover have "set ?fvu \<inter> set vs = {}"
      using new minGraphProps9[OF mgp fg inbetween_inset] by blast
    ultimately show ?thesis using V\<^sub>1 V\<^sub>2 by (auto simp:neq_Nil_conv)
  qed
  have C12: "\<E> f\<^sub>1 \<noteq> (\<E> f\<^sub>2)\<inverse>"
  proof
    assume A: "\<E> f\<^sub>1 = (\<E> f\<^sub>2)\<inverse>"
    show False
    proof -
      have "\<V> f\<^sub>1 = (\<Union>(a,b)\<in>\<E> f\<^sub>1. {a})"
        by(rule vertices_conv_Union_edges)
      also have "\<dots> = (\<Union>(b,a)\<in>\<E> f\<^sub>2. {a})" by(auto simp:A)
      also have "\<dots> = \<V> f\<^sub>2"
        by(rule vertices_conv_Union_edges2[OF distf\<^sub>2, symmetric])
      finally show False using \<open>\<V> f\<^sub>1 \<noteq> \<V> f\<^sub>2\<close> by blast
    qed
  qed
  { fix h :: face assume hg: "h \<in> \<F> g"
    have "\<E> h \<noteq> (\<E> f\<^sub>1)\<inverse> \<and> \<E> h \<noteq> (\<E> f\<^sub>2)\<inverse>" using 2
    proof
      assume "(v,u) \<in> \<E> f\<^sub>1 \<and> (u,v) \<in> \<E> f\<^sub>2 \<and> vs = []"
      moreover hence "(u,v) \<notin> \<E> g"
        using pre by(unfold pre_splitFace_def)simp
      moreover hence "(v,u) \<notin> \<E> g" by(blast intro:minGraphProps10[OF mgp])
      ultimately show ?thesis using hg by(simp add:edges_graph_def) blast
    next
      assume "\<exists>x \<in> \<V> f\<^sub>1 \<inter> \<V> f\<^sub>2. x \<notin> \<V> g"
      then obtain x where "x \<in> \<V> f\<^sub>1" and "x \<in> \<V> f\<^sub>2" and "x \<notin> \<V> g"
        by blast
      obtain y where "(x,y) \<in> \<E> f\<^sub>1" using \<open>x \<in> \<V> f\<^sub>1\<close>
        by(auto simp:vertices_conv_Union_edges)
      moreover obtain z where "(x,z) \<in> \<E> f\<^sub>2" using \<open>x \<in> \<V> f\<^sub>2\<close>
        by(auto simp:vertices_conv_Union_edges)
      moreover have "\<not>(\<exists>y. (y,x) \<in> \<E> h)"
        using \<open>x \<notin> \<V> g\<close> minGraphProps9[OF mgp hg]
        by(blast dest:in_edges_in_vertices)
      ultimately show ?thesis by blast
    qed
  }
  note Cg12 = this
  show ?thesis
  proof cases
    assume 2: "|faces g| = 2"
    with fg obtain f' where Fg: "\<F> g = {f,f'}"
      by(fastforce simp: eval_nat_numeral length_Suc_conv)
    moreover hence "f \<noteq> f'" using 2 distinct_card[OF distF] by auto
    ultimately have Fg': "\<F> g' = {f\<^sub>1,f\<^sub>2,f'}"
      using set_faces_splitFace[OF mgp fg pre fdg] by blast
    show ?thesis using Fg' C12 Cg12 Fg
      by(fastforce simp:face_face_op_def)
  next
    assume "|faces g| \<noteq> 2"
    hence E: "\<And>f f'. f\<in>\<F> g \<Longrightarrow> f'\<in>\<F> g \<Longrightarrow> f \<noteq> f' \<Longrightarrow> \<E> f \<noteq> (\<E> f')\<inverse>"
      using mgp by(simp add:minGraphProps_def face_face_op_def)
    thus ?thesis using set_faces_splitFace[OF mgp fg pre fdg] C12 Cg12
      by(fastforce simp:face_face_op_def)
  qed
qed

lemma splitFace_face_face_op2:
 "minGraphProps g \<Longrightarrow> pre_splitFace g u v f vs
 \<Longrightarrow> face_face_op(snd(snd(splitFace g u v f vs)))"
apply(subgoal_tac "pre_splitFace g u v f vs")
 prefer 2 apply(simp)
by(drule (1) splitFace_face_face_op[where f\<^sub>1 = "fst(splitFace g u v f vs)" and f\<^sub>2 = "fst(snd(splitFace g u v f vs))"], auto)

lemma splitFace_holds_minGraphProps:
  assumes precond: "pre_splitFace g' v a f' [countVertices g'..<countVertices g' + n]"
  and min: "minGraphProps g'"
  shows "minGraphProps (snd (snd (splitFace g' v a f' [countVertices g'..<countVertices g' + n])))"
proof -
  from min have "minGraphProps' g'" by (simp add: minGraphProps_def)
  then show ?thesis apply (simp add: minGraphProps_def) apply safe
    apply (rule splitFace_holds_minGraphProps') apply (rule precond) apply assumption
    apply (rule splitFace_holds_facesAt_eq) apply (rule precond) apply (rule min) apply simp
    apply (rule splitFace_holds_faceListAt_len) apply (rule precond) apply (rule min)
    apply (rule splitFace_holds_facesAt_distinct) apply (rule precond) apply (rule min)
    apply (rule splitFace_holds_faces_distinct) apply (rule precond) apply (rule min)
    apply (rule splitFace_holds_faces_subset) apply (rule precond) apply (rule min)
    apply (rule splitFace_holds_edges_sym) apply (rule precond) apply (rule min)
    apply (rule splitFace_edges_disj2) apply (rule min) apply (rule precond)
    apply (rule splitFace_face_face_op2) apply (rule min) apply (rule precond)
    done
qed


subsection\<open>Invariants of @{const makeFaceFinal}\<close>


lemma MakeFaceFinal_minGraphProps':
  "f \<in> \<F> g \<Longrightarrow> minGraphProps g \<Longrightarrow> minGraphProps' (makeFaceFinal f g)"
apply (simp add: minGraphProps_def minGraphProps'_def makeFaceFinal_def)
apply (subgoal_tac "2 < |vertices f| \<and> distinct (vertices f)")
 apply (rule ballI) apply (elim conjE ballE) apply (rule conjI) apply simp apply simp
  apply (simp add: makeFaceFinalFaceList_def) apply (drule replace5) apply (simp add: setFinal_def)
by force

lemma MakeFaceFinal_facesAt_eq:
  "f \<in> \<F> g \<Longrightarrow> minGraphProps g \<Longrightarrow> facesAt_eq (makeFaceFinal f g)"
apply (simp add: facesAt_eq_def) apply (rule ballI)
apply (subgoal_tac "v \<in> \<V> g")
 apply (rule equalityI)
  apply (rule subsetI)
  apply (simp add: makeFaceFinal_def facesAt_def)
  apply (subgoal_tac "v < | faceListAt g | ")
   apply (simp add: makeFaceFinalFaceList_def)
   apply (subgoal_tac "distinct ((faceListAt g ! v))")
    apply (subgoal_tac "distinct (faces g)")
     apply (simp add: replace6)
     apply (case_tac "x = f")
      apply simp apply (erule (1) minGraphProps6) apply (simp add: facesAt_def) apply blast
     apply simp
     apply (case_tac " f \<in> set (faceListAt g ! v) \<and> x = setFinal f") apply simp
      apply (subgoal_tac "v \<in> \<V> f") apply (simp add: setFinal_def)
      apply (erule (1) minGraphProps6) apply (simp add: facesAt_def)
     apply simp
     apply (rule conjI) apply (rule disjI2)
      apply (erule (1) minGraphProps5) apply (fastforce simp: facesAt_def)
     apply (erule (1) minGraphProps6) apply (fastforce simp: facesAt_def)
    apply (rule minGraphProps11') apply simp
   apply (rule normFaces_distinct) apply (rule minGraphProps8a) apply simp apply simp
  apply (simp add: vertices_graph minGraphProps4)
    (* backward *)

 apply (rule subsetI) apply (simp add: makeFaceFinal_def facesAt_def)
 apply (subgoal_tac "v < | faceListAt g | ") apply simp
  apply (subgoal_tac "distinct (faceListAt g ! v)")
   apply (subgoal_tac "distinct (faces g)")
    apply (simp add: makeFaceFinalFaceList_def replace6)
    apply (case_tac "x = setFinal f") apply simp
     apply (rule disjI1) apply (rule minGraphProps7') apply simp apply simp
    apply (simp add: setFinal_def) apply simp
   apply (rule minGraphProps7') apply simp apply simp apply simp
   apply (rule minGraphProps11') apply simp
  apply (rule normFaces_distinct) apply (rule minGraphProps8a) apply simp apply simp
 apply (simp add: vertices_graph minGraphProps4)
   (* Vorbed v in set (vertices g) *)
apply (simp add: makeFaceFinal_def) by (simp add: in_vertices_graph minGraphProps4)

lemma MakeFaceFinal_faceListAt_len:
 "f \<in> \<F> g \<Longrightarrow> minGraphProps g \<Longrightarrow> faceListAt_len (makeFaceFinal f g)"
  apply (simp add: faceListAt_len_def makeFaceFinal_def) apply (rule minGraphProps4) by simp

lemma normFaces_makeFaceFinalFaceList: "(normFaces (makeFaceFinalFaceList f fs)) = (normFaces fs)"
  apply (simp add: normFaces_def) apply (simp add: makeFaceFinalFaceList_def)
  apply (induct fs) apply simp apply simp apply (rule impI)
  by (simp add: setFinal_def normFace_def verticesFrom_def minVertex_def)

lemma MakeFaceFinal_facesAt_distinct:
 "f \<in> \<F> g \<Longrightarrow>  minGraphProps g \<Longrightarrow> facesAt_distinct (makeFaceFinal f g)"
  apply (simp add: facesAt_distinct_def makeFaceFinal_def)
  apply (clarsimp simp: facesAt_def)
  apply (subgoal_tac "v < | (faceListAt g) |") apply (simp add: normFaces_makeFaceFinalFaceList)
  apply (rule minGraphProps8a') apply simp apply simp by (simp add: minGraphProps4)

lemma MakeFaceFinal_faces_subset:
 "f \<in> \<F> g \<Longrightarrow>  minGraphProps g \<Longrightarrow> faces_subset (makeFaceFinal f g)"
  apply (simp add: faces_subset_def) apply (intro ballI subsetI)
  apply (simp add: makeFaceFinal_def makeFaceFinalFaceList_def)
  apply (drule replace5)
  apply (case_tac "fa \<in> \<F> g") apply simp apply (rule minGraphProps9')
    apply simp apply (thin_tac "f \<in> \<F> g") apply simp+
  apply (rule minGraphProps9') apply simp apply simp by (simp add: setFinal_def)

lemma MakeFaceFinal_edges_sym:
 "f \<in> \<F> g \<Longrightarrow>  minGraphProps g \<Longrightarrow> edges_sym (makeFaceFinal f g)"
  apply (simp add: edges_sym_def) apply (intro allI impI)
  apply (simp add: makeFaceFinal_def edges_graph_def)
  apply (elim bexE) apply (simp add: makeFaceFinalFaceList_def)
  apply (subgoal_tac "distinct (faces g)")
  apply (case_tac "x \<in> \<F> g")
    apply (subgoal_tac "(a,b) \<in> edges g") apply (frule minGraphProps10) apply assumption
    apply (simp add: edges_graph_def) apply (elim bexE)
    apply (case_tac "xb = f")
      apply (subgoal_tac "(b,a) \<in> edges (setFinal f)")
        apply (rule bexI) apply (rotate_tac -1)  apply assumption
        apply (rule replace3) apply simp apply simp
      apply (subgoal_tac "distinct (vertices f)")
      apply (simp add: edges_setFinal)
      apply (rule minGraphProps3) apply simp apply simp
    apply (rule bexI) apply assumption apply (rule replace4) apply simp apply force
    apply (simp add: edges_graph_def) apply force
  apply (frule replace5) apply simp
  apply (subgoal_tac "(a,b) \<in> edges g")
  apply (frule minGraphProps10) apply assumption apply (simp add: edges_graph_def) apply (elim bexE)
    apply (case_tac "xb = f")
      apply (subgoal_tac "(b, a) \<in> edges (setFinal f)")
        apply (rule bexI) apply (rotate_tac -1) apply assumption
        apply (rule replace3) apply simp apply simp
      apply (subgoal_tac "distinct (vertices f)")
      apply (simp add: edges_setFinal)
      apply (rule minGraphProps3) apply simp apply simp
    apply  (rule bexI) apply simp apply (rule replace4) apply simp apply force
  apply (subgoal_tac "distinct (vertices f)")
  apply (subgoal_tac "(a,b) \<in> edges f")
  apply (simp add: edges_graph_def)   apply force
  apply (simp add: edges_setFinal)
  apply (rule minGraphProps3) apply simp apply simp
  by (rule minGraphProps11')

lemma MakeFaceFinal_faces_distinct:
 "f \<in> \<F> g \<Longrightarrow>  minGraphProps g \<Longrightarrow> faces_distinct (makeFaceFinal f g)"
  apply (simp add: faces_distinct_def makeFaceFinal_def normFaces_makeFaceFinalFaceList)
  by (rule minGraphProps11)

lemma MakeFaceFinal_edges_disj:
 "f \<in> \<F> g \<Longrightarrow>  minGraphProps g \<Longrightarrow> edges_disj (makeFaceFinal f g)"
apply(frule minGraphProps11')
apply (clarsimp simp: edges_disj_def makeFaceFinal_def edges_graph_def
                      makeFaceFinalFaceList_def replace6)
apply(case_tac "f = f'")
 apply (fastforce dest:mgp_edges_disj)
apply (fastforce dest:mgp_edges_disj)
done


lemma MakeFaceFinal_face_face_op:
 "f \<in> \<F> g \<Longrightarrow> minGraphProps g \<Longrightarrow> face_face_op (makeFaceFinal f g)"
apply(subgoal_tac "face_face_op g")
 prefer 2 apply(simp add:minGraphProps_def)
apply(drule minGraphProps11')
apply(auto simp: face_face_op_def makeFaceFinal_def makeFaceFinalFaceList_def
                 distinct_set_replace)
done


lemma MakeFaceFinal_minGraphProps:
 "f \<in> \<F> g \<Longrightarrow> minGraphProps g \<Longrightarrow> minGraphProps (makeFaceFinal f g)"
apply (simp (no_asm) add: minGraphProps_def)
apply (simp add: MakeFaceFinal_minGraphProps' MakeFaceFinal_facesAt_eq
    MakeFaceFinal_faceListAt_len MakeFaceFinal_facesAt_distinct
    MakeFaceFinal_faces_subset MakeFaceFinal_edges_sym
    MakeFaceFinal_edges_disj MakeFaceFinal_faces_distinct
    MakeFaceFinal_face_face_op)
done


subsection\<open>Invariants of @{const subdivFace'}\<close>

lemma subdivFace'_holds_minGraphProps: "\<And> f v' v n g.
  pre_subdivFace' g f v' v n ovl \<Longrightarrow> f \<in> \<F> g \<Longrightarrow>
  minGraphProps g \<Longrightarrow> minGraphProps (subdivFace' g f v n ovl)"
proof (induct ovl)
  case Nil then show ?case by (simp add: MakeFaceFinal_minGraphProps)
next
  case (Cons ov ovl) then show ?case
apply auto
apply (cases "ov")
 apply (simp_all split: if_split_asm)
 apply (rule Cons)
   apply (rule pre_subdivFace'_None)
   apply simp_all
apply (intro conjI)
 apply clarsimp
 apply (rule Cons)
   apply (rule pre_subdivFace'_Some2)
   apply simp_all
apply (clarsimp simp: split_def)
apply (rule Cons)
  apply (rule pre_subdivFace'_Some1)
       apply simp_all
  apply (simp add: minGraphProps_def faces_subset_def)
 apply (rule splitFace_add_f21')
 apply simp_all
apply (rule splitFace_holds_minGraphProps)
 apply simp_all
apply (rule pre_subdivFace'_preFaceDiv)
   apply simp_all
by (simp add: minGraphProps_def faces_subset_def)
qed


(* Invariance of one_final *)

abbreviation (input)
  Edges_if :: "face \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> (vertex \<times> vertex)set" where
  "Edges_if f u v ==
    if u=v then {} else Edges(u # between (vertices f) u v @ [v])"

lemma FaceDivsionGraph_one_final_but:
assumes mgp: "minGraphProps g" and pre: "pre_splitFace g u v f vs"
and fdg: "(f\<^sub>1,f\<^sub>2,g') = splitFace g u v f vs"
and nrv: "r \<noteq> v"
and ruv: "before (verticesFrom f r) u v" and rf: "r \<in> \<V> f"
and 1: "one_final_but g (Edges_if f r u)"
shows "one_final_but g' (Edges(r # between (vertices f\<^sub>2) r v @ [v]))"
proof -
  have f\<^sub>1: "f\<^sub>1= fst(split_face f u v vs)" and f\<^sub>2: "f\<^sub>2 = snd(split_face f u v vs)"
   and F: "\<F> g' = {f\<^sub>1} \<union> set(replace f [f\<^sub>2] (faces g))"
   and g': "g' = snd (snd (splitFace g u v f vs))" using fdg
    by(auto simp add:splitFace_def split_def)
  note pre_split = pre_splitFace_pre_split_face[OF pre]
  from pre have nf: "\<not> final f" and fg: "f \<in> \<F> g" and nuv: "u \<noteq> v"
    and uinf: "u \<in> \<V> f"and vinf: "v \<in> \<V> f"
    by(unfold pre_splitFace_def, simp)+
  from mgp fg have distf: "distinct(vertices f)" by(rule minGraphProps3)
  note distFg = minGraphProps11'[OF mgp]
  have fvu: "r\<noteq>u \<Longrightarrow> between (vertices f) v u =
                     between (vertices f) v r @ r # between (vertices f) r u"
    using before_between2[OF ruv distf rf] nrv
      split_between[OF distf vinf uinf, of r] by (auto)
  let ?fuv = "between (vertices f) u v" and ?fvu = "between (vertices f) v u"
  let ?fru = "between (vertices f) r u" and ?f\<^sub>2rv = "between (vertices f\<^sub>2) r v"
  have E\<^sub>1: "\<E> f\<^sub>1 = Edges (v # rev vs @ [u]) \<union> Edges (u # ?fuv @ [v])"
    using f\<^sub>1 by(simp add:edges_split_face1[OF pre_split])
  have E\<^sub>2: "\<E> f\<^sub>2 = Edges (u # vs @ [v]) \<union> Edges (v # ?fvu @ [u])"
    using f\<^sub>2 by(simp add:edges_split_face2[OF pre_split])
  have vf\<^sub>2: "vertices f\<^sub>2 = [v] @ ?fvu @ u # vs"
    using f\<^sub>2 by(simp add:split_face_def)
  have vinf\<^sub>2: "v \<in> \<V> f\<^sub>2" using vf\<^sub>2 by(simp)
  have rinf\<^sub>2: "r \<in> \<V> f\<^sub>2"
  proof cases
    assume "r=u" thus ?thesis by(simp add:vf\<^sub>2)
  next
    assume "r\<noteq>u" thus ?thesis by(simp add: vf\<^sub>2 fvu)
  qed
  have distf\<^sub>2: "distinct(vertices f\<^sub>2)"
    by(simp add:f\<^sub>2)(rule split_face_distinct2'[OF pre_split])
  have f\<^sub>2uv: "between (vertices f\<^sub>2) u v = vs"
    using vf\<^sub>2 distf\<^sub>2 by(simp add:between_def split_def)
  have f\<^sub>2ru: "r\<noteq>u \<Longrightarrow> between (vertices f\<^sub>2) r u = between (vertices f) r u"
    using vf\<^sub>2 fvu distf distf\<^sub>2 by(simp add:between_def split_def)
  hence f\<^sub>2rv: "between (vertices f\<^sub>2) r v =
              (if r=u then [] else ?fru @ [u]) @ vs"
  proof cases
    assume "r=u" thus ?thesis by(simp add: f\<^sub>2uv)
  next
    assume nru: "r \<noteq> u"
    have vinf\<^sub>2: "v \<in> \<V> f\<^sub>2" by(simp add: vf\<^sub>2)
    note u_bet_rv = before_between[OF ruv distf rf nru]
    have u_bet_rv\<^sub>2: "u \<in> set (between (vertices f\<^sub>2) r v)"
      using distf\<^sub>2 nru
      apply(simp add:vf\<^sub>2 fvu)
      apply(subst between_def[of _ r v])
      apply(simp add:split_def)
      done
    show ?thesis
      by(simp add:split_between[OF distf\<^sub>2 rinf\<^sub>2 vinf\<^sub>2 u_bet_rv\<^sub>2] f\<^sub>2ru f\<^sub>2uv)
  qed
  have E\<^sub>2rv: "Edges(r # ?f\<^sub>2rv @ [v]) =
         Edges_if f r u \<union> Edges(u # vs @ [v])" (is "?L = ?R")
  proof -
    have "?L = Edges((if r=u then [] else r # ?fru) @ (u # vs @ [v]))"
      by (simp add: f\<^sub>2rv)
    also have "\<dots> = ?R" by(auto simp:Edges_Cons Edges_append)
    finally show ?thesis .
  qed
  show ?thesis
  proof (auto del: disjCI simp:one_final_but_def F, goal_cases)
    case prems: (1 a b)
    have ab: "(a,b) \<in> \<E> f\<^sub>1"
      and nab: "(a,b) \<notin> Edges (r # ?f\<^sub>2rv @ [v])" by fact+
    have "(a,b) \<in> Edges (v # rev vs @ [u]) \<or>
          (a,b) \<in> Edges (u # ?fuv @ [v])" (is "?A \<or> ?B")
      using E\<^sub>1 ab by blast
    thus ?case
    proof
      assume ?A
      hence "(b,a) \<in> Edges (rev(v # rev vs @ [u]))" by (simp del:rev.simps)
      hence "(b,a) \<in> Edges (r # ?f\<^sub>2rv @ [v])" using E\<^sub>2rv by simp
      thus ?case by blast
    next
      assume abfuv: ?B
      have abf: "(a,b) \<in> \<E> f"
        by(rule Edges_between_edges[OF abfuv pre_split])
      have "(\<exists>f'\<in>set(replace f [f\<^sub>2] (faces g)). final f' \<and> (b,a) \<in> \<E> f')"
      proof cases
        assume "r = u"
        then obtain f' where "f' \<in> \<F> g \<and> final f' \<and> (b, a) \<in> \<E> f'"
          using abf 1 nf fg by(simp add:one_final_but_def)fast
        moreover then have "f' \<in> set (replace f [f\<^sub>2] (faces g))"
          by(clarsimp simp: replace6[OF distFg] nf)
        ultimately show ?thesis by blast
      next
        assume nru: "r \<noteq> u"
        moreover hence "(a,b) \<notin> Edges (r # ?fru @ [u])"
          using abfuv Edges_disj[OF distf rf vinf nru nuv
                        before_between[OF ruv distf rf nru]] by fast
        moreover have "(b,a) \<notin> Edges (r # ?fru @ [u])"
        proof
          assume "(b,a) \<in> Edges (r # ?fru @ [u])"
          moreover have "pre_split_face f r u []"
            by(simp add:pre_split_face_def distf rf uinf nru)
          ultimately show False
            using minGraphProps12[OF mgp fg abf]
            by(blast dest:Edges_between_edges)
        qed
        ultimately obtain f' where "f' \<in> \<F> g \<and> final f' \<and> (b, a) \<in> \<E> f'"
          using abf 1 nf fg by(simp add:one_final_but_def)fast
        moreover hence "f' \<in> set (replace f [f\<^sub>2] (faces g))"
          by(clarsimp simp: replace6[OF distFg] nf)
        ultimately show ?thesis by blast
      qed
      thus ?case ..
    qed
  next
    case (2 f' a b)
    have f': "f' \<in> set (replace f [f\<^sub>2] (faces g))"
      and nf': "\<not> final f'" and abf': "(a,b) \<in> \<E> f'"
      and nab: "(a,b) \<notin> Edges (r # between (vertices f\<^sub>2) r v @ [v])" by fact+
    have "f' = f\<^sub>2 \<or> f' \<in> \<F> g \<and> f' \<noteq> f"
      using f' by(simp add:replace6[OF distFg]) blast
    hence "(b, a) \<in> Edges (r # between (vertices f\<^sub>2) r v @ [v]) \<or>
      (\<exists>f'\<in>set (replace f [f\<^sub>2] (faces g)). final f' \<and> (b, a) \<in> \<E> f')"
      (is "?A \<or> ?B")
    proof
      assume [simp]: "f' = f\<^sub>2"
      have "(a,b) \<in> Edges (v # between (vertices f\<^sub>2) v r @ [r])"
        using abf' nab Edges_compl[OF distf\<^sub>2 vinf\<^sub>2 rinf\<^sub>2 nrv[symmetric]]
        edges_conv_Un_Edges[OF distf\<^sub>2 rinf\<^sub>2 vinf\<^sub>2 nrv] by auto
      moreover have eq: "between(vertices f\<^sub>2) v r = between (vertices f) v r"
      proof (cases "r=u")
        assume "r=u" thus ?thesis
          by(simp add:vf\<^sub>2)(rule between_front[OF between_not_r2[OF distf]])
      next
        assume "r\<noteq>u" thus ?thesis
          by(simp add:vf\<^sub>2 fvu)(rule between_front[OF between_not_r2[OF distf]])
      qed
      ultimately
      have abfvr: "(a,b) \<in> Edges (v # between (vertices f) v r @ [r])"
        by simp
      have abf: "(a,b) \<in> \<E> f"
        apply(rule Edges_between_edges[where vs = "[]", OF abfvr])
        using distf rf vinf nrv by(simp add:pre_split_face_def)
      have "(\<exists>f'\<in>set(replace f [f\<^sub>2] (faces g)). final f' \<and> (b,a) \<in> \<E> f')"
      proof cases
        assume "r = u"
        then obtain f' where "f' \<in> \<F> g \<and> final f' \<and> (b, a) \<in> \<E> f'"
          using abf 1 nf fg by(simp add:one_final_but_def)fast
        moreover then have "f' \<in> set (replace f [f\<^sub>2] (faces g))"
          by(clarsimp simp: replace6[OF distFg] nf)
        ultimately show ?thesis by blast
      next
        assume nru: "r \<noteq> u"
        note uvr = rotate_before_vFrom[OF distf rf nru ruv]
        note bet = before_between[OF uvr distf vinf  nrv[symmetric]]
        have "(a,b) \<notin> Edges (r # ?fru @ [u])"
          using abfvr Edges_disj[OF distf vinf uinf nrv[symmetric] nru bet]
          by fast
        moreover have "(b,a) \<notin> Edges (r # ?fru @ [u])"
        proof
          assume "(b,a) \<in> Edges (r # ?fru @ [u])"
          moreover have "pre_split_face f r u []"
            by(simp add:pre_split_face_def distf rf uinf nru)
          ultimately show False
            using minGraphProps12[OF mgp fg abf]
            by(blast dest:Edges_between_edges)
        qed
        ultimately obtain f' where "f' \<in> \<F> g \<and> final f' \<and> (b, a) \<in> \<E> f'"
          using abf 1 nf fg nru by(simp add:one_final_but_def)fast
        moreover hence "f' \<in> set (replace f [f\<^sub>2] (faces g))"
          by(clarsimp simp: replace6[OF distFg] nf)
        ultimately show ?thesis by blast
      qed
      thus ?thesis ..
    next
      assume  f': "f' \<in> \<F> g \<and> f' \<noteq> f"
      moreover
      hence "\<E> f' \<inter> \<E> f = {}"
        using fg by(blast dest: mgp_edges_disj[OF mgp])
      moreover
      have "Edges_if f r u \<subseteq> \<E> f"
        using distf rf uinf
        apply(clarsimp simp del:is_nextElem_edges_eq)
        apply(erule Edges_between_edges[where vs = "[]"])
        by(simp add:pre_split_face_def)
      ultimately
      have "(b,a) : Edges_if f r u \<or>
            (\<exists>f''\<in>\<F> g. final f'' \<and> (b,a) \<in> \<E> f'')" (is "?A \<or> ?B")
        using 1 f' nf' abf'
        by(simp add:one_final_but_def split:if_split_asm) blast+
      thus ?thesis (is "?A' \<or> ?B'")
      proof
        assume ?A
        moreover
        have "Edges_if f r u \<subseteq> Edges (r # between (vertices f\<^sub>2) r v @ [v])"
          using f\<^sub>2rv by (auto simp:Edges_Cons Edges_append)
        ultimately have ?A' by blast
        thus ?thesis ..
      next
        assume ?B
        then obtain f'' where "f''\<in>\<F> g \<and> final f'' \<and> (b, a) \<in> \<E> f''"
          by blast
        moreover hence "f'' \<noteq> f" using nf by blast
        ultimately have ?B' by (blast intro:in_set_repl)
        thus ?thesis ..
      qed
    qed
    thus ?case by blast
  qed
qed


lemma one_final_but_makeFaceFinal:
 "\<lbrakk> minGraphProps g; one_final_but g E; E \<subseteq> \<E> f; f \<in> \<F> g; \<not> final f \<rbrakk> \<Longrightarrow>
  one_final (makeFaceFinal f g)"
apply(frule minGraphProps11')
apply(clarsimp simp add:one_final_but_def one_final_def makeFaceFinal_def
         makeFaceFinalFaceList_def replace6)
apply(rename_tac f' a b)
apply(erule disjE)
 apply(simp)
apply(subgoal_tac "(a,b) \<notin> E")
 prefer 2 apply (simp add:minGraphProps_def edges_disj_def) apply blast
apply(drule_tac x = f' in bspec)
 apply assumption
apply simp
apply(drule_tac x = "(a,b)" in bspec)
 apply simp
apply(fastforce simp add: replace6)
done


lemma one_final_subdivFace':
  "\<And>f v n g.
  pre_subdivFace' g f u v n ovs \<Longrightarrow> minGraphProps g \<Longrightarrow> f \<in> \<F> g \<Longrightarrow>
  one_final_but g (Edges_if f u v) \<Longrightarrow>
  one_final(subdivFace' g f v n ovs)"
proof (induct ovs)
  case Nil
  hence "pre_split_face f u v []"
    by(simp add:pre_split_face_def pre_subdivFace'_def)
  hence "Edges(u # between (vertices f) u v @ [v]) \<subseteq> \<E> f"
    by(auto simp add:Edges_between_edges)
  moreover have "\<not> final f" using Nil by(simp add:pre_subdivFace'_def)
  ultimately show ?case using Nil by (simp add: one_final_but_makeFaceFinal)
next
  case (Cons ov ovs)
  note IH = Cons(1) and pre = Cons(2) and mgp = Cons(3) and fg = Cons(4)
  note 1 = Cons(5)
  have nf: "\<not> final f" and uf: "u \<in> \<V> f" and vf: "v \<in> \<V> f"
    using pre by(simp add:pre_subdivFace'_def)+
  show ?case
  proof (cases ov)
    case None
    have pre': "pre_subdivFace' g f u v (Suc n) ovs"
      using None pre by (simp add: pre_subdivFace'_None)
    show ?thesis using None
      by (simp add: IH[OF pre' mgp fg 1])
  next
    case (Some w)
    have uw: "u \<noteq> w" using pre Some by(clarsimp simp: pre_subdivFace'_def)
    { assume w: "f \<bullet> v = w" and n: "n = 0"
      from w minGraphProps3[OF mgp fg]
      have vw: "nextElem (vertices f) (hd(vertices f)) v =  w"
        by(simp add:nextVertex_def)
      have 2: "one_final_but g (if u=w then {} else Edges (u # between (vertices f) u w @ [w]))"
          apply (rule one_final_but_antimono[OF 1])
          using uw apply clarsimp
          apply(subgoal_tac "pre_between (vertices f) u v")
           prefer 2
           using pre vf apply(simp add:pre_subdivFace'_def pre_between_def)
          apply(simp add:between_nextElem vw[symmetric])
          apply(fastforce simp add:Edges_Cons Edges_append)
          done
      have pre': "pre_subdivFace' g f u w 0 ovs"
        using pre Some n using [[simp_depth_limit = 5]] by (simp add: pre_subdivFace'_Some2)
      have "one_final (subdivFace' g f w 0 ovs)"
        by (simp add: IH[OF pre' mgp fg 2])
    } moreover
    { let ?vs = "[countVertices g..<countVertices g + n]"
      let ?fdg = "splitFace g v w f ?vs"
      let ?Ew = "if u=w then {} else Edges(u # between(vertices (fst(snd ?fdg))) u w @ [w])"
      assume a: "f \<bullet> v = w \<longrightarrow> 0 < n"
      have pre2: "pre_subdivFace' g f u v n (Some w # ovs)"
        using pre Some by simp
      have fsubg: "\<V> f \<subseteq> \<V> g"
        using mgp fg by(simp add: minGraphProps_def faces_subset_def)
      have pre_fdg: "pre_splitFace g v w f ?vs"
           apply (rule pre_subdivFace'_preFaceDiv[OF _ fg _ fsubg])
            using Some pre apply simp
           using a apply (simp)
           done
      have bet: "before (verticesFrom f u) v w" using pre Some
        by(unfold pre_subdivFace'_def) simp
      have 2: "one_final_but(snd(snd ?fdg)) ?Ew"
        using uw apply simp
        apply(rule FaceDivsionGraph_one_final_but[OF mgp pre_fdg _ uw bet uf 1])
        apply(fastforce intro!:prod_eqI)
        done
      note mgp' = splitFace_holds_minGraphProps[OF pre_fdg mgp]
      have pre2': "pre_subdivFace' (snd (snd ?fdg)) (fst (snd ?fdg)) u w 0 ovs"
        by (rule pre_subdivFace'_Some1[OF pre2 fg _ fsubg HOL.refl HOL.refl])
           (simp add:a)
      note f2inF = splitFace_add_f21'[OF fg]
      have "one_final (subdivFace' (snd (snd ?fdg)) (fst (snd ?fdg)) w 0 ovs)"
        by (simp add: IH[OF pre2' mgp' f2inF 2])
    } ultimately show ?thesis using Some by (simp add: split_def)
  qed
qed


lemma neighbors_edges:
 "minGraphProps g \<Longrightarrow> a : \<V> g \<Longrightarrow> b \<in> set (neighbors g a) = ((a, b) \<in> edges g)"
apply (rule iffI)
 apply (simp add: neighbors_def) apply clarify apply (frule (1) minGraphProps5)
  apply (simp add: vertices_graph)
 apply (simp add: edges_graph_def) apply (intro bexI)
  prefer 2 apply assumption
 apply(simp add:edges_face_eq)
 apply (erule (2) minGraphProps6)
apply (simp add: neighbors_def) apply (simp add: edges_graph_def) apply (elim bexE)
apply (subgoal_tac "x \<in> set (facesAt g a)") apply (simp add: edges_face_def)
apply (rule minGraphProps7) apply simp+ apply (simp add: edges_face_def)
done


lemma no_self_edges: "minGraphProps' g \<Longrightarrow> (a, a) \<notin> edges g" apply (simp add: minGraphProps'_def)
apply (induct g) apply simp apply (simp add: edges_graph_def) apply auto apply (drule bspec) apply assumption
apply auto apply (simp add: is_nextElem_def) apply safe apply (simp add: is_sublist_def) apply force
apply (case_tac "vertices x") apply simp apply (case_tac "list" rule: rev_exhaust) apply simp by simp

text\<open>Requires only @{prop"distinct(vertices f)"} and that \<open>g\<close>
has no self-loops.\<close>

lemma duplicateEdge_is_duplicateEdge_eq:
"minGraphProps g \<Longrightarrow> f \<in> \<F> g \<Longrightarrow> a \<in> \<V> f \<Longrightarrow> b \<in> \<V> f \<Longrightarrow>
 duplicateEdge g f a b = is_duplicateEdge g f a b"
apply (subgoal_tac "distinct (vertices f)")
 prefer 2 apply (simp add: minGraphProps3)
apply(subgoal_tac "a : \<V> g")
 prefer 2 apply (simp add: minGraphProps9)
apply (simp add: duplicateEdge_def is_duplicateEdge_def neighbors_edges)
apply (rule iffI)
 apply (simp add: minGraphProps10)
 apply (cases "a = b") apply (simp add: no_self_edges minGraphProps_def)
 apply (rule ccontr)
 apply (simp add: directedLength_def)
 apply (case_tac "is_nextElem (vertices f) a b")
  apply (simp add: is_nextElem_between_empty)
 apply (simp add: is_nextElem_between_empty)
apply (cases "a = b") apply (simp add: no_self_edges minGraphProps_def)
apply (rule ccontr)
apply (simp add: directedLength_def)
apply (elim impE)
  apply (cases "between (vertices f) b a")
   apply (simp add: is_nextElem_between_empty' del:is_nextElem_between_empty)
  apply simp
 apply (cases "between (vertices f) a b")
  apply (simp add: is_nextElem_between_empty' del:is_nextElem_between_empty)
 apply simp
apply (simp add: minGraphProps10)
done

lemma incrIndexList_less_eq:
 "incrIndexList ls m nmax \<Longrightarrow> Suc n < |ls| \<Longrightarrow> ls!n \<le> ls!Suc n"
apply (subgoal_tac "increasing ls") apply (thin_tac "incrIndexList ls m nmax") apply (rule increasing1) apply simp
apply (subgoal_tac "ls = take n ls @ ls!n # [] @ ls!(Suc n) # drop (Suc (Suc n)) ls") apply assumption
apply simp apply (subgoal_tac "n < | ls|") apply (rotate_tac -1) apply (drule id_take_nth_drop)
apply (subgoal_tac "drop (Suc n) ls = ls ! Suc n # drop (Suc (Suc n)) ls") apply simp apply (drule Cons_nth_drop_Suc)
by auto

lemma incrIndexList_less:
 "incrIndexList ls m nmax \<Longrightarrow> Suc n < |ls| \<Longrightarrow> ls!n \<noteq> ls!Suc n\<Longrightarrow> ls!n < ls!Suc n"
apply (drule  incrIndexList_less_eq) by auto

lemma Seed_holds_minGraphProps': "minGraphProps' (Seed p)"
by (simp  add: graph_def Seed_def minGraphProps'_def)

lemma Seed_holds_facesAt_eq: "facesAt_eq (Seed p)"
by (force simp  add: graph_def Seed_def facesAt_eq_def facesAt_def)

lemma minVertex_zero1: "minVertex (Face [0..<Suc z] Final) = 0"
  apply (induct z) apply (simp add: minVertex_def)
  by (simp add: minVertex_def upt_conv_Cons del: upt_Suc)

lemma minVertex_zero2: "minVertex (Face (rev [0..<Suc z]) Nonfinal) = 0"
  apply (induct z) apply (simp add: minVertex_def)
  by (simp add: minVertex_def min_def)


subsection\<open>Invariants of @{const Seed}\<close>

lemma Seed_holds_facesAt_distinct: "facesAt_distinct (Seed p)"
apply(simp add: Seed_def graph_def
                facesAt_distinct_def normFaces_def facesAt_def normFace_def)
apply(simp add: eval_nat_numeral minVertex_zero1 minVertex_zero2 verticesFrom_Def
   fst_splitAt_upt snd_splitAt_upt fst_splitAt_rev snd_splitAt_rev del:upt_Suc)
apply(simp add:upt_conv_Cons del:upt_Suc)
apply simp
done

lemma Seed_holds_faces_subset: "faces_subset (Seed p)"
by (simp add: Seed_def graph_def faces_subset_def)

lemma Seed_holds_edges_sym: "edges_sym (Seed p)"
by (simp add: Seed_def graph_def edges_sym_def edges_graph_def)


lemma Seed_holds_edges_disj: "edges_disj (Seed p)"
using is_nextElem_circ[of "[0..<(p+3)]"]
by (fastforce simp add: Seed_def graph_def edges_disj_def edges_graph_def)


lemma Seed_holds_faces_distinct: "faces_distinct (Seed p)"
apply(simp add: Seed_def graph_def
                faces_distinct_def normFaces_def facesAt_def normFace_def)
apply(simp add: eval_nat_numeral minVertex_zero1 minVertex_zero2 verticesFrom_Def
   fst_splitAt_upt snd_splitAt_upt fst_splitAt_rev snd_splitAt_rev del:upt_Suc)
apply(simp add:upt_conv_Cons del:upt_Suc)
apply simp
done

lemma Seed_holds_faceListAt_len: "faceListAt_len (Seed p)"
by (simp add: Seed_def graph_def faceListAt_len_def)

lemma face_face_op_Seed: "face_face_op(Seed p)"
by (simp add: Seed_def graph_def face_face_op_def)

lemma one_final_Seed: "one_final Seed\<^bsub>p\<^esub>"
by(clarsimp simp:Seed_def one_final_def one_final_but_def graph_def)

lemma two_face_Seed: "|faces Seed\<^bsub>p\<^esub>| \<ge> 2"
by(simp add:Seed_def graph_def)

lemma inv_Seed: "inv (Seed p)"
  by (simp add: inv_def minGraphProps_def Seed_holds_minGraphProps'
    Seed_holds_facesAt_eq Seed_holds_facesAt_distinct Seed_holds_faces_subset
    Seed_holds_edges_sym Seed_holds_edges_disj face_face_op_Seed
    Seed_holds_faces_distinct Seed_holds_faceListAt_len
    one_final_Seed two_face_Seed)


lemma pre_subdivFace_indexToVertexList:
assumes mgp: "minGraphProps g" and f: "f \<in> set (nonFinals g)"
  and v: "v \<in> \<V> f" and e: "e \<in> set (enumerator i |vertices f| )"
  and containsNot: "\<not> containsDuplicateEdge g f v e" and i: "2 < i"
shows "pre_subdivFace g f v (indexToVertexList f v e)"
proof -
  from e i have le: "|e| = i" by (auto intro: enumerator_length2)
  from f have fg: "f \<in> \<F> g" "\<not> final f" by (auto simp: nonFinals_def)
  with mgp have le_vf: "2 < |vertices f|"
    by (simp add: minGraphProps_def minGraphProps'_def)
  from fg mgp have dist_f:"distinct (vertices f)"
    by (simp add: minGraphProps_def minGraphProps'_def)
  with le v i e le_vf fg have "pre_subdivFace_face f v (indexToVertexList f v e)"
    by (rule_tac indexToVertexList_pre_subdivFace_face) simp_all
  moreover
  from dist_f v e le_vf have "indexToVertexList f v e = natToVertexList v f e"
    apply (rule_tac indexToVertexList_natToVertexList_eq)
        apply simp
       apply simp
      prefer 2 apply (simp add: enumerator_not_empty)
     by (auto simp:set_enumerator_simps intro:enumerator_bound)
  moreover
  from e le_vf le i have "incrIndexList e i |vertices f|" by simp
  moreover note mgp containsNot i dist_f v le
  ultimately show ?thesis
    apply (simp add: pre_subdivFace_def)
    apply (simp add: invalidVertexList_def)
    apply (simp add: containsDuplicateEdge_eq containsDuplicateEdge'_def)
    apply (rule allI) apply(rename_tac j) apply (rule impI)
    apply (case_tac "natToVertexList v f e ! j") apply simp
    apply simp
    apply (case_tac "natToVertexList v f e ! Suc j") apply simp
    apply simp
    apply (case_tac "j") apply (simp add: natToVertexList_nth_0 natToVertexList_nth_Suc split: if_split_asm)
     apply (drule_tac spec) apply (rotate_tac -1) apply (erule impE)
      apply (subgoal_tac "e ! 0 < e ! Suc 0") apply assumption
      apply (cases "e") apply simp
      apply simp
      apply (drule incrIndexList_help21)
      apply simp
     apply (subgoal_tac "f\<^bsup>e ! 0\<^esup> \<bullet> v \<in> \<V> f")
      apply (subgoal_tac "f\<^bsup>e ! Suc 0\<^esup> \<bullet> v \<in> \<V> f")
       apply (simp add: duplicateEdge_is_duplicateEdge_eq [symmetric] fg)
       apply (rule ccontr)
       apply simp
       apply (cases e) apply simp
       apply simp
       apply (drule incrIndexList_help21) apply clarify apply (drule not_sym) apply (rotate_tac -2) apply simp
      apply (rule nextVertices_in_face) apply simp
     apply (rule nextVertices_in_face) apply simp
    apply simp
    apply (subgoal_tac "natToVertexList v f e ! Suc nat =
        (if e ! nat = e ! Suc nat then None else Some (f\<^bsup>e ! Suc nat\<^esup> \<bullet> v))")
     apply (simp split: if_split_asm)
     apply (subgoal_tac "natToVertexList v f e ! Suc (Suc nat) =
        (if e ! (Suc nat) = e ! Suc (Suc nat) then None else Some (f\<^bsup>e ! Suc (Suc nat)\<^esup> \<bullet> v))")
      apply (simp split: if_split_asm)
      apply (drule spec) apply (rotate_tac -1)  apply (erule impE)
       apply (subgoal_tac "e ! nat < e ! Suc nat") apply assumption
       apply (rule incrIndexList_less) apply assumption apply arith
       apply simp
      apply simp
      apply (subgoal_tac "f\<^bsup>e ! Suc nat\<^esup> \<bullet> v \<in> \<V> f")
       apply (subgoal_tac "f\<^bsup>e ! Suc (Suc nat)\<^esup> \<bullet> v \<in> \<V> f")
        apply (simp add: duplicateEdge_is_duplicateEdge_eq [symmetric] fg)
        apply (rule ccontr) apply simp
        apply (rotate_tac -4) apply (erule impE) apply arith
        apply (subgoal_tac "e ! Suc nat < e ! Suc (Suc nat)") apply force
        apply (rule incrIndexList_less) apply assumption apply arith
        apply simp
       apply (rule nextVertices_in_face) apply simp
      apply (rule nextVertices_in_face) apply simp
     apply (rule natToVertexList_nth_Suc) apply simp apply arith
    apply (rule natToVertexList_nth_Suc) apply simp by arith
qed


(* Interlude: increasing properties *)

subsection\<open>Increasing properties of @{const subdivFace'}\<close>

lemma subdivFace'_incr:
assumes Ptrans: "\<And>x y z.  Q x y \<Longrightarrow> P y z \<Longrightarrow> P x z"
and mkFin: "\<And>f g. f \<in> \<F> g \<Longrightarrow> \<not> final f \<Longrightarrow> P g (makeFaceFinal f g)"
and fdg_incr: "\<And>g u v f vs.
   pre_splitFace g u v f vs \<Longrightarrow>
   Q g (snd(snd(splitFace g u v f vs)))"
shows
 "\<And>f' v n g. pre_subdivFace' g f' v' v n ovl \<Longrightarrow>
  minGraphProps g \<Longrightarrow>  f' \<in> \<F> g \<Longrightarrow> P g (subdivFace' g f' v n ovl)"
proof (induct ovl)
  case Nil thus ?case by (simp add: pre_subdivFace'_def mkFin)
next
  case (Cons ov ovl) then show ?case
    apply simp
    apply (cases "ov")
     apply (simp)
     apply (rule Cons)
        apply (rule pre_subdivFace'_None)
        apply assumption+
    apply simp
    apply (intro conjI)
     apply rule
     apply simp
     apply (rule Cons)
        apply (rule pre_subdivFace'_Some2)
        apply  assumption+
    apply (rule)
    apply (simp add: split_def)
    apply(rule Ptrans)
    prefer 2
    apply (rule Cons)
       apply (erule (1) pre_subdivFace'_Some1[OF _ _ _ _ HOL.refl HOL.refl])
        apply simp
       apply (simp add: minGraphProps_def faces_subset_def)
      apply (rule splitFace_holds_minGraphProps)
       apply (erule (1) pre_subdivFace'_preFaceDiv)
        apply simp
       apply(simp add: minGraphProps_def faces_subset_def)
      apply assumption
     apply (erule splitFace_add_f21')
    apply(rule fdg_incr)
    apply(erule (1) pre_subdivFace'_preFaceDiv)
     apply simp
    apply(simp add: minGraphProps_def faces_subset_def)
    done
qed

lemma next_plane0_via_subdivFace':
assumes mgp: "minGraphProps g" and gg': "g [next_plane0\<^bsub>p\<^esub>]\<rightarrow> g'"
and P: "\<And>f v' v n g ovs. minGraphProps g \<Longrightarrow> pre_subdivFace' g f v' v n ovs \<Longrightarrow>
  f \<in> \<F> g \<Longrightarrow> P g (subdivFace' g f v n ovs)"
shows "P g g'"
proof -
  from gg'
  obtain f v i "is" e where g': "g' = subdivFace g f is"
    and f: "f \<in> set (nonFinals g)" and v: "v \<in> \<V> f"
    and e: "e \<in> set (enumerator i |vertices f| )" and i: "2 < i"
    and containsNot: "\<not> containsDuplicateEdge g f v e"
    and is_eq: "is = indexToVertexList f v e"
    by (auto simp: next_plane0_def generatePolygon_def image_def split:if_split_asm)
  from f have fg: "f \<in> \<F> g" by(simp add:nonFinals_def)
  note pre_add = pre_subdivFace_indexToVertexList[OF mgp f v e containsNot i]
  with g' is_eq have g': "g' = subdivFace' g f v 0 (tl is)"
    by (simp  add: subdivFace_subdivFace'_eq)
  from pre_add is_eq have "is \<noteq> []"
    by (simp add: pre_subdivFace_def pre_subdivFace_face_def)
  with pre_add v is_eq
  have "pre_subdivFace' g f v v 0 (tl is)"
    by(fastforce simp add:neq_Nil_conv elim:pre_subdivFace_pre_subdivFace')
  from P[OF mgp this fg] g' show ?thesis by simp
qed

lemma next_plane0_incr:
assumes Ptrans: "\<And>x y z. Q x y \<Longrightarrow> P y z \<Longrightarrow> P x z"
and mkFin: "\<And>f g. f \<in> \<F> g \<Longrightarrow> \<not> final f \<Longrightarrow> P g (makeFaceFinal f g)"
and fdg_incr: "\<And>g u v f vs.
   pre_splitFace g u v f vs \<Longrightarrow>
   Q g (snd(snd(splitFace g u v f vs)))"
and mgp: "minGraphProps g" and gg': "g [next_plane0\<^bsub>p\<^esub>]\<rightarrow> g'"
shows "P g g'"
apply(rule next_plane0_via_subdivFace'[OF mgp gg'])
apply(rule subdivFace'_incr)
     apply(erule (1) Ptrans)
    apply(erule (1) mkFin)
   apply(erule fdg_incr)
  apply assumption+
done

(* End of interlude *)

subsubsection\<open>Increasing number of faces\<close>

lemma splitFace_incr_faces:
 "pre_splitFace g u v f vs \<Longrightarrow>
 finals(snd(snd(splitFace g u v f vs))) = finals g \<and>
       |nonFinals(snd(snd(splitFace g u v f vs)))| = Suc |nonFinals g|"
apply(unfold pre_splitFace_def)
apply(simp add: splitFace_def split_def finals_def nonFinals_def
      split_face_def filter_replace2 length_filter_replace2)
done


lemma subdivFace'_incr_faces:
 "pre_subdivFace' g f u v n ovs \<Longrightarrow>
  minGraphProps g \<Longrightarrow>  f \<in> \<F> g \<Longrightarrow>
  |finals (subdivFace' g f v n ovs)| = Suc |finals g| \<and>
  |nonFinals(subdivFace' g f v n ovs)| \<ge> |nonFinals g| - Suc 0"
apply(rule subdivFace'_incr)
prefer 4 apply assumption
prefer 4 apply assumption
prefer 4 apply assumption
prefer 2
apply(simp add: pre_subdivFace'_def len_finals_makeFaceFinal
      len_nonFinals_makeFaceFinal)
prefer 2
apply(erule splitFace_incr_faces)
apply (rule conjI)
 apply simp
apply arith
done


lemma next_plane0_incr_faces:
 "minGraphProps g \<Longrightarrow> g [next_plane0\<^bsub>p\<^esub>]\<rightarrow> g' \<Longrightarrow>
 |finals g'| = |finals g|+1 \<and> |nonFinals g'| \<ge> |nonFinals g| - 1"
apply simp
apply(rule next_plane0_incr)
prefer 4 apply assumption
prefer 4 apply assumption
prefer 2
apply(simp add: pre_subdivFace'_def len_finals_makeFaceFinal
      len_nonFinals_makeFaceFinal)
prefer 2
apply(erule splitFace_incr_faces)
apply (rule conjI)
 apply simp
apply arith
done

lemma two_faces_subdivFace':
  "pre_subdivFace' g f u v n ovs \<Longrightarrow> minGraphProps g \<Longrightarrow> f \<in> \<F> g \<Longrightarrow>
  |faces g| \<ge> 2 \<Longrightarrow> |faces(subdivFace' g f v n ovs)| \<ge> 2"
apply(drule (2) subdivFace'_incr_faces)
using len_faces_sum[of g] len_faces_sum[of "subdivFace' g f v n ovs"] by arith

subsection\<open>Main invariant theorems\<close>

lemma inv_genPoly:
assumes inv: "inv g" and polygen: "g' \<in> set(generatePolygon i v f g)"
and f: "f \<in> set (nonFinals g)" and i: "2 < i" and v: "v \<in> \<V> f"
shows "inv g'"
proof(unfold inv_def)
  have mgp: "minGraphProps g" and 1: "one_final g"
    using inv by(simp add:inv_def)+
  from polygen
  obtain "is" e where g': "g' = subdivFace g f is"
    and e: "e \<in> set (enumerator i |vertices f| )"
    and containsNot: "\<not> containsDuplicateEdge g f v e"
    and is_eq: "is = indexToVertexList f v e"
    by (auto simp: generatePolygon_def)
  have f': "f \<in> \<F> g" using f by(simp add:nonFinals_def)
  note pre_add = pre_subdivFace_indexToVertexList[OF mgp f v e containsNot i]
  with g' is_eq have g': "g' = subdivFace' g f v 0 (tl is)"
    by (simp  add: subdivFace_subdivFace'_eq)
  from pre_add is_eq have i_nz: "is \<noteq> []"
    by (simp add: pre_subdivFace_def pre_subdivFace_face_def)
  with pre_add v i_nz is_eq
  have pre_addSnd: "pre_subdivFace' g f v v 0 (tl is)"
    by(fastforce simp add:neq_Nil_conv elim:pre_subdivFace_pre_subdivFace')
  note 2 = one_final_antimono[OF 1]
  show "minGraphProps g' \<and> one_final g' \<and> |faces g'| \<ge> 2"
  proof auto
    show "minGraphProps g'" using g' pre_addSnd f
      apply (simp add:nonFinals_def)
      apply (rule subdivFace'_holds_minGraphProps[OF _ _ mgp])
      by (simp_all add: succs)
  next
    show "one_final g'" using g' 1
      by (simp add: one_final_subdivFace'[OF pre_addSnd mgp f' 2])
  next
    show "|faces g'| \<ge> 2" using g'
      by (simp add: two_faces_subdivFace'[OF pre_addSnd mgp f' inv_two_faces[OF inv]])
  qed
qed


lemma inv_inv_next_plane0: "invariant inv next_plane0\<^bsub>p\<^esub>"
proof(clarsimp simp:invariant_def)
  fix g g'
  assume  inv: "inv g" and "g' \<in> set (next_plane0\<^bsub>p\<^esub> g)"
  then obtain i v f where "g' \<in> set(generatePolygon i v f g)"
    and "f \<in> set (nonFinals g)" and "2 < i" and "v \<in> \<V> f"
    by (auto simp: next_plane0_def split: if_split_asm)
  thus "inv g'" using inv by(blast intro:inv_genPoly)
qed

end
