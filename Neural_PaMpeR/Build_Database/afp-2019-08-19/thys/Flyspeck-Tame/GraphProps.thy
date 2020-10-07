(*  Author:  Gertrud Bauer, Tobias Nipkow  *)

section\<open>Properties of Graph Utilities\<close>

theory GraphProps
imports Graph
begin

declare [[linarith_neq_limit = 3]]

lemma final_setFinal[iff]: "final(setFinal f)"
by (simp add:setFinal_def)


lemma eq_setFinal_iff[iff]: "(f = setFinal f) = final f"
proof (induct f)
  case (Face f t)
  then show ?case
    by (cases t) (simp_all add: setFinal_def)
qed

lemma setFinal_eq_iff[iff]: "(setFinal f = f) = final f"
by (blast dest:sym intro:sym)


lemma distinct_vertices[iff]: "distinct(vertices(g::graph))"
by(induct g) simp


subsection\<open>@{const nextElem}\<close>

lemma nextElem_append[simp]:
 "y \<notin> set xs \<Longrightarrow> nextElem (xs @ ys) d y = nextElem ys d y"
by(induct xs) auto

lemma nextElem_cases:
"nextElem xs d x = y \<Longrightarrow>
 x \<notin> set xs \<and> y = d \<or>
 xs \<noteq> [] \<and> x = last xs \<and> y = d \<and> x \<notin> set(butlast xs) \<or>
 (\<exists>us vs. xs = us @ [x,y] @ vs \<and> x \<notin> set us)"
apply(induct xs)
 apply simp
apply simp
apply(split if_splits)
 apply(simp split:list.splits)
 apply(rule_tac x = "[]" in exI)
 apply simp
apply simp
apply(erule disjE)
 apply simp
apply(erule disjE)
 apply clarsimp
apply(rule conjI)
 apply clarsimp
apply (clarsimp)
apply(erule_tac x = "a#us" in allE)
apply simp
done


lemma nextElem_notin_butlast[rule_format,simp]:
 "y \<notin> set(butlast xs) \<longrightarrow> nextElem xs x y = x"
by(induct xs) auto

lemma nextElem_in: "nextElem xs x y : set(x#xs)"
apply (induct xs)
 apply simp
apply auto
apply(clarsimp split: list.splits)
apply(clarsimp split: list.splits)
done

lemma nextElem_notin[simp]: "a \<notin> set as \<Longrightarrow> nextElem as c a = c"
by(erule nextElem_append[where ys = "[]", simplified])

lemma nextElem_last[simp]: assumes dist: "distinct xs"
shows "nextElem xs c (last xs) = c"
proof cases
  assume "xs = []" thus ?thesis by simp
next
  let ?xs = "butlast xs @ [last xs]"
  assume xs: "xs \<noteq> []"
  with dist have "distinct ?xs" by simp
  hence notin: "last xs \<notin> set(butlast xs)" by simp
  from xs have "nextElem xs c (last xs) = nextElem ?xs c (last xs)" by simp
  also from notin have "\<dots> = c" by simp
  finally show ?thesis .
qed


lemma prevElem_nextElem:
assumes dist: "distinct xs" and xxs: "x : set xs"
shows "nextElem (rev xs) (last xs) (nextElem xs (hd xs) x) = x"
proof -
  define x' where "x' = nextElem xs (hd xs) x"
  hence nE: "nextElem xs (hd xs) x = x'" by simp
  have "xs \<noteq> [] \<and> x = last xs \<and> x' = hd xs \<or> (\<exists>us vs. xs = us @ [x, x'] @ vs)"
    (is "?A \<or> ?B")
    using nextElem_cases[OF nE] xxs by blast
  thus ?thesis
  proof
    assume ?A
    thus ?thesis using dist by(clarsimp simp:neq_Nil_conv)
  next
    assume ?B
    then obtain us vs where [simp]: "xs = us @ [x, x'] @ vs" by blast
    thus ?thesis using dist by simp
  qed
qed

lemma nextElem_prevElem:
 "\<lbrakk> distinct xs; x : set xs \<rbrakk> \<Longrightarrow>
  nextElem xs (hd xs) (nextElem (rev xs) (last xs) x) = x"
apply(cases "xs = []")
 apply simp
using prevElem_nextElem[where xs = "rev xs" and x=x]
apply(simp add:hd_rev last_rev)
done


lemma nextElem_nth:
 "\<And>i. \<lbrakk>distinct xs; i < length xs \<rbrakk>
   \<Longrightarrow> nextElem xs z (xs!i) = (if length xs = i+1 then z else xs!(i+1))"
apply(induct xs) apply simp
apply(case_tac i)
 apply(simp split:list.split)
apply clarsimp
done


subsection \<open>\<open>nextVertex\<close>\<close>

lemma nextVertex_in_face'[simp]:
  "vertices f \<noteq> [] \<Longrightarrow> f \<bullet> v \<in> \<V> f"
proof -
  assume f: "vertices f \<noteq> []"
  define c where "c = nextElem (vertices f) (hd (vertices f)) v"
  then have "nextElem (vertices f) (hd (vertices f)) v = c" by auto
  with f show ?thesis
    apply (simp add: nextVertex_def)
    apply (drule_tac nextElem_cases)
    apply(fastforce simp:neq_Nil_conv)
    done
qed

lemma nextVertex_in_face[simp]:
  "v \<in> set (vertices f) \<Longrightarrow> f \<bullet> v \<in> \<V> f"
 by (auto intro: nextVertex_in_face')


lemma nextVertex_prevVertex[simp]:
 "\<lbrakk> distinct(vertices f); v \<in> \<V> f \<rbrakk>
 \<Longrightarrow> f \<bullet> (f\<^bsup>-1\<^esup> \<bullet> v) = v"
by(simp add:prevVertex_def nextVertex_def nextElem_prevElem)

lemma prevVertex_nextVertex[simp]:
 "\<lbrakk> distinct(vertices f); v \<in> \<V> f \<rbrakk>
 \<Longrightarrow> f\<^bsup>-1\<^esup> \<bullet> (f \<bullet> v) = v"
by(simp add:prevVertex_def nextVertex_def prevElem_nextElem)

lemma prevVertex_in_face[simp]:
 "v \<in> \<V> f \<Longrightarrow> f\<^bsup>-1\<^esup> \<bullet> v \<in> \<V> f"
apply(cases "vertices f = []")
 apply simp
using nextElem_in[of "rev (vertices f)" "(last (vertices f))" v]
apply (auto simp add: prevVertex_def)
done

lemma nextVertex_nth:
 "\<lbrakk> distinct(vertices f); i < |vertices f| \<rbrakk> \<Longrightarrow>
  f \<bullet> (vertices f ! i) = vertices f ! ((i+1) mod |vertices f| )"
apply(cases "vertices f = []") apply simp
apply(simp add:nextVertex_def nextElem_nth hd_conv_nth)
done


subsection \<open>\<open>\<E>\<close>\<close>

lemma edges_face_eq:
 "((a,b) \<in> \<E> (f::face)) = ((f \<bullet> a = b) \<and> a \<in> \<V> f)"
by (auto simp add: edges_face_def)


lemma edges_setFinal[simp]: "\<E>(setFinal f) = \<E> f"
by(induct f)(simp add:setFinal_def edges_face_def nextVertex_def)

lemma in_edges_in_vertices:
 "(x,y) \<in> \<E>(f::face) \<Longrightarrow> x \<in> \<V> f \<and> y \<in> \<V> f"
apply(simp add:edges_face_eq nextVertex_def)
apply(cut_tac xs= "vertices f" and x= "hd(vertices f)" and y=x in nextElem_in)
apply(cases "vertices f")
apply(auto)
done


lemma vertices_conv_Union_edges:
 "\<V>(f::face) = (\<Union>(a,b)\<in>\<E> f. {a})"
apply(induct f)
apply(simp add:vertices_face_def edges_face_def)
apply blast
done


lemma nextVertex_in_edges: "v \<in> \<V> f \<Longrightarrow> (v, f \<bullet> v) \<in> edges f"
by(auto simp:edges_face_def)

lemma prevVertex_in_edges:
 "\<lbrakk>distinct(vertices f); v \<in> \<V> f\<rbrakk> \<Longrightarrow> (f\<^bsup>-1\<^esup> \<bullet> v, v) \<in> edges f"
by(simp add:edges_face_eq)


subsection \<open>Triangles\<close>

lemma vertices_triangle:
   "|vertices f| = 3 \<Longrightarrow> a \<in> \<V> f \<Longrightarrow>
  distinct (vertices f) \<Longrightarrow>
  \<V> f = {a, f \<bullet> a, f \<bullet> (f \<bullet> a)}"
proof -
  assume "|vertices f| = 3"
  then obtain a1 a2 a3 where "vertices f = [a1, a2, a3]"
    by (auto dest!:  length3D)
  moreover assume "a \<in> \<V> f"
  moreover assume "distinct (vertices f)"
  ultimately show ?thesis
    by (simp, elim disjE) (auto simp add: nextVertex_def)
qed

(* could be generalized from 3 to n
   but presburger would no longer do the job *)
lemma tri_next3_id:
 "|vertices f| = 3 \<Longrightarrow> distinct(vertices f) \<Longrightarrow> v \<in> \<V> f
  \<Longrightarrow> f \<bullet> (f \<bullet> (f \<bullet> v)) = v"
apply(subgoal_tac "\<forall>(i::nat) < 3. (((((i+1) mod 3)+1) mod 3)+1) mod 3 = i")
 apply(clarsimp simp:in_set_conv_nth nextVertex_nth)
apply(presburger)
done


lemma triangle_nextVertex_prevVertex:
 "|vertices f| = 3 \<Longrightarrow> a \<in> \<V> f \<Longrightarrow>
  distinct (vertices f) \<Longrightarrow>
  f \<bullet> (f \<bullet> a) = f\<^bsup>-1\<^esup> \<bullet> a"
proof -
  assume "|vertices f| = 3"
  then obtain a1 a2 a3 where "vertices f = [a1, a2, a3]"
    by (auto dest!:length3D)
  moreover assume "a \<in> \<V> f"
  moreover assume "distinct (vertices f)"
  ultimately show ?thesis
    by (simp, elim disjE) (auto simp add: nextVertex_def prevVertex_def)
qed

subsection \<open>Quadrilaterals\<close>


lemma vertices_quad:
  "|vertices f| = 4 \<Longrightarrow> a \<in> \<V> f \<Longrightarrow>
  distinct (vertices f) \<Longrightarrow>
  \<V> f = {a, f \<bullet> a, f \<bullet> (f \<bullet> a), f \<bullet> (f \<bullet> (f \<bullet> a))}"
proof -
  assume "|vertices f| = 4"
  then obtain a1 a2 a3 a4 where "vertices f = [a1, a2, a3, a4]"
    by (auto dest!: length4D)
  moreover assume "a \<in> \<V> f"
  moreover assume "distinct (vertices f)"
  ultimately show ?thesis
    by (simp, elim disjE) (auto simp add: nextVertex_def)
qed

lemma quad_next4_id:
 "\<lbrakk> |vertices f| = 4; distinct(vertices f); v \<in> \<V> f \<rbrakk> \<Longrightarrow>
  f \<bullet> (f \<bullet> (f \<bullet> (f \<bullet> v))) = v"
apply(subgoal_tac "\<forall>(i::nat) < 4.
 (((((((i+1) mod 4)+1) mod 4)+1) mod 4)+1) mod 4 = i")
 apply(clarsimp simp:in_set_conv_nth nextVertex_nth)
apply(presburger)
done


lemma quad_nextVertex_prevVertex:
 "|vertices f| = 4 \<Longrightarrow> a \<in> \<V> f \<Longrightarrow> distinct (vertices f) \<Longrightarrow>
  f \<bullet> (f \<bullet> (f \<bullet> a)) = f\<^bsup>-1\<^esup> \<bullet> a"
proof -
  assume "|vertices f| = 4"
  then obtain a1 a2 a3 a4 where "vertices f = [a1, a2, a3, a4]"
    by (auto dest!: length4D)
  moreover assume "a \<in> \<V> f"
  moreover assume "distinct (vertices f)"
  ultimately show ?thesis
    by (auto) (auto simp add: nextVertex_def prevVertex_def)
qed

(*
lemma C0[dest]: "f \<in> set (facesAt g v) \<Longrightarrow> v \<in> \<V> g"
  by (simp add: facesAt_def split: if_split_asm)
*)

lemma len_faces_sum: "|faces g| = |finals g| + |nonFinals g|"
by(simp add:finals_def nonFinals_def sum_length_filter_compl)


lemma graph_max_final_ex:
 "\<exists>f\<in>set (finals (graph n)). |vertices f| = n"
proof (induct "n")
  case 0 then show ?case by (simp add: graph_def finals_def)
next
  case (Suc n) then show ?case
   by (simp add: graph_def finals_def)
qed


subsection\<open>No loops\<close>

lemma distinct_no_loop2:
 "\<lbrakk> distinct(vertices f); v \<in> \<V> f; u \<in> \<V> f; u \<noteq> v \<rbrakk> \<Longrightarrow> f \<bullet> v \<noteq> v"
apply(frule split_list[of v])
apply(clarsimp simp: nextVertex_def neq_Nil_conv hd_append
  split:list.splits if_split_asm)
done

lemma distinct_no_loop1:
 "\<lbrakk> distinct(vertices f); v \<in> \<V> f; |vertices f| > 1 \<rbrakk> \<Longrightarrow> f \<bullet> v \<noteq> v"
apply(subgoal_tac "\<exists>u \<in> \<V> f. u \<noteq> v")
 apply(blast dest:distinct_no_loop2)
apply(cases "vertices f") apply simp
apply(rename_tac a as)
apply (clarsimp simp:neq_Nil_conv)
done


subsection\<open>@{const between}\<close>

lemma between_front[simp]:
 "v \<notin> set us \<Longrightarrow> between (u # us @ v # vs) u v = us"
by(simp add:between_def split_def)

lemma between_back:
 "\<lbrakk> v \<notin> set us; u \<notin> set vs; v \<noteq> u \<rbrakk> \<Longrightarrow> between (v # vs @ u # us) u v = us"
by(simp add:between_def split_def)


lemma next_between:
 "\<lbrakk>distinct(vertices f); v \<in> \<V> f; u \<in> \<V> f; f \<bullet> v \<noteq> u \<rbrakk>
  \<Longrightarrow> f \<bullet> v \<in> set(between (vertices f) v u)"
apply(frule split_list[of u])
apply(clarsimp)
apply(erule disjE)
 apply(clarsimp simp:set_between_id nextVertex_def hd_append split:list.split)
apply(erule disjE)
 apply(frule split_list[of v])
 apply(clarsimp simp: between_def split_def nextVertex_def split:list.split)
 apply(clarsimp simp:append_eq_Cons_conv)
apply(frule split_list[of v])
apply(clarsimp simp: between_def split_def nextVertex_def split:list.split)
apply(clarsimp simp: hd_append)
done


lemma next_between2:
 "\<lbrakk> distinct(vertices f); v \<in> \<V> f; u \<in> \<V> f; u \<noteq> v \<rbrakk> \<Longrightarrow>
  v \<in> set(between (vertices f) u (f \<bullet> v))"
apply(frule split_list[of u])
apply(clarsimp)
apply(erule disjE)
 apply(clarsimp simp: nextVertex_def hd_append split:list.split)
 apply(rule conjI)
  apply(clarsimp)
 apply(frule split_list[of v])
 apply(clarsimp simp: between_def split_def split:list.split)
 apply(fastforce simp: append_eq_Cons_conv)
apply(frule split_list[of v])
apply(clarsimp simp: between_def split_def nextVertex_def split:list.splits)
apply(clarsimp simp: hd_append)
apply(erule disjE)
 apply(clarsimp)
apply(frule split_list)
apply(fastforce)
done


(* distinctness seems not to be necessary but simplifies the proof *)
lemma between_next_empty:
 "distinct(vertices f) \<Longrightarrow> between (vertices f) v (f \<bullet> v) = []"
apply(cases "v \<in> \<V> f")
 apply(frule split_list)
 apply(clarsimp simp:between_def split_def nextVertex_def
   neq_Nil_conv hd_append split:list.split)
 apply(clarsimp simp:between_def split_def nextVertex_def)
apply(cases "vertices f")
 apply simp
apply simp
done


lemma unroll_between_next2:
 "\<lbrakk> distinct(vertices f); u \<in> \<V> f; v \<in> \<V> f; u \<noteq> v \<rbrakk> \<Longrightarrow>
  between (vertices f) u (f \<bullet> v) = between (vertices f) u v @ [v]"
using split_between[OF _ _ _ next_between2]
by (simp add: between_next_empty split:if_split_asm)


lemma nextVertex_eq_lemma:
 "\<lbrakk> distinct(vertices f); x \<in> \<V> f; y \<in> \<V> f; x \<noteq> y;
    v \<in> set(x # between (vertices f) x y) \<rbrakk> \<Longrightarrow>
  f \<bullet> v = nextElem (x # between (vertices f) x y @ [y]) z v"
apply(drule split_list[of x])
apply(simp add:nextVertex_def)
apply(erule disjE)
 apply(clarsimp)
 apply(erule disjE)
  apply(drule split_list)
  apply(clarsimp simp add:between_def split_def hd_append split:list.split)
  apply(fastforce simp:append_eq_Cons_conv)
 apply(drule split_list)
 apply(clarsimp simp add:between_def split_def hd_append split:list.split)
 apply(fastforce simp:append_eq_Cons_conv)
apply(clarsimp)
 apply(erule disjE)
 apply(drule split_list[of y])
 apply(clarsimp simp:between_def split_def)
 apply(erule disjE)
  apply(drule split_list[of v])
  apply(fastforce simp: hd_append neq_Nil_conv split:list.split)
 apply(drule split_list[of v])
 apply(clarsimp)
 apply(clarsimp simp: hd_append split:list.split)
 apply(fastforce simp:append_eq_Cons_conv)
apply(drule split_list[of y])
apply(clarsimp simp:between_def split_def)
apply(drule split_list[of v])
apply(clarsimp)
apply(clarsimp simp: hd_append split:list.split)
apply(clarsimp simp:append_eq_Cons_conv)
apply(fastforce simp: hd_append neq_Nil_conv split:list.split)
done

end
