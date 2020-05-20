(*  Author:     Gertrud Bauer, Tobias Nipkow
*)

section \<open>Properties of Lower Bound Machinery\<close>

theory ScoreProps
imports ListSum TameEnum PlaneProps TameProps
begin

lemma deleteAround_empty[simp]: "deleteAround g a [] = []"
by (simp add: deleteAround_def)

lemma deleteAroundCons:
  "deleteAround g a (p#ps) =
    (if fst p \<in> {v. \<exists>f \<in> set (facesAt g a).
               (length (vertices f) = 4) \<and> v \<in> {f \<bullet> a, f \<bullet> (f \<bullet> a)}
             \<or> (length (vertices f) \<noteq> 4) \<and> (v = f \<bullet> a)}
     then deleteAround g a ps
     else p#deleteAround g a ps)"
by (fastforce simp: nextV2 deleteAround_def)

lemma deleteAround_subset: "set (deleteAround g a ps) \<subseteq> set ps"
by (simp add: deleteAround_def)

lemma distinct_deleteAround: "distinct (map fst ps) \<Longrightarrow>
    distinct (map fst (deleteAround g (fst (a, b)) ps))"
proof (induct ps)
  case Nil then show ?case by simp
next
  case (Cons p ps)
  then have "fst p \<notin> fst ` set ps" by simp
  moreover have "set (deleteAround g a ps) \<subseteq> set ps"
    by (rule deleteAround_subset)
  ultimately have "fst p \<notin> fst ` set (deleteAround g a ps)" by auto

  moreover from Cons have "distinct (map fst ps)" by simp
  then have "distinct (map fst (deleteAround g (fst (a, b)) ps))"
    by (rule Cons)
  ultimately show ?case by (simp add: deleteAroundCons)
qed


definition deleteAround' :: "graph \<Rightarrow> vertex \<Rightarrow> (vertex \<times> nat) list \<Rightarrow>
    (vertex \<times> nat) list" where
  "deleteAround' g v ps \<equiv>
      let fs = facesAt g v;
      vs = (\<lambda>f. let n1 = f \<bullet> v;
                n2 = f \<bullet> n1 in
                if length (vertices f) = 4 then [n1, n2] else [n1]);
      ws = concat (map vs fs) in
      removeKeyList ws ps"


lemma deleteAround_eq: "deleteAround g v ps = deleteAround' g v ps"
apply (auto simp add: deleteAround_def deleteAround'_def split: if_split_asm)
apply (unfold nextV2[THEN eq_reflection], simp)
done

lemma deleteAround_nextVertex:
  "f \<in> set (facesAt g a) \<Longrightarrow>
  (f \<bullet> a, b) \<notin> set (deleteAround g a ps)"
by (auto simp add: deleteAround_eq deleteAround'_def removeKeyList_eq)

lemma deleteAround_nextVertex_nextVertex:
  "f \<in> set (facesAt g a) \<Longrightarrow> |vertices f| = 4 \<Longrightarrow>
  (f \<bullet> (f \<bullet> a), b) \<notin> set (deleteAround g a ps)"
by (auto simp add: deleteAround_eq deleteAround'_def removeKeyList_eq)


lemma deleteAround_prevVertex:
  "minGraphProps g \<Longrightarrow> a : \<V> g \<Longrightarrow> f \<in> set (facesAt g a) \<Longrightarrow>
  (f\<^bsup>-1\<^esup> \<bullet> a, b) \<notin> set (deleteAround g a ps)"
proof -
  assume a: "minGraphProps g" "a : \<V> g" "f \<in> set (facesAt g a)"
  have "(f\<^bsup>-1\<^esup> \<bullet> a, a) \<in> \<E> f" using a
    by(blast intro:prevVertex_in_edges minGraphProps)
  then obtain f' :: face where f': "f' \<in> set(facesAt g a)"
    and e: "(a, f\<^bsup>-1\<^esup> \<bullet> a) \<in> \<E> f'"
    using a by(blast dest:mgp_edge_face_ex)
  have "(f' \<bullet> a, b) \<notin> set (deleteAround g a ps)" using f'
    by (auto simp add: deleteAround_eq deleteAround'_def removeKeyList_eq)
  moreover have "f' \<bullet> a = f\<^bsup>-1\<^esup> \<bullet> a"
    using e by (simp add:edges_face_eq)
  ultimately show ?thesis by simp
qed


lemma deleteAround_separated:
assumes mgp: "minGraphProps g" and fin: "final g" and ag: "a : \<V> g" and 4: "|vertices f| \<le> 4"
and f: "f \<in> set(facesAt g a)"
shows "\<V> f \<inter> set [fst p. p \<leftarrow> deleteAround g a ps] \<subseteq> {a}" (is "?A")
proof -
  note MGP = mgp ag f
  have af: "a \<in> \<V> f" using MGP by(blast intro:minGraphProps)
  have "2 < |vertices f|" using MGP by(blast intro:minGraphProps)
  with 4 have "|vertices f| = 3 \<or> |vertices f| = 4" by arith
  then show "?A"
  proof
    assume 3: "|vertices f| = 3"
    show "?A"
    proof (rule ccontr)
      assume "\<not> ?A"
      then obtain b where b1: "b \<noteq> a" "b \<in> \<V> f"
        "b \<in> set (map fst (deleteAround g a ps))" by auto
      from MGP have d: "distinct (vertices f)"
        by(blast intro:minGraphProps)
      with af 3 have "\<V> f = {a, f \<bullet> a, f \<bullet> (f \<bullet> a)}"
          by (rule_tac vertices_triangle)
      also from d af 3 have
        "f \<bullet> (f \<bullet> a) = f\<^bsup>-1\<^esup> \<bullet> a"
        by (simp add: triangle_nextVertex_prevVertex)
      finally have
        "b \<in> {f \<bullet> a, f\<^bsup>-1\<^esup> \<bullet> a}"
        using b1 by simp
      with MGP have "b \<notin> set (map fst (deleteAround g a ps))"
      using deleteAround_nextVertex deleteAround_prevVertex by auto
      then show False by contradiction (rule b1)
    qed
  next
    assume 4: "|vertices f| = 4"
    show "?A"
    proof (rule ccontr)
      assume "\<not> ?A"
      then obtain b where b1: "b \<noteq> a" "b \<in> \<V> f"
        "b \<in> set (map fst (deleteAround g a ps))" by auto
      from MGP have d: "distinct (vertices f)" by(blast intro:minGraphProps)
      with af 4 have "\<V> f = {a, f \<bullet> a, f \<bullet> (f \<bullet> a), f \<bullet> (f \<bullet> (f \<bullet> a))}"
        by (rule_tac vertices_quad)
      also from d af 4 have "f \<bullet> (f \<bullet> (f \<bullet> a)) = f\<^bsup>-1\<^esup> \<bullet> a"
        by (simp add: quad_nextVertex_prevVertex)
      finally have "b \<in> {f \<bullet> a, f \<bullet> (f \<bullet> a), f\<^bsup>-1\<^esup> \<bullet> a}"
      using b1 by simp
      with MGP 4 have "b \<notin> set (map fst (deleteAround g a ps))"
      using deleteAround_nextVertex deleteAround_prevVertex
           deleteAround_nextVertex_nextVertex by auto
      then show False by contradiction (rule b1)
    qed
  qed
qed
(*
deleteAround g y loescht nextVertex f a,
nextVertex f (nextVertex f a),
prevVertex f a wird mit nachbarflaeche geloescht.
*)

lemma [iff]: "separated g {}"
by (simp add: separated_def separated\<^sub>2_def separated\<^sub>3_def)

lemma separated_insert:
assumes mgp: "minGraphProps g" and a: "a \<in> \<V> g"
  and Vg: "V \<subseteq> \<V> g"
  and ps: "separated g V"
  and s2: "(\<And>f. f \<in> set (facesAt g a) \<Longrightarrow> f \<bullet> a \<notin> V)"
  and s3: "(\<And>f. f \<in> set (facesAt g a) \<Longrightarrow>
      |vertices f| \<le> 4 \<Longrightarrow> \<V> f \<inter> V \<subseteq> {a})"
  shows "separated g (insert a V)"
proof (simp add: separated_def separated\<^sub>2_def separated\<^sub>3_def,
 intro conjI ballI impI)
  fix f assume f: "f \<in> set (facesAt g a)"
  then show "f \<bullet> a \<noteq> a" by (rule mgp_facesAt_no_loop[OF mgp a])
  from f show "f \<bullet> a \<notin> V" by (rule s2)
next
  fix f v assume v: "f \<in> set (facesAt g v)" and vV: "v \<in> V"
  have "v : \<V> g" using vV Vg by blast
  show "f \<bullet> v \<noteq> a"
  proof
    assume f: "f \<bullet> v = a"
    then obtain f' where f': "f' \<in> set(facesAt g a)" and v: "f' \<bullet> a = v"
      using mgp_nextVertex_face_ex2[OF mgp \<open>v : \<V> g\<close> v] by blast
    have "f' \<bullet> a \<in> V" using v vV by simp
    with f' s2 show False by blast
  qed
  from ps v vV show "f \<bullet> v \<notin> V"
    by (simp add: separated_def separated\<^sub>2_def)
next
  fix f assume f:  "f \<in> set (facesAt g a)" "|vertices f| \<le> 4"
  then have "\<V> f \<inter> V \<subseteq> {a}" by (rule s3)
  moreover from mgp a f have "a \<in> \<V> f" by(blast intro:minGraphProps)
  ultimately show "\<V> f \<inter> insert a V = {a}" by auto
next
  fix v f
  assume a: "v \<in> V" "f \<in> set (facesAt g v)"
    "|vertices f| \<le> 4"
  with ps have v: "\<V> f \<inter> V = {v}"
    by (simp add: separated_def separated\<^sub>3_def)
  have "v : \<V> g" using a Vg by blast
  show  "\<V> f \<inter> insert a V = {v}"
  proof cases
    assume "a = v"
    with v mgp a show ?thesis by(blast intro:minGraphProps)
  next
    assume n: "a \<noteq> v"
    have  "a \<notin> \<V> f"
    proof
      assume a2: "a \<in> \<V> f"
      with mgp a \<open>v : \<V> g\<close> have "f \<in> \<F> g" by(blast intro:minGraphProps)
      with mgp a2 have "f \<in> set (facesAt g a)" by(blast intro:minGraphProps)
      with a have "\<V> f \<inter> V \<subseteq> {a}" by (simp add: s3)
      with v have "a = v" by auto
      with n show False by auto
    qed
    with a  v show "\<V> f \<inter> insert a V = {v}" by blast
  qed
qed


function ExcessNotAtRecList :: "(vertex, nat) table \<Rightarrow> graph \<Rightarrow> vertex list" where
  "ExcessNotAtRecList [] = (\<lambda>g. [])"
  | "ExcessNotAtRecList ((x, y) # ps) = (\<lambda>g.
      let l1 = ExcessNotAtRecList ps g;
      l2 = ExcessNotAtRecList (deleteAround g x ps) g in
      if ExcessNotAtRec ps g
       \<le> y + ExcessNotAtRec (deleteAround g x ps) g
      then x # l2 else l1)"
by pat_completeness auto
termination by (relation "measure size")
  (auto simp add: less_Suc_eq_le length_deleteAround)

lemma isTable_deleteAround:
  "isTable E vs ((a,b)#ps) \<Longrightarrow> isTable E vs (deleteAround g a ps)"
by (rule isTable_subset, rule deleteAround_subset,
    rule isTable_Cons)

lemma ListSum_ExcessNotAtRecList:
 "isTable E vs ps \<Longrightarrow> ExcessNotAtRec ps g
  = (\<Sum>\<^bsub>p \<in> ExcessNotAtRecList ps g\<^esub> E p)" (is "?T ps \<Longrightarrow> ?P ps")
proof (induct ps rule: ExcessNotAtRecList.induct)
  case 1 show ?case by simp
next
  case (2 a b ps)
  from 2 have prem: "?T ((a,b)#ps)" by blast
  then have E: "b = E a" by (simp add: isTable_eq)
  from 2 have hyp1: "?T (deleteAround g a ps) \<Longrightarrow>
   ?P (deleteAround g a ps)" by blast
  from 2 have hyp2:  "?T ps \<Longrightarrow> ?P ps" by blast
  have H1: "?P (deleteAround g a ps)"
    by (rule hyp1, rule isTable_deleteAround) (rule prem)
  have H2: "?P ps" by (rule hyp2, rule isTable_Cons, rule prem)
  show "?P ((a,b)#ps)"
  proof cases
    assume
    "ExcessNotAtRec ps g
    \<le> b + ExcessNotAtRec (deleteAround g a ps) g"
    with H1 E show ?thesis
      by (simp add: max_def split: if_split_asm)
  next
    assume "\<not> ExcessNotAtRec ps g
       \<le> b + ExcessNotAtRec (deleteAround g a ps) g"
    with H2 E show ?thesis
      by (simp add: max_def split: if_split_asm)
  qed
qed

lemma ExcessNotAtRecList_subset:
  "set (ExcessNotAtRecList ps g) \<subseteq> set [fst p. p \<leftarrow> ps]" (is "?P ps")
proof (induct ps rule: ExcessNotAtRecList.induct)
  case 1 show ?case by simp
next
  case (2 a b ps)
  presume H1: "?P (deleteAround g a ps)"
  presume H2: "?P ps"
  show "?P ((a, b) # ps)"
  proof cases
    assume a: "ExcessNotAtRec ps g
      \<le> b + ExcessNotAtRec (deleteAround g a ps) g"
    have "set (deleteAround g a ps) \<subseteq> set ps"
      by (simp add: deleteAround_subset)
    then have
    "fst ` set (deleteAround g a ps) \<subseteq> insert a (fst ` set ps)"
      by blast
    with a H1 show ?thesis by (simp)
  next
    assume "\<not> ExcessNotAtRec ps g
      \<le> b + ExcessNotAtRec (deleteAround g a ps) g"
    with H2 show ?thesis by (auto)
  qed
qed simp

lemma separated_ExcessNotAtRecList:
 "minGraphProps g \<Longrightarrow> final g \<Longrightarrow> isTable E (vertices g) ps \<Longrightarrow>
  separated g (set (ExcessNotAtRecList ps g))"
proof -
  assume fin: "final g" and mgp: "minGraphProps g"
  show
   "isTable E (vertices g) ps \<Longrightarrow> separated g (set (ExcessNotAtRecList ps g))"
   (is "?T ps \<Longrightarrow> ?P ps")
  proof (induct rule: ExcessNotAtRec.induct)
    case 1 show ?case by simp
  next
    case (2 a b ps)
    from 2 have prem: "?T ((a,b)#ps)" by blast
    then have E: "b = E a" by (simp add: isTable_eq)
    have "a :\<V> g" using prem by(auto simp: isTable_def)
    from 2 have hyp1: "?T (deleteAround g a ps) \<Longrightarrow>
      ?P (deleteAround g a ps)" by blast
    from 2 have hyp2:  "?T ps \<Longrightarrow> ?P ps" by blast
    have H1: "?P (deleteAround g a ps)"
      by (rule hyp1, rule isTable_deleteAround) (rule prem)
    have H2: "?P ps" by (rule hyp2, rule isTable_Cons) (rule prem)

    show "?P ((a,b)#ps)"
    proof cases
      assume c: "ExcessNotAtRec ps g
        \<le> b + ExcessNotAtRec (deleteAround g a ps) g"
      have "separated g
       (insert a (set (ExcessNotAtRecList (deleteAround g a ps) g)))"
      proof (rule separated_insert[OF mgp])
        from prem show "a \<in> set (vertices g)" by (auto simp add: isTable_def)

        show "set (ExcessNotAtRecList (deleteAround g a ps) g) \<subseteq> \<V> g"
        proof-
          have "set (ExcessNotAtRecList (deleteAround g a ps) g) \<subseteq>
                set (map fst (deleteAround g a ps))"
            by(rule ExcessNotAtRecList_subset[simplified concat_map_singleton])
          also have "\<dots> \<subseteq> set (map fst ps)"
            using deleteAround_subset by fastforce
          finally show ?thesis using prem by(auto simp: isTable_def)
        qed
        from H1
        show pS: "separated g
            (set (ExcessNotAtRecList (deleteAround g a ps) g))"
          by simp

        fix f assume f: "f \<in> set (facesAt g a)"
        then have
        "f \<bullet> a \<notin> set [fst p. p \<leftarrow> deleteAround g a ps]"
          by (auto simp add: facesAt_def deleteAround_eq deleteAround'_def
            removeKeyList_eq split: if_split_asm)
        moreover
        have "set (ExcessNotAtRecList (deleteAround g a ps) g)
          \<subseteq> set [fst p. p \<leftarrow> deleteAround g a ps]"
          by (rule ExcessNotAtRecList_subset)
        ultimately
        show "f \<bullet> a
          \<notin> set (ExcessNotAtRecList (deleteAround g a ps) g)"
          by auto
        assume "|vertices f| \<le> 4"
        from this f have "set (vertices f)
          \<inter> set [fst p. p \<leftarrow> deleteAround g a ps] \<subseteq> {a}"
          by (rule deleteAround_separated[OF mgp fin \<open>a : \<V> g\<close>])
        moreover
        have "set (ExcessNotAtRecList (deleteAround g a ps) g)
          \<subseteq> set [fst p. p \<leftarrow> deleteAround g a ps]"
           by (rule ExcessNotAtRecList_subset)
        ultimately
        show "set (vertices f)
           \<inter> set (ExcessNotAtRecList (deleteAround g a ps) g) \<subseteq> {a}"
          by blast
      qed
      with H1 E c show ?thesis by (simp)
    next
      assume "\<not> ExcessNotAtRec ps g
        \<le> b + ExcessNotAtRec (deleteAround g a ps) g"
      with H2 E show ?thesis by simp
    qed
  qed
qed

lemma isTable_ExcessTable:
  "isTable (\<lambda>v. ExcessAt g v) vs (ExcessTable g vs)"
by (auto simp add: isTable_def ExcessTable_def ExcessAt_def)

lemma ExcessTable_subset:
  "set (map fst (ExcessTable g vs)) \<subseteq> set vs"
by (induct vs) (auto simp add: ExcessTable_def)

lemma distinct_ExcessNotAtRecList:
  "distinct (map fst ps) \<Longrightarrow> distinct (ExcessNotAtRecList ps g)"
    (is "?T ps \<Longrightarrow> ?P ps")
proof (induct rule: ExcessNotAtRec.induct)
  case 1 show ?case by simp
next
  case (2 a b ps)
  from 2 have prem: "?T ((a,b)#ps)" by blast
  then have a: "a \<notin> set (map fst ps)" by simp
  from 2 have hyp1: "?T (deleteAround g a ps) \<Longrightarrow>
    ?P (deleteAround g a ps)" by blast
  from 2 have hyp2:  "?T ps \<Longrightarrow> ?P ps" by blast
  from 2 have "?T ps" by simp
  then have H1: "?P (deleteAround g a ps)"
   by (rule_tac hyp1) (rule distinct_deleteAround [simplified])
  from prem have H2: "?P ps"
    by (rule_tac hyp2) simp

  have "a \<notin> set (ExcessNotAtRecList (deleteAround g a ps) g)"(* auto ?? *)
  proof
    assume "a \<in> set (ExcessNotAtRecList (deleteAround g a ps) g)"
    also have "set (ExcessNotAtRecList (deleteAround g a ps) g)
      \<subseteq> set [fst p. p \<leftarrow> deleteAround g a ps]"
     by (rule ExcessNotAtRecList_subset)
    also have "set (deleteAround g a ps) \<subseteq> set ps"
      by (rule deleteAround_subset)
    then have "set [fst p. p \<leftarrow> deleteAround g a ps]
      \<subseteq> set [fst p. p \<leftarrow> ps]" by auto
    finally have "a \<in> set (map fst ps)" by simp
    with a show False by contradiction
  qed
  with H1 H2 show "?P ((a,b)#ps)"
    by ( simp add: ExcessNotAtRecList_subset)
qed

(* alternative definition *)
primrec ExcessTable_cont ::
  "(vertex \<Rightarrow> nat) \<Rightarrow> vertex list \<Rightarrow> (vertex \<times> nat) list"
where
  "ExcessTable_cont ExcessAtPG [] = []" |
  "ExcessTable_cont ExcessAtPG (v#vs) =
   (let vi = ExcessAtPG v in
     if 0 < vi
     then (v, vi)#ExcessTable_cont ExcessAtPG vs
     else ExcessTable_cont ExcessAtPG vs)"

definition ExcessTable' :: "graph \<Rightarrow> vertex list \<Rightarrow> (vertex \<times> nat) list" where
  "ExcessTable' g \<equiv> ExcessTable_cont (ExcessAt g)"



lemma distinct_ExcessTable_cont:
  "distinct vs \<Longrightarrow>
  distinct (map fst (ExcessTable_cont (ExcessAt g) vs))"
proof (induct vs)
  case Nil then show ?case by (simp add: ExcessTable_def)
next
  case (Cons v vs)
  from Cons have v: "v \<notin> set vs" by simp
  from Cons have "distinct vs" by simp
  with Cons have IH:
    "distinct (map fst (ExcessTable_cont (ExcessAt g) vs))"
    by simp
  moreover have
    "v \<notin> fst ` set (ExcessTable_cont (ExcessAt g) vs)"
  proof
    assume "v \<in> fst ` set (ExcessTable_cont (ExcessAt g) vs)"
    also have "fst ` set (ExcessTable_cont (ExcessAt g) vs) \<subseteq> set vs"
      by (induct vs) auto
    finally have " v \<in> set vs" .
    with v show False by contradiction
  qed
  ultimately show ?case by (simp add: ExcessTable_def)
qed


lemma ExcessTable_cont_eq:
 "ExcessTable_cont E vs =
  [(v, E v). v \<leftarrow> [v\<leftarrow>vs . 0 < E v]]"
by (induct vs) (simp_all)


lemma ExcessTable_eq: "ExcessTable = ExcessTable'"
proof (rule ext, rule ext)
  fix p g vs show "ExcessTable g vs = ExcessTable' g vs"
  by (simp add: ExcessTable_def ExcessTable'_def ExcessTable_cont_eq)
qed

lemma distinct_ExcessTable:
   "distinct vs \<Longrightarrow> distinct [fst p. p \<leftarrow> ExcessTable g vs]"
by (simp_all add: ExcessTable_eq ExcessTable'_def distinct_ExcessTable_cont)

lemma ExcessNotAt_eq:
  "minGraphProps g \<Longrightarrow> final g \<Longrightarrow>
  \<exists>V. ExcessNotAt g None
      = (\<Sum>\<^bsub>v \<in> V\<^esub> ExcessAt g v)
   \<and> separated g (set V) \<and> set V \<subseteq> set (vertices g)
   \<and> distinct V"
proof (intro exI conjI)
  assume mgp: "minGraphProps g" and fin: "final g"
  let ?ps = "ExcessTable g (vertices g)"
  let ?V = "ExcessNotAtRecList ?ps g"
  let ?vs = "vertices g"
  let ?E = "\<lambda>v. ExcessAt g v"
  have t: "isTable ?E ?vs ?ps" by (rule isTable_ExcessTable)
  with this show "ExcessNotAt g None = (\<Sum>\<^bsub>v \<in> ?V\<^esub> ?E v)"
    by (simp add: ListSum_ExcessNotAtRecList ExcessNotAt_def)

  show "separated g (set ?V)"
    by(rule separated_ExcessNotAtRecList[OF mgp fin t])

  have "set (ExcessNotAtRecList ?ps g) \<subseteq> set (map fst ?ps)"
    by (rule ExcessNotAtRecList_subset[simplified concat_map_singleton])
  also have "\<dots> \<subseteq> set (vertices g)" by (rule ExcessTable_subset)
  finally show "set ?V \<subseteq> set (vertices g)" .

  show "distinct ?V"
    by (simp add: distinct_ExcessNotAtRecList distinct_ExcessTable[simplified concat_map_singleton])
qed

lemma excess_eq:
  assumes 7: "t + q \<le> 7"
  shows "excessAtType t q 0 + t * \<d> 3 + q * \<d> 4 = \<b> t q"
proof -
  note simps = excessAtType_def squanderVertex_def squanderFace_def
    nat_minus_add_max squanderTarget_def
  from 7 have "q=0 \<or> q=1 \<or> q=2 \<or> q=3 \<or> q=4 \<or> q=5 \<or> q=6 \<or> q=7" by arith
  then show ?thesis
  proof (elim disjE)
    assume q: "q = 0" (* 16 subgoals *)
    with 7 show ?thesis by (simp add: simps)
  next
    assume q: "q = 1" (* 29 subgoals *)
    with 7 show ?thesis by (simp add: simps)
  next
    assume q: "q = 2" (* 16 subgoals *)
    with 7 show ?thesis by (simp add: simps)
  next
    assume q: "q = 3" (* 16 subgoals *)
    with 7 show ?thesis by (simp add: simps)
  next
    assume q: "q = 4" (* 6 subgoals *)
    with 7 show ?thesis by (simp add: simps)
  next
    assume q: "q = 5" (* 1 subgoal *)
    with 7 show ?thesis by (simp add: simps)
  next
    assume q: "q = 6" (* 1 subgoal *)
    with 7 show ?thesis by (simp add: simps)
  next
    assume q: "q = 7" (* 1 subgoal *)
    with 7 show ?thesis by (simp add: simps)
  qed
qed

lemma excess_eq1:
  "\<lbrakk> inv g; final g; tame g; except g v = 0; v \<in> set(vertices g) \<rbrakk> \<Longrightarrow>
   ExcessAt g v + (tri g v) * \<d> 3 + (quad g v) * \<d>  4
   = \<b> (tri g v) (quad g v)"
apply(subgoal_tac "finalVertex g v")
apply(simp add: ExcessAt_def excess_eq faceCountMax_bound)
apply(auto simp:finalVertex_def plane_final_facesAt)
done

text \<open>separating\<close>

definition separating :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> bool" where
  "separating V F \<equiv> 
   (\<forall>v1 \<in> V. \<forall>v2 \<in> V. v1 \<noteq> v2 \<longrightarrow>  F v1 \<inter> F v2 = {})"


lemma separating_insert1: 
  "separating (insert a V) F \<Longrightarrow> separating V F"
  by (simp add: separating_def)

lemma separating_insert2:
  "separating (insert a V) F \<Longrightarrow> a \<notin> V \<Longrightarrow>  v \<in> V \<Longrightarrow> 
  F a \<inter> F v = {}"
  by (auto simp add: separating_def)

lemma sum_disj_Union: 
 "finite V \<Longrightarrow> 
  (\<And>f. finite (F f)) \<Longrightarrow> 
  separating V F \<Longrightarrow> 
  (\<Sum>v\<in>V. \<Sum>f\<in>(F v). (w f::nat)) = (\<Sum>f\<in>(\<Union>v\<in>V. F v). w f)"
proof (induct  rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert a V) 
  then have s: "separating (insert a V) F" by simp
  then have "separating V F" by (rule_tac separating_insert1)
  with insert
  have IH: "(\<Sum>v\<in>V. \<Sum>f\<in>(F v). w f) = (\<Sum>f\<in>(\<Union>v\<in>V. F v). w f)" 
    by simp

  moreover have fin: "finite V" "a \<notin> V" "\<And>f. finite (F f)" by fact+

  moreover from s have "\<And>v. a \<notin> V \<Longrightarrow> v \<in> V \<Longrightarrow> F a \<inter> F v = {}"
   by (simp add: separating_insert2)
  with fin have "(F a) \<inter> (\<Union>v\<in>V. F v) = {}" by auto 

  ultimately show ?case by (simp add: sum.union_disjoint)
qed

lemma separated_separating:
assumes Vg: "set V \<subseteq> \<V> g"
and pS: "separated g (set V)"
and noex: "\<forall>f\<in>P. |vertices f| \<le> 4"
shows "separating (set V) (\<lambda>v. set (facesAt g v) \<inter> P)"
proof -
  from pS have i: "\<forall>v\<in>set V. \<forall>f\<in>set (facesAt g v).
    |vertices f| \<le> 4 \<longrightarrow> set (vertices f) \<inter> set V = {v}"
    by (simp add: separated_def separated\<^sub>3_def)
  show "separating (set V) (\<lambda>v. set (facesAt g v) \<inter> P)"
  proof (simp add: separating_def, intro ballI impI)
    fix v1 v2 assume v: "v1 \<in> set V" "v2 \<in> set V" "v1 \<noteq> v2"
    hence "v1 : \<V> g" using Vg by blast
    show "(set (facesAt g v1) \<inter> P) \<inter> (set (facesAt g v2) \<inter> P) = {}" (is "?P")
    proof (rule ccontr)
      assume "\<not> ?P"
      then obtain f where f1: "f \<in> set (facesAt g v1)"
        and f2: "f \<in> set (facesAt g v2)" and "f : P" by auto
      with noex have l: "|vertices f| \<le> 4" by blast
      from v f1 l i have "set (vertices f) \<inter> set V = {v1}" by simp
      also from v f2 l i
      have "set (vertices f) \<inter> set V = {v2}" by simp
      finally have "v1 = v2" by auto
      then show False by contradiction (rule v)
    qed
  qed
qed

lemma ListSum_V_F_eq_ListSum_F:
assumes pl: "inv g"
and pS: "separated g (set V)" and dist: "distinct V"
and V_subset: "set V \<subseteq> set (vertices g)"
and noex: "\<forall>f \<in> Collect P. |vertices f| \<le> 4"
shows "(\<Sum>\<^bsub>v \<in> V\<^esub> \<Sum>\<^bsub>f \<in> filter P (facesAt g v)\<^esub> (w::face \<Rightarrow> nat) f)
       = (\<Sum>\<^bsub>f \<in> [f\<leftarrow>faces g . \<exists>v \<in> set V. f \<in> set (facesAt g v) \<inter> Collect P]\<^esub> w f)"
proof -
  have s: "separating (set V) (\<lambda>v. set (facesAt g v) \<inter> Collect P)"
    by (rule separated_separating[OF V_subset pS noex])
  moreover note dist
  moreover from pl V_subset
  have "\<And>v. v \<in> set V \<Longrightarrow> distinct (facesAt g v)"
    by(blast intro:mgp_dist_facesAt[OF inv_mgp])
  hence v: "\<And>v. v \<in> set V \<Longrightarrow> distinct (filter P (facesAt g v))"
    by simp
  moreover
  have "distinct [f\<leftarrow>faces g . \<exists>v \<in> set V. f \<in> set (facesAt g v) \<inter> Collect P]"
    by (intro distinct_filter minGraphProps11'[OF inv_mgp[OF pl]])
  moreover from pl have "{x. x \<in> \<F> g \<and> (\<exists>v \<in> set V. x \<in> set (facesAt g v) \<and> P x)} =
      (\<Union>v\<in>set V. set (facesAt g v) \<inter> Collect P)" using V_subset
    by (blast intro:minGraphProps inv_mgp)
  moreover from v have "(\<Sum>v\<in>set V. ListSum (filter P (facesAt g v)) w) = (\<Sum>v\<in>set V. sum w (set(facesAt g v) \<inter> Collect P))"
    by (auto simp add: ListSum_conv_sum Int_def)
  ultimately show ?thesis
    by (simp add: ListSum_conv_sum sum_disj_Union)
qed

lemma separated_disj_Union2:
assumes pl: "inv g" and fin: "final g" and ne: "noExceptionals g (set V)"
and pS: "separated g (set V)" and dist: "distinct V"
and V_subset: "set V \<subseteq> set (vertices g)"
shows "(\<Sum>\<^bsub>v \<in> V\<^esub> \<Sum>\<^bsub>f \<in> facesAt g v\<^esub> (w::face \<Rightarrow> nat) f)
       = (\<Sum>\<^bsub>f \<in> [f\<leftarrow>faces g . \<exists>v \<in> set V. f \<in> set (facesAt g v)]\<^esub> w f)"
proof -
  let ?P = "\<lambda>f. |vertices f| \<le> 4"
  have "\<forall>v \<in> set V. \<forall>f \<in> set (facesAt g v). |vertices f| \<le> 4"
    using V_subset ne
    by (auto simp: noExceptionals_def
      intro: minGraphProps5[OF inv_mgp[OF pl]] not_exceptional[OF pl fin])
  thus ?thesis
    using ListSum_V_F_eq_ListSum_F[where P = ?P, OF pl pS dist V_subset]
    by (simp add: Int_def cong: conj_cong)
qed

lemma squanderFace_distr2: "inv g \<Longrightarrow> final g \<Longrightarrow> noExceptionals g (set V) \<Longrightarrow>
  separated g (set V) \<Longrightarrow> distinct V \<Longrightarrow> set V \<subseteq> set (vertices g) \<Longrightarrow>
     (\<Sum>\<^bsub>f \<in> [f\<leftarrow>faces g. \<exists>v \<in> set V. f \<in> set (facesAt g v)]\<^esub>
         \<d> |vertices f| )
   = (\<Sum>\<^bsub>v \<in> V\<^esub> ((tri g v) * \<d> 3
         + (quad g v) * \<d> 4))"
proof -
  assume pl: "inv g"
  assume fin: "final g"
  assume ne: "noExceptionals g (set V)"
  assume "separated g (set V)"  "distinct V" and V_subset: "set V \<subseteq> set (vertices g)"
  with pl ne fin have
    "(\<Sum>\<^bsub>f \<in> [f\<leftarrow>faces g. \<exists>v\<in>set V. f\<in>set (facesAt g v)]\<^esub> \<d> |vertices f| )
   = (\<Sum>\<^bsub>v \<in> V\<^esub> \<Sum>\<^bsub>f \<in> facesAt g v\<^esub> \<d> |vertices f| )"
    by (simp add: separated_disj_Union2)
  also have "\<And>v. v \<in> set V \<Longrightarrow>
    (\<Sum>\<^bsub>f \<in> facesAt g v\<^esub> \<d> |vertices f| )
  = (tri g v) * \<d> 3 + (quad g v) * \<d> 4"
  proof -
    fix v assume v1: "v \<in> set V"
    with V_subset have v: "v \<in> set (vertices g)" by auto

    with ne have d:
      "\<And>f. f \<in> set (facesAt g v) \<Longrightarrow>
      |vertices f| = 3 \<or> |vertices f| = 4"
    proof -
      fix f assume f: "f \<in> set (facesAt g v)"
      then have ff: "f \<in> set (faces g)" by (rule minGraphProps5[OF inv_mgp[OF pl] v])
      with ne f v1 pl fin v have "|vertices f| \<le> 4"
        by (auto simp add: noExceptionals_def not_exceptional)
      moreover from pl ff have "3 \<le> |vertices f|" by(rule planeN4)
      ultimately show "?thesis f" by arith
    qed

    from d pl v have
      "(\<Sum>\<^bsub>f \<in> facesAt g v\<^esub> \<d> |vertices f| )
    = (\<Sum>\<^bsub>f\<in>[f \<leftarrow> facesAt g v. |vertices f| = 3]\<^esub> \<d> |vertices f| )
    + (\<Sum>\<^bsub>f\<in>[f \<leftarrow> facesAt g v. |vertices f| = 4]\<^esub> \<d> |vertices f| )"
      apply (rule_tac ListSum_disj_union)
      apply (rule distinct_filter) apply simp
      apply (rule distinct_filter) apply simp
      apply simp
      apply force
      apply force
      done
    also have "\<dots> = tri g v * \<d> 3 + quad g v * \<d> 4"
    proof -
      from pl fin v have "\<And>A.[f \<leftarrow> facesAt g v. final f \<and> A f]
        = [f \<leftarrow> facesAt g v. A f]"
        by (rule_tac filter_eqI) (auto simp:plane_final_facesAt)
      with fin show ?thesis  by (auto simp add: tri_def quad_def)
    qed
    finally show "(\<Sum>\<^bsub>f \<in> facesAt g v\<^esub> \<d> |vertices f| ) = tri g v * \<d> 3 + quad g v * \<d> 4" .
  qed
  then have "(\<Sum>\<^bsub>v \<in> V\<^esub> \<Sum>\<^bsub>f \<in> facesAt g v\<^esub> \<d> |vertices f| ) =
         (\<Sum>\<^bsub>v \<in> V\<^esub> (tri g v * \<d> 3 + quad g v * \<d> 4))"
     by (rule ListSum_eq)
  finally show ?thesis .
qed



lemma separated_subset: (* separated *)
   "V1 \<subseteq> V2 \<Longrightarrow> separated g V2 \<Longrightarrow> separated g V1"
proof (simp add:  separated_def separated\<^sub>3_def separated\<^sub>2_def,
  elim conjE, intro allI impI ballI conjI)
  fix v f
  assume a: "v \<in> V1" "V1 \<subseteq> V2" "f \<in> set (facesAt g v)"
    "|vertices f| \<le> 4"
    "\<forall>v\<in>V2. \<forall>f\<in>set (facesAt g v). |vertices f| \<le> 4 \<longrightarrow>
      set (vertices f) \<inter> V2 = {v}"
  then show "set (vertices f) \<inter> V1 = {v}" by auto
next
  fix v f
  assume a: "v \<in> V1" "V1 \<subseteq> V2" "f \<in> set (facesAt g v)"
    "\<forall>v\<in>V2. \<forall>f\<in>set (facesAt g v). f \<bullet> v \<notin> V2"
  then have "v \<in> V2" by auto
  with a have "f \<bullet> v \<notin> V2" by auto
  with a show "f \<bullet> v \<notin> V1" by auto
qed

end
