(*  Title:       AWN_Term_Graph.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)
theory AWN_Term_Graph
imports AWN_Cterms
begin

datatype ('p, 'l) node =
    RootNode 'p
  | InternalNode 'l

datatype ('p, 'l) link =
    ILink "('p, 'l) node" "('p, 'l) node"
  | ELink "('p, 'l) node" "('p, 'l) node"

definition gseqp'_fails where "gseqp'_fails = []"
declare [[code abort: gseqp'_fails]]

fun gseqp'
  :: "('s, 'm, 'p, 'l) seqp_env \<Rightarrow> ('s, 'm, 'p, 'l) seqp \<Rightarrow> ('p, 'l) node list"
where
    "gseqp' \<Gamma> ({l}\<langle>_\<rangle> _)                = [InternalNode l]"
  | "gseqp' \<Gamma> ({l}\<lbrakk>_\<rbrakk> _)                = [InternalNode l]"
  | "gseqp' \<Gamma> ({l}unicast(_, _)._ \<triangleright> _) = [InternalNode l]"
  | "gseqp' \<Gamma> ({l}broadcast(_). _)     = [InternalNode l]"
  | "gseqp' \<Gamma> ({l}groupcast(_, _). _)  = [InternalNode l]"
  | "gseqp' \<Gamma> ({l}send(_)._)           = [InternalNode l]"
  | "gseqp' \<Gamma> ({l}deliver(_)._)        = [InternalNode l]"
  | "gseqp' \<Gamma> ({l}receive(_)._)        = [InternalNode l]"
  | "gseqp' \<Gamma> (p1 \<oplus> p2)                = gseqp' \<Gamma> p1 @ gseqp' \<Gamma> p2"
  | "gseqp' \<Gamma> (call(pn))               = gseqp'_fails"
(*
(* It would be better to define this function for all wellformed \<Gamma>, as shown
   below, but I can't get the code generator to work smoothly with the
   conditional simp rules. *)

  | "gseqp' \<Gamma> (call(pn))               = gseqp' \<Gamma> (\<Gamma> pn)"
  by pat_completeness auto

lemma gseqp'_termination:
  assumes "wellformed \<Gamma>"
    shows "gseqp'_dom (\<Gamma>, p)"
  proof -
    have gseqp'_rel':
      "gseqp'_rel = (\<lambda>gq gp. (gq, gp) \<in> {((\<Gamma>, q), (\<Gamma>', p)). \<Gamma> = \<Gamma>' \<and> p \<leadsto>\<^bsub>\<Gamma>\<^esub> q})"
      by (rule ext)+ (auto simp: gseqp'_rel.simps elim: microstep.cases)

    from assms have "\<forall>x. x \<in> acc {(q, p). p \<leadsto>\<^bsub>\<Gamma>\<^esub> q}"
      unfolding wellformed_def by (simp add: wf_acc_iff)
    hence "p \<in> acc {(q, p). p \<leadsto>\<^bsub>\<Gamma>\<^esub> q}" ..

    hence "(\<Gamma>, p) \<in> acc {((\<Gamma>, q), (\<Gamma>', p)). \<Gamma> = \<Gamma>' \<and> p \<leadsto>\<^bsub>\<Gamma>\<^esub> q}"
      by (rule acc_induct) (auto intro: accI)

    thus "gseqp'_dom (\<Gamma>, p)" unfolding gseqp'_rel' accp_acc_eq .
  qed

declare gseqp'.psimps [simp, code del]
lemmas gseqp'_psimps[simp] = gseqp'.psimps [OF gseqp'_termination]
   and gseqp'_pinduct = gseqp'.pinduct [OF gseqp'_termination]
*)

fun gseqp :: "('s, 'm, 'p, 'l) seqp_env \<Rightarrow> ('s, 'm, 'p, 'l) seqp
              \<Rightarrow> ('p, 'l) node list * ('p, 'l) node list * ('p, 'l) link list"
where
    "gseqp \<Gamma> ({l}\<langle>_\<rangle> p)                = (let me = InternalNode l in
                                          let (next, acc, links) = gseqp \<Gamma> p in
                                          ([me], me # acc, map (ILink me) next @ links))"
  | "gseqp \<Gamma> ({l}\<lbrakk>_\<rbrakk> p)                = (let me = InternalNode l in
                                          let (next, acc, links) = gseqp \<Gamma> p in
                                          ([me], me # acc, map (ILink me) next @ links))"
  | "gseqp \<Gamma> (p1 \<oplus> p2)                = (let (next1, acc1, links1) = gseqp \<Gamma> p1 in
                                          let (next2, acc2, links2) = gseqp \<Gamma> p2 in
                                          (next1 @ next2, acc1 @ acc2, links1 @ links2))"
  | "gseqp \<Gamma> ({l}unicast(_, _).p \<triangleright> q) = (let me = InternalNode l in
                                          let (next1, acc1, links1) = gseqp \<Gamma> p in
                                          let (next2, acc2, links2) = gseqp \<Gamma> q in
                                          ([me], me # acc1 @ acc2,
                                        map (ELink me) (next1 @ next2) @ links1 @ links2))"
  | "gseqp \<Gamma> ({l}broadcast(_). p)     = (let me = InternalNode l in
                                          let (next, acc, links) = gseqp \<Gamma> p in
                                         ([me], me # acc, map (ELink me) next @ links))"
  | "gseqp \<Gamma> ({l}groupcast(_, _). p)  = (let me = InternalNode l in
                                          let (next, acc, links) = gseqp \<Gamma> p in
                                          ([me], me # acc, map (ELink me) next @ links))"
  | "gseqp \<Gamma> ({l}send(_).p)           = (let me = InternalNode l in
                                          let (next, acc, links) = gseqp \<Gamma> p in
                                          ([me], me # acc, map (ELink me) next @ links))"
  | "gseqp \<Gamma> ({l}deliver(_).p)        = (let me = InternalNode l in
                                          let (next, acc, links) = gseqp \<Gamma> p in
                                          ([me], me # acc, map (ELink me) next @ links))"
  | "gseqp \<Gamma> ({l}receive(_).p)        = (let me = InternalNode l in
                                          let (next, acc, links) = gseqp \<Gamma> p in
                                          ([me], me # acc, map (ELink me) next @ links))"
  | "gseqp \<Gamma> (call(pn))               = (gseqp' \<Gamma> (\<Gamma> pn), [], [])"

definition graph_of_other :: "('s, 'm, 'p, 'l) seqp_env
                              \<Rightarrow> (('p, 'l) node list * ('p, 'l) link list)
                              \<Rightarrow> 'p
                              \<Rightarrow> ('p, 'l) node list * ('p, 'l) link list"
where
  "graph_of_other \<Gamma> r pn = (let (next, acc, links) = gseqp \<Gamma> (\<Gamma> pn) in
                            (acc @ fst r, links @ snd r))"

definition graph_of_root :: "('s, 'm, 'p, 'l) seqp_env
                             \<Rightarrow> (('p, 'l) node list * ('p, 'l) link list)
                             \<Rightarrow> 'p
                             \<Rightarrow> ('p, 'l) node list * ('p, 'l) link list"
where
  "graph_of_root \<Gamma> r pn = (let me = RootNode pn in
                           let (next, acc, links) = gseqp \<Gamma> (\<Gamma> pn) in
                           (acc @ fst r @ [me], map (ILink me) next @ links @ snd r))"

definition graph_of_seqp :: "('s, 'm, 'p, 'l) seqp_env
                             \<Rightarrow> 'p list
                             \<Rightarrow> ('p, 'l) node list * ('p, 'l) link list"
where
  "graph_of_seqp \<Gamma> pns = map_prod (rev \<circ> remdups) remdups
                           (foldl (graph_of_other \<Gamma>) (graph_of_root \<Gamma> ([], []) (hd pns)) (tl pns))"

definition graph_of_seqps :: "('s, 'm, 'p, 'l) seqp_env
                              \<Rightarrow> 'p list
                              \<Rightarrow> ('p, 'l) node list * ('p, 'l) link list"
where
  "graph_of_seqps \<Gamma> pns = map_prod (rev \<circ> remdups) remdups (foldl (graph_of_root \<Gamma>) ([], [])
                                   (List.rev pns))"

end
