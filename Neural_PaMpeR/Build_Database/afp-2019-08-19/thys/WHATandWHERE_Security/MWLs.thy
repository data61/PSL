(*
Title: WHATandWHERE-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory MWLs
imports Strong_Security.Types
begin

\<comment> \<open>type parameters not instantiated:\<close>
\<comment> \<open>'exp: expressions (arithmetic, boolean...)\<close>
\<comment> \<open>'val: numbers, boolean constants....\<close>
\<comment> \<open>'id: identifier names\<close>

\<comment> \<open>SYNTAX\<close>

datatype ('exp, 'id) MWLsCom
  = Skip "nat" ("skip\<^bsub>_\<^esub>" [50] 70)
  | Assign "'id" "nat" "'exp"
       ("_:=\<^bsub>_\<^esub> _" [70,50,70] 70)

  | Seq "('exp, 'id) MWLsCom"
         "('exp, 'id) MWLsCom"
       ("_;_" [61,60] 60)

  | If_Else "nat" "'exp" "('exp, 'id) MWLsCom"
         "('exp, 'id) MWLsCom"
       ("if\<^bsub>_\<^esub> _ then _ else _ fi" [50,80,79,79] 70)

  | While_Do "nat" "'exp" "('exp, 'id) MWLsCom"
       ("while\<^bsub>_\<^esub> _ do _ od" [50,80,79] 70)

  | Spawn "nat" "(('exp, 'id) MWLsCom) list"
       ("spawn\<^bsub>_\<^esub> _" [50,70] 70)

\<comment> \<open>function for obtaining the program point of some MWLsloc command\<close>
primrec pp ::"('exp, 'id) MWLsCom \<Rightarrow> nat"
where
"pp (skip\<^bsub>\<iota>\<^esub>) = \<iota>" |
"pp (x :=\<^bsub>\<iota>\<^esub> e) = \<iota>" |
"pp (c1;c2) = pp c1" |
"pp (if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi) = \<iota>" |
"pp (while\<^bsub>\<iota>\<^esub> b do c od) = \<iota>" |
"pp (spawn\<^bsub>\<iota>\<^esub> V) = \<iota>"

\<comment> \<open>mutually recursive functions to collect program points of commands and thread pools\<close>
primrec PPc :: "('exp,'id) MWLsCom \<Rightarrow> nat list"
and PPV :: "('exp,'id) MWLsCom list \<Rightarrow> nat list"
where
"PPc (skip\<^bsub>\<iota>\<^esub>) = [\<iota>]" |
"PPc (x :=\<^bsub>\<iota>\<^esub> e) = [\<iota>]" |
"PPc (c1;c2) = (PPc c1) @ (PPc c2)" |
"PPc (if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi) =  [\<iota>] @ (PPc c1) @ (PPc c2)" |
"PPc (while\<^bsub>\<iota>\<^esub> b do c od) = [\<iota>] @ (PPc c)" |
"PPc (spawn\<^bsub>\<iota>\<^esub> V) = [\<iota>] @ (PPV V)" |

"PPV [] = []" |
"PPV (c#V) = (PPc c) @ (PPV V)"

\<comment> \<open>predicate indicating that a command only contains unique program points\<close>
definition unique_PPc :: "('exp, 'id) MWLsCom \<Rightarrow> bool"
where
"unique_PPc c = distinct (PPc c)"

\<comment> \<open>predicate indicating that a thread pool only contains unique program points\<close>
definition unique_PPV :: "('exp, 'id) MWLsCom list \<Rightarrow> bool"
where
"unique_PPV V = distinct (PPV V)"

lemma PPc_nonempt: "PPc c \<noteq> []"
  by (induct c) auto

lemma unique_c_uneq: "set (PPc c) \<inter> set (PPc c') = {} \<Longrightarrow> c \<noteq> c'"
  by (insert PPc_nonempt, force)

lemma V_nonempt_PPV_nonempt: "V \<noteq> [] \<Longrightarrow> PPV V \<noteq> []"
  by (auto, induct V, simp_all, insert PPc_nonempt, force)

lemma unique_V_uneq:
"\<lbrakk>V \<noteq> []; V' \<noteq> []; set (PPV V) \<inter> set (PPV V') = {}\<rbrakk> \<Longrightarrow> V \<noteq> V'"
  by (auto, induct V, simp_all, insert V_nonempt_PPV_nonempt, auto)

lemma PPc_in_PPV: "c \<in> set V \<Longrightarrow> set (PPc c) \<subseteq> set (PPV V)"
  by (induct V, auto)

lemma listindices_aux: "i < length V \<Longrightarrow> (V!i) \<in> set V"
  by (metis nth_mem)

lemma PPc_in_PPV_version:
  "i < length V \<Longrightarrow> set (PPc (V!i)) \<subseteq> set (PPV V)"
  by (rule PPc_in_PPV, erule listindices_aux)

lemma uniPPV_uniPPc: "unique_PPV V \<Longrightarrow> (\<forall>i < length V. unique_PPc (V!i))"
  by (auto, simp add: unique_PPV_def, induct V,
    auto simp add: unique_PPc_def,
    metis in_set_conv_nth length_Suc_conv set_ConsD)

\<comment> \<open>SEMANTICS\<close>

locale MWLs_semantics =
fixes E :: "('exp, 'id, 'val) Evalfunction"
and BMap :: "'val \<Rightarrow> bool"
begin

\<comment> \<open>steps semantics, set of deterministic steps from commands to program states\<close>
inductive_set
MWLsSteps_det ::
  "('exp, 'id, 'val, ('exp, 'id) MWLsCom) TLSteps"
and MWLslocSteps_det' ::
  "('exp, 'id, 'val, ('exp, 'id) MWLsCom) TLSteps_curry"
("(1\<langle>_,/_\<rangle>) \<rightarrow>\<lhd>_\<rhd>/ (1\<langle>_,/_\<rangle>)" [0,0,0,0,0] 81)
where
"\<langle>c1,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>c2,m2\<rangle> \<equiv> ((c1,m1),\<alpha>,(c2,m2)) \<in> MWLsSteps_det" |
skip: "\<langle>skip\<^bsub>\<iota>\<^esub>,m\<rangle> \<rightarrow>\<lhd>[]\<rhd> \<langle>None,m\<rangle>" |
assign: "(E e m) = v \<Longrightarrow>
  \<langle>x :=\<^bsub>\<iota>\<^esub> e,m\<rangle> \<rightarrow>\<lhd>[]\<rhd> \<langle>None,m(x := v)\<rangle>" |
seq1: "\<langle>c1,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>None,m'\<rangle> \<Longrightarrow>
  \<langle>c1;c2,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>Some c2,m'\<rangle>" |
seq2: "\<langle>c1,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>Some c1',m'\<rangle> \<Longrightarrow>
  \<langle>c1;c2,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>Some (c1';c2),m'\<rangle>" |
iftrue: "BMap (E b m) = True \<Longrightarrow>
  \<langle>if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi,m\<rangle> \<rightarrow>\<lhd>[]\<rhd> \<langle>Some c1,m\<rangle>" |
iffalse: "BMap (E b m) = False \<Longrightarrow>
  \<langle>if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi,m\<rangle> \<rightarrow>\<lhd>[]\<rhd> \<langle>Some c2,m\<rangle>" |
whiletrue: "BMap (E b m) = True \<Longrightarrow>
  \<langle>while\<^bsub>\<iota>\<^esub> b do c od,m\<rangle> \<rightarrow>\<lhd>[]\<rhd> \<langle>Some (c;(while\<^bsub>\<iota>\<^esub> b do c od)),m\<rangle>" |
whilefalse: "BMap (E b m) = False \<Longrightarrow>
  \<langle>while\<^bsub>\<iota>\<^esub> b do c od,m\<rangle> \<rightarrow>\<lhd>[]\<rhd> \<langle>None,m\<rangle>" |
spawn: "\<langle>spawn\<^bsub>\<iota>\<^esub> V,m\<rangle> \<rightarrow>\<lhd>V\<rhd> \<langle>None,m\<rangle>"

inductive_cases MWLsSteps_det_cases:
"\<langle>skip\<^bsub>\<iota>\<^esub>,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>"
"\<langle>x :=\<^bsub>\<iota>\<^esub> e,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>"
"\<langle>c1;c2,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>"
"\<langle>if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>"
"\<langle>while\<^bsub>\<iota>\<^esub> b do c od,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>"
"\<langle>spawn\<^bsub>\<iota>\<^esub> V,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>"

\<comment> \<open>non-deterministic, possibilistic system step (added for intuition, not used in the proofs)\<close>
inductive_set
MWLsSteps_ndet ::
  "('exp, 'id, 'val, ('exp, 'id) MWLsCom) TPSteps"
and MWLsSteps_ndet' ::
  "('exp, 'id, 'val, ('exp, 'id) MWLsCom) TPSteps_curry"
("(1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>)" [0,0,0,0] 81)
where
"\<langle>V,m\<rangle> \<Rightarrow> \<langle>V',m'\<rangle> \<equiv> ((V,m),(V',m')) \<in> MWLsSteps_ndet" |
stepthreadi1: "\<langle>ci,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>None,m'\<rangle> \<Longrightarrow>
  \<langle>cf @ [ci] @ ca,m\<rangle> \<Rightarrow> \<langle>cf @ \<alpha> @ ca,m'\<rangle>" |
stepthreadi2: "\<langle>ci,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>Some c',m'\<rangle> \<Longrightarrow>
  \<langle>cf @ [ci] @ ca,m\<rangle> \<Rightarrow> \<langle>cf @ [c'] @ \<alpha> @ ca,m\<rangle>"


\<comment> \<open>lemma about existence and uniqueness of next memory of a step\<close>
lemma nextmem_exists_and_unique:
"\<exists>m' p \<alpha>. \<langle>c,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>
  \<and> (\<forall>m''. (\<exists>p \<alpha>. \<langle>c,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m''\<rangle>) \<longrightarrow> m'' = m')"
  by (induct c, auto, metis MWLsSteps_det.skip MWLsSteps_det_cases(1),
    metis MWLsSteps_det_cases(2) MWLsSteps_det.assign,
    metis (no_types) MWLsSteps_det.seq1 MWLsSteps_det.seq2
    MWLsSteps_det_cases(3) not_Some_eq,
    metis MWLsSteps_det.iffalse MWLsSteps_det.iftrue
    MWLsSteps_det_cases(4),
    metis MWLsSteps_det.whilefalse MWLsSteps_det.whiletrue
    MWLsSteps_det_cases(5),
    metis MWLsSteps_det.spawn MWLsSteps_det_cases(6))

lemma PPsc_of_step:
"\<lbrakk> \<langle>c,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>; \<exists>c'. p = Some c' \<rbrakk>
  \<Longrightarrow> set (PPc (the p)) \<subseteq> set (PPc c)"
  by (induct rule: MWLsSteps_det.induct, auto)

lemma PPs\<alpha>_of_step:
"\<langle>c,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>
  \<Longrightarrow> set (PPV \<alpha>) \<subseteq> set (PPc c)"
  by (induct rule: MWLsSteps_det.induct, auto)


end

end
