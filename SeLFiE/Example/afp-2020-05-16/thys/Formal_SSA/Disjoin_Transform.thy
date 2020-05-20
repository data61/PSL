(*  Title:      Disjoin_Transform.thy
    Author:     Sebastian Ullrich
*)

theory Disjoin_Transform imports
Slicing.AdditionalLemmas
begin

inductive subcmd :: "cmd \<Rightarrow> cmd \<Rightarrow> bool" where
  sub_Skip: "subcmd c Skip"
| sub_Base: "subcmd c c"
| sub_Seq1: "subcmd c1 c \<Longrightarrow> subcmd (c1;;c2) c"
| sub_Seq2: "subcmd c2 c \<Longrightarrow> subcmd (c1;;c2) c"
| sub_If1: "subcmd c1 c \<Longrightarrow> subcmd (if (b) c1 else c2) c"
| sub_If2:"subcmd c2 c \<Longrightarrow> subcmd (if (b) c1 else c2) c"
| sub_While: "subcmd c' c \<Longrightarrow> subcmd (while (b) c') c"

fun maxVnameLen_aux :: "expr \<Rightarrow> nat" where
  "maxVnameLen_aux (Val _ ) = 0"
| "maxVnameLen_aux (Var V) = length V"
| "maxVnameLen_aux (e1 \<guillemotleft> _ \<guillemotright> e2) = max (maxVnameLen_aux e1) (maxVnameLen_aux e2)"

fun maxVnameLen :: "cmd \<Rightarrow> nat" where
  "maxVnameLen Skip = 0"
| "maxVnameLen (V:=e) = max (length V) (maxVnameLen_aux e)"
| "maxVnameLen (c\<^sub>1;;c\<^sub>2) = max (maxVnameLen c\<^sub>1) (maxVnameLen c\<^sub>2)"
| "maxVnameLen (if (b) c\<^sub>1 else c\<^sub>2) = max (maxVnameLen c\<^sub>1) (max (maxVnameLen_aux b) (maxVnameLen c\<^sub>2))"
| "maxVnameLen (while (b) c) = max (maxVnameLen c) (maxVnameLen_aux b)"

definition tempName :: "cmd \<Rightarrow> vname" where "tempName c \<equiv> replicate (Suc (maxVnameLen c)) (CHR ''a'')"

inductive newname :: "cmd \<Rightarrow> vname \<Rightarrow> bool" where
  "newname Skip V"
| "V \<notin> {V'} \<union> rhs_aux e \<Longrightarrow> newname (V':=e) V"
| "\<lbrakk>newname c1 V; newname c2 V\<rbrakk> \<Longrightarrow> newname (c1;;c2) V"
| "\<lbrakk>newname c1 V; newname c2 V; V \<notin> rhs_aux b\<rbrakk> \<Longrightarrow> newname (if (b) c1 else c2) V"
| "\<lbrakk>newname c V; V \<notin> rhs_aux b\<rbrakk> \<Longrightarrow> newname (while (b) c) V"

lemma maxVnameLen_aux_newname: "length V > maxVnameLen_aux e \<Longrightarrow> V \<notin> rhs_aux e"
by (induction e) auto

lemma maxVnameLen_newname: "length V > maxVnameLen c \<Longrightarrow> newname c V"
by (induction c) (auto intro:newname.intros dest:maxVnameLen_aux_newname)

lemma tempname_newname[intro]: "newname c (tempName c)"
  by (rule maxVnameLen_newname) (simp add: tempName_def)

fun transform_aux :: "vname \<Rightarrow> cmd \<Rightarrow> cmd" where
  "transform_aux _ Skip = Skip"
| "transform_aux V' (V:=e) =
    (if V \<in> rhs (V:=e) then V':=e;; V:=Var V'
     else V:=e)"
| "transform_aux V' (c\<^sub>1;;c\<^sub>2) = transform_aux V' c\<^sub>1;; transform_aux V' c\<^sub>2"
| "transform_aux V' (if (b) c\<^sub>1 else c\<^sub>2) =
    (if (b) transform_aux V' c\<^sub>1 else transform_aux V' c\<^sub>2)"
| "transform_aux V' (while (b) c) = (while (b) transform_aux V' c)"

abbreviation transform :: "cmd \<Rightarrow> cmd" where
  "transform c \<equiv> transform_aux (tempName c) c"

fun leftmostCmd :: "cmd \<Rightarrow> cmd" where
  "leftmostCmd (c1;;c2) = leftmostCmd c1"
| "leftmostCmd c = c"

lemma leftmost_lhs[simp]: "lhs (leftmostCmd c) = lhs c"
by (induction c) auto

lemma leftmost_rhs[simp]: "rhs (leftmostCmd c) = rhs c"
by (induction c) auto

lemma leftmost_subcmd[intro]: "subcmd c (leftmostCmd c)"
by (induction c) (auto intro:subcmd.intros)

lemma leftmost_labels: "labels c n c' \<Longrightarrow> subcmd c (leftmostCmd c')"
by (induction rule:labels.induct) (auto intro:subcmd.intros)

theorem transform_disjoint:
  assumes "subcmd (transform_aux temp c) (V:=e)" "newname c temp"
  shows "V \<notin> rhs_aux e"
using assms proof (induction c rule:transform_aux.induct)
  case (3 V c1 c2)
  from "3.prems"(1) show ?case
  apply simp
  proof (cases "(transform_aux temp c1;; transform_aux temp c2)" "(V:=e)" rule:subcmd.cases)
    case sub_Seq2
    with "3.prems"(2) show ?thesis by -(rule "3.IH"(1), auto elim:newname.cases)
  next
    case sub_If1
    with "3.prems"(2) show ?thesis by -(rule "3.IH"(2), auto elim:newname.cases)
  qed auto
next
  case (4 V b c1 c2)
  from "4.prems"(1) show ?case
  apply simp
  proof (cases "(if (b) transform_aux temp c1 else transform_aux temp c2)" "(V:=e)" rule:subcmd.cases)
    case sub_If2
    with "4.prems"(2) show ?thesis by -(rule "4.IH"(1), auto elim:newname.cases)
  next
    case sub_While
    with "4.prems"(2) show ?thesis by -(rule "4.IH"(2), auto elim:newname.cases)
  qed auto
next
  case 5
  from "5.prems" show ?case by -(rule "5.IH", auto elim:subcmd.cases newname.cases)
qed (auto elim!:subcmd.cases newname.cases split:if_split_asm)

lemma transform_disjoint': "subcmd (transform c) (leftmostCmd c') \<Longrightarrow> lhs c' \<inter> rhs c' = {}"
  by (induction c') (auto dest: transform_disjoint)

corollary Defs_Uses_transform_disjoint [simp]: "Defs (transform c) n \<inter> Uses (transform c) n = {}"
  by (auto dest: leftmost_labels transform_disjoint' labels_det)

end

