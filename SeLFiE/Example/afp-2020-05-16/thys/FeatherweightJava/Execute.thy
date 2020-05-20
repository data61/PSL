(*  Author:      Lukas Bulwahn, TU Muenchen, 2009  *)

theory Execute
imports FJSound
begin

section \<open>Executing FeatherweightJava programs\<close>
text \<open>We execute FeatherweightJava programs using the predicate compiler.\<close>

code_pred (modes: i => i => i => bool,
  i => i => o => bool as supertypes_of) subtyping .

thm subtyping.equation

text \<open>The reduction relation requires that we inverse the @{term List.append} function.
Therefore, we define a new predicate append and derive introduction rules.\<close>

definition append where "append xs ys zs = (zs = xs @ ys)"

lemma [code_pred_intro]: "append [] xs xs"
unfolding append_def by simp

lemma [code_pred_intro]: "append xs ys zs \<Longrightarrow> append (x#xs) ys (x#zs)"
unfolding append_def by simp

text \<open>With this at hand, we derive new introduction rules for the reduction relation:\<close>

lemma rc_invk_arg': "CT \<turnstile> ei \<rightarrow> ei' \<Longrightarrow> append el (ei # er) e' \<Longrightarrow> append el (ei' # er) e'' \<Longrightarrow>
CT \<turnstile> MethodInvk e m e' \<rightarrow> MethodInvk e m e''"
unfolding append_def by simp (rule reduction.intros(6))

lemma rc_new_arg': "CT \<turnstile> ei \<rightarrow> ei' \<Longrightarrow> append el (ei # er) e \<Longrightarrow> append el (ei' # er) e'
   ==> CT \<turnstile> New C e \<rightarrow> New C e'"
unfolding append_def by simp (rule reduction.intros(7))

lemmas [code_pred_intro] = reduction.intros(1-5)
  rc_invk_arg' rc_new_arg' reduction.intros(8)

code_pred (modes: i => i => i => bool, i => i => o => bool as reduce) reduction
proof -
  case append
  from this show thesis
    unfolding append_def by (cases xa) fastforce+
next
  case reduction
  from reduction.prems show thesis
  proof (cases rule: reduction.cases)
    case r_field
    with reduction(1) show thesis by fastforce
  next
    case r_invk
    with reduction(2) show thesis by fastforce
  next
    case r_cast
    with reduction(3) show thesis by fastforce
  next
    case rc_field
    with reduction(4) show thesis by fastforce
  next
    case rc_invk_recv
    with reduction(5) show thesis by fastforce
  next
    case rc_invk_arg
    with reduction(6) show thesis
      unfolding append_def by fastforce
  next
    case rc_new_arg
    with reduction(7) show thesis
      unfolding append_def by fastforce
  next
    case rc_cast
    with reduction(8) show thesis by fastforce
  qed
qed

thm reduction.equation

code_pred reductions .

thm reductions.equation

text \<open>We also make the class typing executable: this requires that
  we derive rules for @{term "method_typing"}.\<close>

definition method_typing_aux
where
  "method_typing_aux CT m D Cs C = (\<not> (\<forall>Ds D0. mtype(CT,m,D) = Ds \<rightarrow> D0 \<longrightarrow> Cs = Ds \<and> C = D0))"

lemma method_typing_aux:
  "(\<forall>Ds D0. mtype(CT,m,D) = Ds \<rightarrow> D0 \<longrightarrow> Cs = Ds \<and> C = D0) = (\<not> method_typing_aux CT m D Cs C)"
unfolding method_typing_aux_def by auto

lemma [code_pred_intro]:
  "mtype(CT,m,D) = Ds \<rightarrow> D0 \<Longrightarrow> Cs \<noteq> Ds \<Longrightarrow> method_typing_aux CT m D Cs C"
unfolding method_typing_aux_def by auto

lemma [code_pred_intro]:
  "mtype(CT,m,D) = Ds \<rightarrow> D0 \<Longrightarrow> C \<noteq> D0 \<Longrightarrow> method_typing_aux CT m D Cs C"
unfolding method_typing_aux_def by auto

declare method_typing.intros[unfolded method_typing_aux, code_pred_intro]

declare class_typing.intros[unfolded append_def[symmetric], code_pred_intro]

code_pred (modes: i => i => bool) class_typing
proof -
  case class_typing
  from class_typing.cases[OF class_typing.prems, of thesis] this(1) show thesis
    unfolding append_def by fastforce
next
  case method_typing
  from method_typing.cases[OF method_typing.prems, of thesis] this(1) show thesis
    unfolding append_def method_typing_aux_def by fastforce
next
  case method_typing_aux
  from this show thesis
    unfolding method_typing_aux_def by auto
qed

subsection \<open>A simple example\<close>

text \<open>We now execute a simple FJ example program:\<close>

abbreviation A :: className
where "A == Suc 0"

abbreviation B :: className
where "B == 2"

abbreviation cPair :: className
where "cPair == 3"

definition classA_Def :: classDef
where
  "classA_Def = \<lparr> cName = A, cSuper = Object, cFields = [], cConstructor = \<lparr>kName = A, kParams = [], kSuper = [], kInits = []\<rparr>, cMethods = []\<rparr>"

definition
  "classB_Def = \<lparr> cName = B, cSuper = Object, cFields = [], cConstructor = \<lparr>kName = B, kParams = [], kSuper = [], kInits = []\<rparr>, cMethods = []\<rparr>"

abbreviation ffst :: varName
where
  "ffst == 4"

abbreviation fsnd :: varName
where
  "fsnd == 5"

abbreviation setfst :: methodName
where
  "setfst == 6"

abbreviation newfst :: varName
where
  "newfst == 7"

definition classPair_Def :: classDef
where
  "classPair_Def = \<lparr> cName = cPair, cSuper = Object,
    cFields = [\<lparr> vdName = ffst, vdType = Object \<rparr>, \<lparr> vdName = fsnd, vdType = Object \<rparr>],
    cConstructor = \<lparr> kName = cPair, kParams = [\<lparr> vdName = ffst, vdType = Object \<rparr>, \<lparr> vdName = fsnd, vdType = Object \<rparr>], kSuper = [], kInits = [ffst, fsnd]\<rparr> ,
    cMethods = [\<lparr> mReturn = cPair, mName = setfst, mParams = [\<lparr>vdName = newfst, vdType = Object \<rparr>],
      mBody = New cPair [Var newfst, FieldProj (Var this) fsnd]  \<rparr>]\<rparr>"

definition exampleProg :: classTable
  where "exampleProg = (((%x. None)(A := Some classA_Def))(B := Some classB_Def))(cPair := Some classPair_Def)"


value "exampleProg \<turnstile> classA_Def OK"
value "exampleProg \<turnstile> classB_Def OK"
value "exampleProg \<turnstile> classPair_Def OK"


values "{x. exampleProg \<turnstile> MethodInvk (New cPair [New A [], New B []]) setfst [New B []] \<rightarrow>* x}"
values "{x. exampleProg \<turnstile> FieldProj (FieldProj (New cPair [New cPair [New A [], New B []], New A []]) ffst) fsnd \<rightarrow>* x}"


end
