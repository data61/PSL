(*  Author:     Klaus Aehlig, Tobias Nipkow

Normalization by Evaluation.
*)
(*<*)
theory NBE imports Main begin

declare [[syntax_ambiguity_warning = false]]

declare Let_def[simp]
(*>*)
section "Terms"

type_synonym vname = nat
type_synonym ml_vname = nat

(* FIXME only for codegen*)
type_synonym cname = int

text\<open>ML terms:\<close>

datatype ml =
 \<comment> \<open>ML\<close>
  C_ML cname ("C\<^sub>M\<^sub>L") (* ref to compiled code *)
| V_ML ml_vname ("V\<^sub>M\<^sub>L")
| A_ML ml "(ml list)" ("A\<^sub>M\<^sub>L")
| Lam_ML ml ("Lam\<^sub>M\<^sub>L")
 \<comment> \<open>the universal datatype\<close>
| C\<^sub>U cname "(ml list)"
| V\<^sub>U vname "(ml list)"
| Clo ml "(ml list)" nat
 \<comment> \<open>ML function \emph{apply}\<close>
| "apply" ml ml

text\<open>Lambda-terms:\<close>

datatype tm = C cname | V vname | \<Lambda> tm | At tm tm (infix "\<bullet>" 100)
            | "term" ml   \<comment> \<open>ML function \texttt{term}\<close>

text \<open>The following locale captures type conventions for variables.
  It is not actually used, merely a formal comment.\<close>

locale Vars =
 fixes r s t:: tm
 and rs ss ts :: "tm list"
 and u v w :: ml
 and us vs ws :: "ml list"
 and nm :: cname
 and x :: vname
 and X :: ml_vname

text\<open>The subset of pure terms:\<close>

inductive pure :: "tm \<Rightarrow> bool" where
"pure(C nm)" |
"pure(V x)" |
Lam: "pure t \<Longrightarrow> pure(\<Lambda> t)" |
"pure s \<Longrightarrow> pure t \<Longrightarrow> pure(s\<bullet>t)"

declare pure.intros[simp]
declare Lam[simp del]

lemma pure_Lam[simp]: "pure(\<Lambda> t) = pure t"
proof
  assume "pure(\<Lambda> t)" thus "pure t"
  proof cases qed auto
next
  assume "pure t" thus "pure(\<Lambda> t)" by(rule Lam)
qed

text\<open>Closed terms w.r.t.\ ML variables:\<close>

fun closed_ML :: "nat \<Rightarrow> ml \<Rightarrow> bool" ("closed\<^sub>M\<^sub>L") where
"closed\<^sub>M\<^sub>L i (C\<^sub>M\<^sub>L nm) = True" |
"closed\<^sub>M\<^sub>L i (V\<^sub>M\<^sub>L X) = (X<i)"  |
"closed\<^sub>M\<^sub>L i (A\<^sub>M\<^sub>L v vs) = (closed\<^sub>M\<^sub>L i v \<and> (\<forall>v \<in> set vs. closed\<^sub>M\<^sub>L i v))" |
"closed\<^sub>M\<^sub>L i (Lam\<^sub>M\<^sub>L v) = closed\<^sub>M\<^sub>L (i+1) v" |
"closed\<^sub>M\<^sub>L i (C\<^sub>U nm vs) = (\<forall>v \<in> set vs. closed\<^sub>M\<^sub>L i v)" |
"closed\<^sub>M\<^sub>L i (V\<^sub>U nm vs) = (\<forall>v \<in> set vs. closed\<^sub>M\<^sub>L i v)" |
"closed\<^sub>M\<^sub>L i (Clo f vs n) = (closed\<^sub>M\<^sub>L i f \<and> (\<forall>v \<in> set vs. closed\<^sub>M\<^sub>L i v))" |
"closed\<^sub>M\<^sub>L i (apply v w) = (closed\<^sub>M\<^sub>L i v \<and> closed\<^sub>M\<^sub>L i w)"

fun closed_tm_ML :: "nat \<Rightarrow> tm \<Rightarrow> bool" ("closed\<^sub>M\<^sub>L") where
"closed_tm_ML i (r\<bullet>s) = (closed_tm_ML i r \<and> closed_tm_ML i s)" |
"closed_tm_ML i (\<Lambda> t) = (closed_tm_ML i t)" |
"closed_tm_ML i (term v) = closed_ML i v" |
"closed_tm_ML i v = True"

text\<open>Free variables:\<close>

fun fv_ML :: "ml \<Rightarrow> ml_vname set" ("fv\<^sub>M\<^sub>L") where
"fv\<^sub>M\<^sub>L (C\<^sub>M\<^sub>L nm) = {}" |
"fv\<^sub>M\<^sub>L (V\<^sub>M\<^sub>L X) = {X}"  |
"fv\<^sub>M\<^sub>L (A\<^sub>M\<^sub>L v vs) = fv\<^sub>M\<^sub>L v \<union> (\<Union>v \<in> set vs. fv\<^sub>M\<^sub>L v)" |
"fv\<^sub>M\<^sub>L (Lam\<^sub>M\<^sub>L v) = {X. Suc X : fv\<^sub>M\<^sub>L v}" |
"fv\<^sub>M\<^sub>L (C\<^sub>U nm vs) = (\<Union>v \<in> set vs. fv\<^sub>M\<^sub>L v)" |
"fv\<^sub>M\<^sub>L (V\<^sub>U nm vs) = (\<Union>v \<in> set vs. fv\<^sub>M\<^sub>L v)" |
"fv\<^sub>M\<^sub>L (Clo f vs n) = fv\<^sub>M\<^sub>L f \<union> (\<Union>v \<in> set vs. fv\<^sub>M\<^sub>L v)" |
"fv\<^sub>M\<^sub>L (apply v w) = fv\<^sub>M\<^sub>L v \<union> fv\<^sub>M\<^sub>L w"

primrec fv :: "tm \<Rightarrow> vname set" where
"fv (C nm) = {}" |
"fv (V X) = {X}"  |
"fv (s \<bullet> t) = fv s \<union> fv t" |
"fv (\<Lambda> t) = {X. Suc X : fv t}"


subsection "Iterated Term Application"

abbreviation foldl_At (infix "\<bullet>\<bullet>" 90) where
"t \<bullet>\<bullet> ts \<equiv> foldl (\<bullet>) t ts"

text\<open>Auxiliary measure function:\<close>
primrec depth_At :: "tm \<Rightarrow> nat"
where
  "depth_At(C nm) = 0"
| "depth_At(V x) = 0"
| "depth_At(s \<bullet> t) = depth_At s + 1"
| "depth_At(\<Lambda> t) = 0"
| "depth_At(term v) = 0"

lemma depth_At_foldl:
 "depth_At(s \<bullet>\<bullet> ts) = depth_At s + size ts"
by (induct ts arbitrary: s) simp_all

lemma foldl_At_eq_lemma: "size ts = size ts' \<Longrightarrow>
 s \<bullet>\<bullet> ts = s' \<bullet>\<bullet> ts' \<longleftrightarrow> s = s' \<and> ts = ts'"
by (induct arbitrary: s s' rule:list_induct2) simp_all

lemma foldl_At_eq_length:
 "s \<bullet>\<bullet> ts = s \<bullet>\<bullet> ts' \<Longrightarrow> length ts = length ts'"
apply(subgoal_tac "depth_At(s \<bullet>\<bullet> ts) = depth_At(s \<bullet>\<bullet> ts')")
apply(erule thin_rl)
 apply (simp add:depth_At_foldl)
apply simp
done

lemma foldl_At_eq[simp]: "s \<bullet>\<bullet> ts = s \<bullet>\<bullet> ts' \<longleftrightarrow> ts = ts'"
apply(rule)
 prefer 2 apply simp
apply(blast dest:foldl_At_eq_lemma foldl_At_eq_length)
done

lemma term_eq_foldl_At[simp]:
  "term v = t \<bullet>\<bullet> ts \<longleftrightarrow> t = term v \<and> ts = []"
by (induct ts arbitrary:t) auto

lemma At_eq_foldl_At[simp]:
  "r \<bullet> s = t \<bullet>\<bullet> ts \<longleftrightarrow>
  (if ts=[] then t = r \<bullet> s else s = last ts \<and> r = t \<bullet>\<bullet> butlast ts)"
apply (induct ts arbitrary:t)
 apply fastforce
apply rule
 apply clarsimp
 apply rule
  apply clarsimp
 apply clarsimp
 apply(subgoal_tac "\<exists>ts' t'. ts = ts' @ [t']")
  apply clarsimp
 defer
 apply (clarsimp split:list.split)
apply (metis append_butlast_last_id)
done

lemma foldl_At_eq_At[simp]:
  "t \<bullet>\<bullet> ts = r \<bullet> s \<longleftrightarrow>
  (if ts=[] then t = r \<bullet> s else s = last ts \<and> r = t \<bullet>\<bullet> butlast ts)"
by(metis At_eq_foldl_At)

lemma Lam_eq_foldl_At[simp]:
  "\<Lambda> s = t \<bullet>\<bullet> ts \<longleftrightarrow> t = \<Lambda> s \<and> ts = []"
by (induct ts arbitrary:t) auto

lemma foldl_At_eq_Lam[simp]:
  "t \<bullet>\<bullet> ts = \<Lambda> s \<longleftrightarrow> t = \<Lambda> s \<and> ts = []"
by (induct ts arbitrary:t) auto

lemma [simp]: "s \<bullet> t \<noteq> s"
apply(subgoal_tac "size(s \<bullet> t) \<noteq> size s")
apply metis
apply simp
done

(* Better: a simproc for disproving "s = t"
   if s is a subterm of t or vice versa, by proving "size s ~= size t"
*)

fun atomic_tm :: "tm \<Rightarrow> bool" where
"atomic_tm(s \<bullet> t) = False" |
"atomic_tm(_) = True"

fun head_tm where
"head_tm(s \<bullet> t) = head_tm s" |
"head_tm(s) = s"

fun args_tm where
"args_tm(s \<bullet> t) = args_tm s @ [t]" |
"args_tm(_) = []"

lemma head_tm_foldl_At[simp]: "head_tm(s \<bullet>\<bullet> ts) = head_tm s"
by(induct ts arbitrary: s) auto

lemma args_tm_foldl_At[simp]: "args_tm(s \<bullet>\<bullet> ts) = args_tm s @ ts"
by(induct ts arbitrary: s) auto

lemma tm_eq_iff:
  "atomic_tm(head_tm s) \<Longrightarrow> atomic_tm(head_tm t)
   \<Longrightarrow> s = t \<longleftrightarrow> head_tm s = head_tm t \<and> args_tm s = args_tm t"
apply(induct s arbitrary: t)
apply(case_tac t, simp+)+
done

declare
  tm_eq_iff[of "h \<bullet>\<bullet> ts", simp]
  tm_eq_iff[of _ "h \<bullet>\<bullet> ts", simp]
  for h ts

lemma atomic_tm_head_tm: "atomic_tm(head_tm t)"
by(induct t) auto

lemma head_tm_idem: "head_tm(head_tm t) = head_tm t"
by(induct t) auto

lemma args_tm_head_tm: "args_tm(head_tm t) = []"
by(induct t) auto

lemma eta_head_args: "t = head_tm t \<bullet>\<bullet> args_tm t"
by (subst tm_eq_iff) (auto simp: atomic_tm_head_tm head_tm_idem args_tm_head_tm)


lemma tm_vector_cases:
  "(\<exists>n ts. t = V n \<bullet>\<bullet> ts) \<or>
   (\<exists>nm ts. t = C nm \<bullet>\<bullet> ts) \<or>
   (\<exists>t' ts. t = \<Lambda> t' \<bullet>\<bullet> ts) \<or>
   (\<exists>v ts. t = term v \<bullet>\<bullet> ts)"
apply(induct t)
apply simp_all
by (metis snoc_eq_iff_butlast)

lemma fv_head_C[simp]: "fv (t \<bullet>\<bullet> ts) = fv t \<union> (\<Union>t\<in>set ts. fv t)"
by(induct ts arbitrary:t) auto


subsection "Lifting and Substitution"

fun lift_ml :: "nat \<Rightarrow> ml \<Rightarrow> ml" ("lift") where
"lift i (C\<^sub>M\<^sub>L nm) = C\<^sub>M\<^sub>L nm" |
"lift i (V\<^sub>M\<^sub>L X) = V\<^sub>M\<^sub>L X" |
"lift i (A\<^sub>M\<^sub>L v vs) = A\<^sub>M\<^sub>L (lift i v) (map (lift i) vs)" |
"lift i (Lam\<^sub>M\<^sub>L v) = Lam\<^sub>M\<^sub>L (lift i v)" |
"lift i (C\<^sub>U nm vs) = C\<^sub>U nm (map (lift i) vs)" |
"lift i (V\<^sub>U x vs) = V\<^sub>U (if x < i then x else x+1) (map (lift i) vs)" |
"lift i (Clo v vs n) = Clo (lift i v) (map (lift i) vs) n" |
"lift i (apply u v) = apply (lift i u) (lift i v)"

lemmas ml_induct = lift_ml.induct[of "\<lambda>i v. P v"] for P

fun lift_tm :: "nat \<Rightarrow> tm \<Rightarrow> tm" ("lift") where
"lift i (C nm) = C nm" |
"lift i (V x) = V(if x < i then x else x+1)" |
"lift i (s\<bullet>t) = (lift i s)\<bullet>(lift i t)" |
"lift i (\<Lambda> t) = \<Lambda>(lift (i+1) t)" |
"lift i (term v) = term (lift i v)"

fun lift_ML :: "nat \<Rightarrow> ml \<Rightarrow> ml" ("lift\<^sub>M\<^sub>L") where
"lift\<^sub>M\<^sub>L i (C\<^sub>M\<^sub>L nm) = C\<^sub>M\<^sub>L nm" |
"lift\<^sub>M\<^sub>L i (V\<^sub>M\<^sub>L X) = V\<^sub>M\<^sub>L (if X < i then X else X+1)" |
"lift\<^sub>M\<^sub>L i (A\<^sub>M\<^sub>L v vs) = A\<^sub>M\<^sub>L (lift\<^sub>M\<^sub>L i v) (map (lift\<^sub>M\<^sub>L i) vs)" |
"lift\<^sub>M\<^sub>L i (Lam\<^sub>M\<^sub>L v) = Lam\<^sub>M\<^sub>L (lift\<^sub>M\<^sub>L (i+1) v)" |
"lift\<^sub>M\<^sub>L i (C\<^sub>U nm vs) = C\<^sub>U nm (map (lift\<^sub>M\<^sub>L i) vs)" |
"lift\<^sub>M\<^sub>L i (V\<^sub>U x vs) = V\<^sub>U x (map (lift\<^sub>M\<^sub>L i) vs)" |
"lift\<^sub>M\<^sub>L i (Clo v vs n) = Clo (lift\<^sub>M\<^sub>L i v) (map (lift\<^sub>M\<^sub>L i) vs) n" |
"lift\<^sub>M\<^sub>L i (apply u v) = apply (lift\<^sub>M\<^sub>L i u) (lift\<^sub>M\<^sub>L i v)"

definition
 cons :: "tm \<Rightarrow> (nat \<Rightarrow> tm) \<Rightarrow> (nat \<Rightarrow> tm)" (infix "##" 65) where
"t##\<sigma> \<equiv> \<lambda>i. case i of 0 \<Rightarrow> t | Suc j \<Rightarrow> lift 0 (\<sigma> j)"

definition
 cons_ML :: "ml \<Rightarrow> (nat \<Rightarrow> ml) \<Rightarrow> (nat \<Rightarrow> ml)" (infix "##" 65) where
"v##\<sigma> \<equiv> \<lambda>i. case i of 0 \<Rightarrow> v::ml | Suc j \<Rightarrow> lift\<^sub>M\<^sub>L 0 (\<sigma> j)"

text\<open>Only for pure terms!\<close>
primrec subst :: "(nat \<Rightarrow> tm) \<Rightarrow> tm \<Rightarrow> tm"
where
  "subst \<sigma> (C nm) = C nm"
| "subst \<sigma> (V x) = \<sigma> x"
| "subst \<sigma> (\<Lambda> t) = \<Lambda>(subst (V 0 ## \<sigma>) t)"
| "subst \<sigma> (s\<bullet>t) = (subst \<sigma> s) \<bullet> (subst \<sigma> t)"

fun subst_ML :: "(nat \<Rightarrow> ml) \<Rightarrow> ml \<Rightarrow> ml" ("subst\<^sub>M\<^sub>L") where
"subst\<^sub>M\<^sub>L \<sigma> (C\<^sub>M\<^sub>L nm) = C\<^sub>M\<^sub>L nm" |
"subst\<^sub>M\<^sub>L \<sigma> (V\<^sub>M\<^sub>L X) = \<sigma> X" |
"subst\<^sub>M\<^sub>L \<sigma> (A\<^sub>M\<^sub>L v vs) = A\<^sub>M\<^sub>L (subst\<^sub>M\<^sub>L \<sigma> v) (map (subst\<^sub>M\<^sub>L \<sigma>) vs)" |
"subst\<^sub>M\<^sub>L \<sigma> (Lam\<^sub>M\<^sub>L v) = Lam\<^sub>M\<^sub>L (subst\<^sub>M\<^sub>L (V\<^sub>M\<^sub>L 0 ## \<sigma>) v)" |
"subst\<^sub>M\<^sub>L \<sigma> (C\<^sub>U nm vs) = C\<^sub>U nm (map (subst\<^sub>M\<^sub>L \<sigma>) vs)" |
"subst\<^sub>M\<^sub>L \<sigma> (V\<^sub>U x vs) = V\<^sub>U x (map (subst\<^sub>M\<^sub>L \<sigma>) vs)" |
"subst\<^sub>M\<^sub>L \<sigma> (Clo v vs n) = Clo (subst\<^sub>M\<^sub>L \<sigma> v) (map (subst\<^sub>M\<^sub>L \<sigma>) vs) n" |
"subst\<^sub>M\<^sub>L \<sigma> (apply u v) = apply (subst\<^sub>M\<^sub>L \<sigma> u) (subst\<^sub>M\<^sub>L \<sigma> v)"
(* FIXME currrently needed for code generator
lemmas [code] = lift_tm.simps lift_ml.simps
lemmas [code] = subst_ML.simps *)

abbreviation
  subst_decr :: "nat \<Rightarrow> tm \<Rightarrow> nat \<Rightarrow> tm" where
  "subst_decr k t \<equiv> \<lambda>n. if n<k then V n else if n=k then t else V(n - 1)"
abbreviation
  subst_decr_ML :: "nat \<Rightarrow> ml \<Rightarrow> nat \<Rightarrow> ml" where
"subst_decr_ML k v \<equiv> \<lambda>n. if n<k then V\<^sub>M\<^sub>L n else if n=k then v else V\<^sub>M\<^sub>L(n - 1)"
abbreviation
  subst1 :: "tm \<Rightarrow> tm \<Rightarrow> nat \<Rightarrow> tm" ("(_/[_'/_])" [300, 0, 0] 300) where
 "s[t/k] \<equiv> subst (subst_decr k t) s"
abbreviation
  subst1_ML :: "ml \<Rightarrow> ml \<Rightarrow> nat \<Rightarrow> ml" ("(_/[_'/_])" [300, 0, 0] 300) where
 "u[v/k] \<equiv> subst\<^sub>M\<^sub>L (subst_decr_ML k v) u"

lemma apply_cons[simp]:
  "(t##\<sigma>) i = (if i=0 then t::tm else lift 0 (\<sigma>(i - 1)))"
by(simp add: cons_def split:nat.split)

lemma apply_cons_ML[simp]:
  "(v##\<sigma>) i = (if i=0 then v::ml else lift\<^sub>M\<^sub>L 0 (\<sigma>(i - 1)))"
by(simp add: cons_ML_def split:nat.split)

lemma lift_foldl_At[simp]:
  "lift k (s \<bullet>\<bullet> ts) = (lift k s) \<bullet>\<bullet> (map (lift k) ts)"
by(induct ts arbitrary:s) simp_all

lemma lift_lift_ml: fixes v :: ml shows
  "i < k+1 \<Longrightarrow> lift (Suc k) (lift i v) = lift i (lift k v)"
by(induct i v rule:lift_ml.induct)
  simp_all
lemma lift_lift_tm: fixes t :: tm shows
    "i < k+1 \<Longrightarrow> lift (Suc k) (lift i t) = lift i (lift k t)"
by(induct t arbitrary: i rule:lift_tm.induct)(simp_all add:lift_lift_ml)

lemma lift_lift_ML:
  "i < k+1 \<Longrightarrow> lift\<^sub>M\<^sub>L (Suc k) (lift\<^sub>M\<^sub>L i v) = lift\<^sub>M\<^sub>L i (lift\<^sub>M\<^sub>L k v)"
by(induct v arbitrary: i rule:lift_ML.induct)
  simp_all

lemma lift_lift_ML_comm:
  "lift j (lift\<^sub>M\<^sub>L i v) = lift\<^sub>M\<^sub>L i (lift j v)"
by(induct v arbitrary: i j rule:lift_ML.induct)
  simp_all

lemma V_ML_cons_ML_subst_decr[simp]:
  "V\<^sub>M\<^sub>L 0 ## subst_decr_ML k v = subst_decr_ML (Suc k) (lift\<^sub>M\<^sub>L 0 v)"
by(rule ext)(simp add:cons_ML_def split:nat.split)

lemma shift_subst_decr[simp]:
 "V 0 ## subst_decr k t = subst_decr (Suc k) (lift 0 t)"
by(rule ext)(simp add:cons_def split:nat.split)

lemma lift_comp_subst_decr[simp]:
  "lift 0 o subst_decr_ML k v = subst_decr_ML k (lift 0 v)"
by(rule ext) simp

lemma subst_ML_ext: "\<forall>i. \<sigma> i = \<sigma>' i \<Longrightarrow> subst\<^sub>M\<^sub>L \<sigma> v = subst\<^sub>M\<^sub>L \<sigma>' v"
by(metis ext)

lemma subst_ext: "\<forall>i. \<sigma> i = \<sigma>' i \<Longrightarrow> subst \<sigma> v = subst \<sigma>' v"
by(metis ext)

lemma lift_Pure_tms[simp]: "pure t \<Longrightarrow> pure(lift k t)"
by(induct arbitrary:k pred:pure) simp_all

lemma cons_ML_V_ML[simp]: "(V\<^sub>M\<^sub>L 0 ## V\<^sub>M\<^sub>L) = V\<^sub>M\<^sub>L"
by(rule ext) simp

lemma cons_V[simp]: "(V 0 ## V) = V"
by(rule ext) simp

lemma lift_o_shift: "lift k \<circ> (V\<^sub>M\<^sub>L 0 ## \<sigma>) = (V\<^sub>M\<^sub>L 0 ## (lift k \<circ> \<sigma>))"
by(rule ext)(simp add: lift_lift_ML_comm)

lemma lift_subst_ML:
 "lift k (subst\<^sub>M\<^sub>L \<sigma> v) = subst\<^sub>M\<^sub>L (lift k \<circ> \<sigma>) (lift k v)"
apply(induct \<sigma> v rule:subst_ML.induct)
apply(simp_all add: o_assoc lift_o_shift del:apply_cons_ML)
apply(simp add:o_def)
done

corollary lift_subst_ML1:
  "\<forall>v k. lift_ml 0 (u[v/k]) = (lift_ml 0 u)[lift 0 v/k]"
apply(induct u rule:ml_induct)
apply(simp_all add:lift_lift_ml lift_subst_ML)
apply(subst lift_lift_ML_comm)apply simp
done

lemma lift_ML_subst_ML:
 "lift\<^sub>M\<^sub>L k (subst\<^sub>M\<^sub>L \<sigma> v) =
  subst\<^sub>M\<^sub>L (\<lambda>i. if i<k then lift\<^sub>M\<^sub>L k (\<sigma> i) else if i=k then V\<^sub>M\<^sub>L k else lift\<^sub>M\<^sub>L k (\<sigma>(i - 1))) (lift\<^sub>M\<^sub>L k v)"
  (is "_ = subst\<^sub>M\<^sub>L (?insrt k \<sigma>) (lift\<^sub>M\<^sub>L k v)")
apply (induct k v arbitrary: \<sigma> k rule: lift_ML.induct)
apply (simp_all add: o_assoc lift_o_shift)
apply(subgoal_tac "V\<^sub>M\<^sub>L 0 ## ?insrt k \<sigma> = ?insrt (Suc k) (V\<^sub>M\<^sub>L 0 ## \<sigma>)")
 apply simp
apply (simp add:fun_eq_iff lift_lift_ML cons_ML_def split:nat.split)
done

corollary subst_cons_lift:
 "subst\<^sub>M\<^sub>L (V\<^sub>M\<^sub>L 0 ## \<sigma>) o (lift\<^sub>M\<^sub>L 0) = lift\<^sub>M\<^sub>L 0 o (subst\<^sub>M\<^sub>L \<sigma>)"
apply(rule ext)
apply(simp add: lift_ML_subst_ML)
apply(subgoal_tac "(V\<^sub>M\<^sub>L 0 ## \<sigma>) = (\<lambda>i. if i = 0 then V\<^sub>M\<^sub>L 0 else lift\<^sub>M\<^sub>L 0 (\<sigma> (i - 1)))")
 apply simp
apply(rule ext, simp)
done

lemma lift_ML_id[simp]: "closed\<^sub>M\<^sub>L k v \<Longrightarrow> lift\<^sub>M\<^sub>L k v = v"
by(induct k v rule: lift_ML.induct)(simp_all add:list_eq_iff_nth_eq)

lemma subst_ML_id:
  "closed\<^sub>M\<^sub>L k v \<Longrightarrow> \<forall>i<k. \<sigma> i = V\<^sub>M\<^sub>L i \<Longrightarrow> subst\<^sub>M\<^sub>L \<sigma> v = v"
apply (induct \<sigma> v arbitrary: k rule: subst_ML.induct)
apply (auto simp add: list_eq_iff_nth_eq)
   apply(simp add:Ball_def)
   apply(erule_tac x="vs!i" in meta_allE)
   apply(erule_tac x="k" in meta_allE)
   apply(erule_tac x="k" in meta_allE)
   apply simp
  apply(erule_tac x="vs!i" in meta_allE)
  apply(erule_tac x="k" in meta_allE)
  apply simp
 apply(erule_tac x="vs!i" in meta_allE)
 apply(erule_tac x="k" in meta_allE)
 apply simp
apply(erule_tac x="vs!i" in meta_allE)
apply(erule_tac x="k" in meta_allE)
apply(erule_tac x="k" in meta_allE)
apply simp
done

corollary subst_ML_id2[simp]: "closed\<^sub>M\<^sub>L 0 v \<Longrightarrow> subst\<^sub>M\<^sub>L \<sigma> v = v"
using subst_ML_id[where k=0] by simp

lemma subst_ML_coincidence:
  "closed\<^sub>M\<^sub>L k v \<Longrightarrow> \<forall>i<k. \<sigma> i = \<sigma>' i \<Longrightarrow> subst\<^sub>M\<^sub>L \<sigma> v = subst\<^sub>M\<^sub>L \<sigma>' v"
by (induct \<sigma> v arbitrary: k \<sigma>' rule: subst_ML.induct) auto

lemma subst_ML_comp:
  "subst\<^sub>M\<^sub>L \<sigma> (subst\<^sub>M\<^sub>L \<sigma>' v) = subst\<^sub>M\<^sub>L (subst\<^sub>M\<^sub>L \<sigma>  \<circ> \<sigma>') v"
apply (induct \<sigma>' v arbitrary: \<sigma> rule: subst_ML.induct)
apply (simp_all add: list_eq_iff_nth_eq)
apply(rule subst_ML_ext)
apply simp
apply (metis o_apply subst_cons_lift)
done

lemma subst_ML_comp2:
  "\<forall>i. \<sigma>'' i = subst\<^sub>M\<^sub>L \<sigma> (\<sigma>' i) \<Longrightarrow> subst\<^sub>M\<^sub>L \<sigma> (subst\<^sub>M\<^sub>L \<sigma>' v) = subst\<^sub>M\<^sub>L \<sigma>'' v"
by(simp add:subst_ML_comp subst_ML_ext)

lemma closed_tm_ML_foldl_At:
  "closed\<^sub>M\<^sub>L k (t \<bullet>\<bullet> ts) \<longleftrightarrow> closed\<^sub>M\<^sub>L k t \<and> (\<forall>t \<in> set ts. closed\<^sub>M\<^sub>L k t)"
by(induct ts arbitrary: t) simp_all

lemma closed_ML_lift[simp]:
  fixes v :: ml shows "closed\<^sub>M\<^sub>L k v \<Longrightarrow> closed\<^sub>M\<^sub>L k (lift m v)"
by(induct k v arbitrary: m rule: lift_ML.induct)
  (simp_all add:list_eq_iff_nth_eq)

lemma closed_ML_Suc: "closed\<^sub>M\<^sub>L n v \<Longrightarrow> closed\<^sub>M\<^sub>L (Suc n) (lift\<^sub>M\<^sub>L k v)"
by (induct k v arbitrary: n rule: lift_ML.induct) simp_all

lemma closed_ML_subst_ML:
  "\<forall>i. closed\<^sub>M\<^sub>L k (\<sigma> i) \<Longrightarrow> closed\<^sub>M\<^sub>L k (subst\<^sub>M\<^sub>L \<sigma> v)"
by(induct \<sigma> v arbitrary: k rule: subst_ML.induct) (auto simp: closed_ML_Suc)

lemma closed_ML_subst_ML2:
  "closed\<^sub>M\<^sub>L k v \<Longrightarrow> \<forall>i<k. closed\<^sub>M\<^sub>L l (\<sigma> i) \<Longrightarrow> closed\<^sub>M\<^sub>L l (subst\<^sub>M\<^sub>L \<sigma> v)"
by(induct \<sigma> v arbitrary: k l rule: subst_ML.induct)(auto simp: closed_ML_Suc)


lemma subst_foldl[simp]:
 "subst \<sigma> (s \<bullet>\<bullet> ts) = (subst \<sigma> s) \<bullet>\<bullet> (map (subst \<sigma>) ts)"
by (induct ts arbitrary: s) auto

lemma subst_V: "pure t \<Longrightarrow> subst V t = t"
by(induct pred:pure) simp_all

lemma lift_subst_aux:
  "pure t \<Longrightarrow> \<forall>i<k. \<sigma>' i = lift k (\<sigma> i) \<Longrightarrow>
   \<forall>i\<ge>k. \<sigma>'(Suc i) = lift k (\<sigma> i) \<Longrightarrow> 
  \<sigma>' k = V k \<Longrightarrow> lift k (subst \<sigma> t) = subst \<sigma>' (lift k t)"
apply(induct arbitrary:\<sigma> \<sigma>' k pred:pure)
apply (simp_all add: split:nat.split)
apply(erule meta_allE)+
apply(erule meta_impE)
defer
apply(erule meta_impE)
defer
apply(erule meta_mp)
apply (simp_all add: cons_def lift_lift_ml lift_lift_tm split:nat.split)
done

corollary lift_subst:
  "pure t \<Longrightarrow> lift 0 (subst \<sigma> t) = subst (V 0 ## \<sigma>) (lift 0 t)"
by (simp add: lift_subst_aux lift_lift_ml)

lemma subst_comp:
  "pure t \<Longrightarrow> \<forall>i. pure(\<sigma>' i) \<Longrightarrow>
   \<sigma>'' = (\<lambda>i. subst \<sigma> (\<sigma>' i)) \<Longrightarrow> subst \<sigma> (subst \<sigma>' t) = subst \<sigma>'' t"
apply(induct arbitrary:\<sigma> \<sigma>' \<sigma>'' pred:pure)
apply simp
apply simp
defer
apply simp
apply (simp (no_asm))
apply(erule meta_allE)+
apply(erule meta_impE)
defer
apply(erule meta_mp)
prefer 2 apply simp
apply(rule ext)
apply(simp add:lift_subst)
done


section "Reduction"

subsection "Patterns"

inductive pattern :: "tm \<Rightarrow> bool"
      and patterns :: "tm list \<Rightarrow> bool" where
       "patterns ts \<equiv> \<forall>t\<in>set ts. pattern t" |
pat_V: "pattern(V X)" |
pat_C: "patterns ts \<Longrightarrow> pattern(C nm \<bullet>\<bullet> ts)"

lemma pattern_Lam[simp]: "\<not> pattern(\<Lambda> t)"
by(auto elim!: pattern.cases)

lemma pattern_At'D12: "pattern r \<Longrightarrow> r = (s \<bullet> t) \<Longrightarrow> pattern s \<and> pattern t"
proof(induct arbitrary: s t pred:pattern)
  case pat_V thus ?case by simp
next
  case pat_C thus ?case
    by (simp add: atomic_tm_head_tm split:if_split_asm)
       (metis eta_head_args in_set_butlastD pattern.pat_C)
qed

lemma pattern_AtD12: "pattern(s \<bullet> t) \<Longrightarrow> pattern s \<and> pattern t"
by(metis pattern_At'D12)

lemma pattern_At_vecD: "pattern(s \<bullet>\<bullet> ts) \<Longrightarrow> patterns ts"
apply(induct ts rule:rev_induct)
 apply simp
apply (fastforce dest!:pattern_AtD12)
done

lemma pattern_At_decomp: "pattern(s \<bullet> t) \<Longrightarrow> \<exists>nm ss. s = C nm \<bullet>\<bullet> ss"
proof(induct s arbitrary: t)
  case (At s1 s2) show ?case
    using At by (metis foldl_Cons foldl_Nil foldl_append pattern_AtD12)
qed (auto elim!: pattern.cases split:if_split_asm)


subsection "Reduction of \<open>\<lambda>\<close>-terms"

text\<open>The source program:\<close>

axiomatization R :: "(cname * tm list * tm)set" where
pure_R: "(nm,ts,t) : R \<Longrightarrow> (\<forall>t \<in> set ts. pure t) \<and> pure t" and
fv_R:   "(nm,ts,t) : R \<Longrightarrow> X : fv t \<Longrightarrow> \<exists>t' \<in> set ts. X : fv t'" and
pattern_R: "(nm,ts,t') : R \<Longrightarrow> patterns ts"

inductive_set
  Red_tm :: "(tm * tm)set"
  and red_tm :: "[tm, tm] => bool"  (infixl "\<rightarrow>" 50)
where
  "s \<rightarrow> t \<equiv> (s, t) \<in> Red_tm"
 \<comment> \<open>$\beta$-reduction\<close>
| "(\<Lambda> t) \<bullet> s \<rightarrow> t[s/0]"
 \<comment> \<open>$\eta$-expansion\<close>
| "t \<rightarrow> \<Lambda> ((lift 0 t) \<bullet> (V 0))"
 \<comment> \<open>Rewriting\<close>
| "(nm,ts,t) : R \<Longrightarrow> (C nm) \<bullet>\<bullet> (map (subst \<sigma>) ts) \<rightarrow> subst \<sigma> t"
| "t \<rightarrow> t' \<Longrightarrow> \<Lambda> t \<rightarrow> \<Lambda> t'"
| "s \<rightarrow> s' \<Longrightarrow> s \<bullet> t \<rightarrow> s' \<bullet> t"
| "t \<rightarrow> t' \<Longrightarrow> s \<bullet> t \<rightarrow> s \<bullet> t'"

abbreviation
  reds_tm :: "[tm, tm] => bool"  (infixl "\<rightarrow>*" 50) where
  "s \<rightarrow>* t \<equiv> (s, t) \<in> Red_tm^*"

inductive_set
  Reds_tm_list :: "(tm list * tm list) set"
  and reds_tm_list :: "[tm list, tm list] \<Rightarrow> bool" (infixl "\<rightarrow>*" 50)
where
  "ss \<rightarrow>* ts \<equiv> (ss, ts) \<in> Reds_tm_list"
| "[] \<rightarrow>* []"
| "ts \<rightarrow>* ts' \<Longrightarrow> t \<rightarrow>* t' \<Longrightarrow> t#ts \<rightarrow>* t'#ts'"


declare Reds_tm_list.intros[simp]

lemma Reds_tm_list_refl[simp]: fixes ts :: "tm list" shows "ts \<rightarrow>* ts"
by(induct ts) auto

lemma Red_tm_append: "rs \<rightarrow>* rs' \<Longrightarrow> ts \<rightarrow>* ts' \<Longrightarrow> rs @ ts \<rightarrow>* rs' @ ts'"
by(induct set: Reds_tm_list) auto

lemma Red_tm_rev: "ts \<rightarrow>* ts' \<Longrightarrow> rev ts \<rightarrow>* rev ts'"
by(induct set: Reds_tm_list) (auto simp:Red_tm_append)

lemma red_Lam[simp]: "t \<rightarrow>* t' \<Longrightarrow> \<Lambda> t \<rightarrow>* \<Lambda> t'"
apply(induct rule:rtrancl_induct)
apply(simp_all)
apply(blast intro: rtrancl_into_rtrancl Red_tm.intros)
done

lemma red_At1[simp]: "t \<rightarrow>* t' \<Longrightarrow> t \<bullet> s \<rightarrow>* t' \<bullet> s"
apply(induct rule:rtrancl_induct)
apply(simp_all)
apply(blast intro: rtrancl_into_rtrancl Red_tm.intros)
done

lemma red_At2[simp]: "t \<rightarrow>* t' \<Longrightarrow> s \<bullet> t \<rightarrow>* s \<bullet> t'"
apply(induct rule:rtrancl_induct)
apply(simp_all)
apply(blast intro:rtrancl_into_rtrancl Red_tm.intros)
done

lemma Reds_tm_list_foldl_At:
 "ts \<rightarrow>* ts' \<Longrightarrow> s \<rightarrow>* s' \<Longrightarrow> s \<bullet>\<bullet> ts \<rightarrow>* s' \<bullet>\<bullet> ts'"
apply(induct arbitrary:s s' rule:Reds_tm_list.induct)
apply simp
apply simp
apply(blast dest: red_At1 red_At2 intro:rtrancl_trans)
done


subsection "Reduction of ML-terms"

text\<open>The compiled rule set:\<close>

consts compR :: "(cname * ml list * ml)set"

text\<open>\noindent
The actual definition is given in \S\ref{sec:Compiler} below.\<close>

text\<open>Now we characterize ML values that cannot possibly be rewritten by a
rule in @{const compR}.\<close>

lemma termination_no_match_ML:
  "i < length ps \<Longrightarrow> rev ps ! i = C\<^sub>U nm vs
   \<Longrightarrow> sum_list (map size vs) < sum_list (map size ps)"
apply(subgoal_tac "C\<^sub>U nm vs : set ps")
 apply(drule sum_list_map_remove1[of _ _ size])
 apply (simp add:size_list_conv_sum_list)
apply (metis in_set_conv_nth length_rev set_rev)
done

declare conj_cong[fundef_cong]

function no_match_ML ("no'_match\<^sub>M\<^sub>L") where
"no_match\<^sub>M\<^sub>L ps os =
  (\<exists>i < min (size os) (size ps).
   \<exists>nm nm' vs vs'. (rev ps)!i = C\<^sub>U nm vs \<and> (rev os)!i = C\<^sub>U nm' vs' \<and>
      (nm=nm' \<longrightarrow> no_match\<^sub>M\<^sub>L vs vs'))"
by pat_completeness auto
termination
apply(relation "measure(%(vs::ml list,_). \<Sum>v\<leftarrow>vs. size v)")
apply (auto simp:termination_no_match_ML)
done


abbreviation
"no_match_compR nm os \<equiv>
  \<forall>(nm',ps,v)\<in> compR. nm=nm' \<longrightarrow> no_match\<^sub>M\<^sub>L ps os"

declare no_match_ML.simps[simp del]

inductive_set
  Red_ml :: "(ml * ml)set"
  and Red_ml_list :: "(ml list * ml list)set"
  and red_ml :: "[ml, ml] => bool"  (infixl "\<Rightarrow>" 50)
  and red_ml_list :: "[ml list, ml list] => bool"  (infixl "\<Rightarrow>" 50)
  and reds_ml :: "[ml, ml] => bool"  (infixl "\<Rightarrow>*" 50)
where
  "s \<Rightarrow> t \<equiv> (s, t) \<in> Red_ml"
| "ss \<Rightarrow> ts \<equiv> (ss, ts) \<in> Red_ml_list"
| "s \<Rightarrow>* t \<equiv> (s, t) \<in> Red_ml^*"
 \<comment> \<open>ML $\beta$-reduction\<close>
| "A\<^sub>M\<^sub>L (Lam\<^sub>M\<^sub>L u) [v] \<Rightarrow> u[v/0]"
 \<comment> \<open>Execution of a compiled rewrite rule\<close>
| "(nm,vs,v) : compR \<Longrightarrow> \<forall> i. closed\<^sub>M\<^sub>L 0 (\<sigma> i) \<Longrightarrow>
   A\<^sub>M\<^sub>L (C\<^sub>M\<^sub>L nm) (map (subst\<^sub>M\<^sub>L \<sigma>) vs) \<Rightarrow> subst\<^sub>M\<^sub>L \<sigma> v"
\<comment> \<open>default rule:\<close>
| "\<forall>i. closed\<^sub>M\<^sub>L 0 (\<sigma> i)
   \<Longrightarrow> vs = map V\<^sub>M\<^sub>L [0..<arity nm] \<Longrightarrow> vs' = map (subst\<^sub>M\<^sub>L \<sigma>) vs
   \<Longrightarrow> no_match_compR nm vs'
   \<Longrightarrow> A\<^sub>M\<^sub>L (C\<^sub>M\<^sub>L nm) vs' \<Rightarrow> subst\<^sub>M\<^sub>L \<sigma> (C\<^sub>U nm vs)"
 \<comment> \<open>Equations for function \texttt{apply}\<close>
| apply_Clo1: "apply (Clo f vs (Suc 0)) v \<Rightarrow> A\<^sub>M\<^sub>L f (v # vs)"
| apply_Clo2: "n > 0 \<Longrightarrow>
 apply (Clo f vs (Suc n)) v \<Rightarrow> Clo f (v # vs) n"
| apply_C: "apply (C\<^sub>U nm vs) v \<Rightarrow> C\<^sub>U nm (v # vs)"
| apply_V: "apply (V\<^sub>U x vs) v \<Rightarrow> V\<^sub>U x (v # vs)"
 \<comment> \<open>Context rules\<close>
| ctxt_C: "vs \<Rightarrow> vs' \<Longrightarrow> C\<^sub>U nm vs \<Rightarrow> C\<^sub>U nm vs'"
| ctxt_V: "vs \<Rightarrow> vs' \<Longrightarrow> V\<^sub>U x vs \<Rightarrow> V\<^sub>U x vs'"
| ctxt_Clo1: "f \<Rightarrow> f'   \<Longrightarrow> Clo f vs n \<Rightarrow> Clo f' vs n"
| ctxt_Clo3: "vs \<Rightarrow> vs' \<Longrightarrow> Clo f vs n \<Rightarrow> Clo f vs' n"
| ctxt_apply1: "s \<Rightarrow> s'   \<Longrightarrow> apply s t \<Rightarrow> apply s' t"
| ctxt_apply2: "t \<Rightarrow> t'   \<Longrightarrow> apply s t \<Rightarrow> apply s t'"
| ctxt_A_ML1: "f \<Rightarrow> f'   \<Longrightarrow> A\<^sub>M\<^sub>L f vs \<Rightarrow> A\<^sub>M\<^sub>L f' vs"
| ctxt_A_ML2: "vs \<Rightarrow> vs' \<Longrightarrow> A\<^sub>M\<^sub>L f vs \<Rightarrow> A\<^sub>M\<^sub>L f vs'"
| ctxt_list1: "v \<Rightarrow> v'   \<Longrightarrow> v#vs \<Rightarrow> v'#vs"
| ctxt_list2: "vs \<Rightarrow> vs' \<Longrightarrow> v#vs \<Rightarrow> v#vs'"

inductive_set
  Red_term :: "(tm * tm)set"
  and red_term :: "[tm, tm] => bool"  (infixl "\<Rightarrow>" 50)
  and reds_term :: "[tm, tm] => bool"  (infixl "\<Rightarrow>*" 50)
where
  "s \<Rightarrow> t \<equiv> (s, t) \<in> Red_term"
| "s \<Rightarrow>* t \<equiv> (s, t) \<in> Red_term^*"
 \<comment> \<open>function \texttt{term}\<close>
| term_C: "term (C\<^sub>U nm vs) \<Rightarrow> (C nm) \<bullet>\<bullet> (map term (rev vs))"
| term_V: "term (V\<^sub>U x vs) \<Rightarrow> (V x) \<bullet>\<bullet> (map term (rev vs))"
| term_Clo: "term(Clo vf vs n) \<Rightarrow> \<Lambda> (term (apply (lift 0 (Clo vf vs n)) (V\<^sub>U 0 [])))"
 \<comment> \<open>context rules\<close>
| ctxt_Lam: "t \<Rightarrow> t' \<Longrightarrow> \<Lambda> t \<Rightarrow> \<Lambda> t'"
| ctxt_At1: "s \<Rightarrow> s' \<Longrightarrow> s \<bullet> t \<Rightarrow> s' \<bullet> t"
| ctxt_At2: "t \<Rightarrow> t' \<Longrightarrow> s \<bullet> t \<Rightarrow> s \<bullet> t'"
| ctxt_term: "v \<Rightarrow> v' \<Longrightarrow> term v \<Rightarrow> term v'"


section "Kernel"

text\<open>First a special size function and some lemmas for the
termination proof of the kernel function.\<close>

fun size' :: "ml \<Rightarrow> nat" where
"size' (C\<^sub>M\<^sub>L nm) = 1" |
"size' (V\<^sub>M\<^sub>L X) = 1"  |
"size' (A\<^sub>M\<^sub>L v vs) = (size' v + (\<Sum>v\<leftarrow>vs. size' v))+1" |
"size' (Lam\<^sub>M\<^sub>L v) = size' v + 1" |
"size' (C\<^sub>U nm vs) = (\<Sum>v\<leftarrow>vs. size' v)+1" |
"size' (V\<^sub>U nm vs) = (\<Sum>v\<leftarrow>vs. size' v)+1" |
"size' (Clo f vs n) = (size' f + (\<Sum>v\<leftarrow>vs. size' v))+1" |
"size' (apply v w) = (size' v + size' w)+1"

lemma sum_list_size'[simp]:
 "v \<in> set vs \<Longrightarrow> size' v < Suc(sum_list (map size' vs))"
by(induct vs)(auto)

corollary cor_sum_list_size'[simp]:
 "v \<in> set vs \<Longrightarrow> size' v < Suc(m + sum_list (map size' vs))"
using sum_list_size'[of v vs] by arith

lemma size'_lift_ML: "size' (lift\<^sub>M\<^sub>L k v) = size' v"
apply(induct v arbitrary:k rule:size'.induct)
apply simp_all
   apply(rule arg_cong[where f = sum_list])
   apply(rule map_ext)
   apply simp
  apply(rule arg_cong[where f = sum_list])
  apply(rule map_ext)
  apply simp
 apply(rule arg_cong[where f = sum_list])
 apply(rule map_ext)
 apply simp
apply(rule arg_cong[where f = sum_list])
apply(rule map_ext)
apply simp
done

lemma size'_subst_ML[simp]:
 "\<forall>i j. size'(\<sigma> i) = 1 \<Longrightarrow> size' (subst\<^sub>M\<^sub>L \<sigma> v) = size' v"
apply(induct v arbitrary:\<sigma> rule:size'.induct)
apply simp_all
    apply(rule arg_cong[where f = sum_list])
    apply(rule map_ext)
    apply simp
   apply(erule meta_allE)
   apply(erule meta_mp)
   apply(simp add: size'_lift_ML split:nat.split)
  apply(rule arg_cong[where f = sum_list])
  apply(rule map_ext)
  apply simp
 apply(rule arg_cong[where f = sum_list])
 apply(rule map_ext)
 apply simp
apply(rule arg_cong[where f = sum_list])
apply(rule map_ext)
apply simp
done

lemma size'_lift[simp]: "size' (lift i v) = size' v"
apply(induct v arbitrary:i rule:size'.induct)
apply simp_all
   apply(rule arg_cong[where f = sum_list])
   apply(rule map_ext)
   apply simp
  apply(rule arg_cong[where f = sum_list])
  apply(rule map_ext)
  apply simp
 apply(rule arg_cong[where f = sum_list])
 apply(rule map_ext)
 apply simp
apply(rule arg_cong[where f = sum_list])
apply(rule map_ext)
apply simp
done

function kernel  :: "ml \<Rightarrow> tm"  ("_!" 300) where
"(C\<^sub>M\<^sub>L nm)! = C nm" |
"(A\<^sub>M\<^sub>L v vs)! = v! \<bullet>\<bullet> (map kernel (rev vs))" |
"(Lam\<^sub>M\<^sub>L v)! = \<Lambda> (((lift 0 v)[V\<^sub>U 0 []/0])!)" |
"(C\<^sub>U nm vs)! = (C nm) \<bullet>\<bullet> (map kernel (rev vs))" |
"(V\<^sub>U x vs)! = (V x) \<bullet>\<bullet> (map kernel (rev vs))" |
"(Clo f vs n)! = f! \<bullet>\<bullet> (map kernel (rev vs))" |
"(apply v w)! = v! \<bullet> (w!)" |
"(V\<^sub>M\<^sub>L X)! = undefined"
by pat_completeness auto
termination by(relation "measure size'") auto

primrec kernelt :: "tm \<Rightarrow> tm" ("_!" 300)
where
  "(C nm)! = C nm"
| "(V x)! = V x"
| "(s \<bullet> t)! = (s!) \<bullet> (t!)"
| "(\<Lambda> t)! = \<Lambda>(t!)"
| "(term v)! = v!"

abbreviation
  kernels :: "ml list \<Rightarrow> tm list" ("_!" 300) where
  "vs! \<equiv> map kernel vs"

lemma kernel_pure: assumes "pure t" shows "t! = t"
using assms by (induct) simp_all

lemma kernel_foldl_At[simp]: "(s \<bullet>\<bullet> ts)! = (s!) \<bullet>\<bullet> (map kernelt ts)"
by (induct ts arbitrary: s) simp_all

lemma kernelt_o_term[simp]: "(kernelt \<circ> term) = kernel"
by(rule ext) simp

lemma pure_foldl:
 "pure t \<Longrightarrow> \<forall>t\<in>set ts. pure t \<Longrightarrow> 
 (!!s t. pure s \<Longrightarrow> pure t \<Longrightarrow> pure(f s t)) \<Longrightarrow>
 pure(foldl f t ts)"
by(induct ts arbitrary: t) simp_all

lemma pure_kernel: fixes v :: ml shows "closed\<^sub>M\<^sub>L 0 v \<Longrightarrow> pure(v!)"
proof(induct v rule:kernel.induct)
  case (3 v)
  hence "closed\<^sub>M\<^sub>L (Suc 0) (lift 0 v)" by simp
  then have "subst\<^sub>M\<^sub>L (\<lambda>n. V\<^sub>U 0 []) (lift 0 v) = lift 0 v[V\<^sub>U 0 []/0]"
    by(rule subst_ML_coincidence) simp
  moreover have "closed\<^sub>M\<^sub>L 0 (subst\<^sub>M\<^sub>L (\<lambda>n. V\<^sub>U 0 []) (lift 0 v))"
    by(simp add: closed_ML_subst_ML)
  ultimately have "closed\<^sub>M\<^sub>L 0 (lift 0 v[V\<^sub>U 0 []/0])" by simp
  thus ?case using 3(1) by (simp add:pure_foldl)
qed (simp_all add:pure_foldl)

corollary subst_V_kernel: fixes v :: ml shows
  "closed\<^sub>M\<^sub>L 0 v \<Longrightarrow> subst V (v!) = v!"
by (metis pure_kernel subst_V)

lemma kernel_lift_tm: fixes v :: ml shows
  "closed\<^sub>M\<^sub>L 0 v \<Longrightarrow> (lift i v)! = lift i (v!)"
apply(induct v arbitrary: i rule: kernel.induct)
apply (simp_all add:list_eq_iff_nth_eq)
 apply(simp add: rev_nth)
defer
 apply(simp add: rev_nth)
 apply(simp add: rev_nth)
 apply(simp add: rev_nth)
apply(erule_tac x="Suc i" in meta_allE)
apply(erule meta_impE)
defer
apply (simp add:lift_subst_ML)
apply(subgoal_tac "lift (Suc i) \<circ> (\<lambda>n. if n = 0 then V\<^sub>U 0 [] else V\<^sub>M\<^sub>L (n - 1)) = (\<lambda>n. if n = 0 then V\<^sub>U 0 [] else V\<^sub>M\<^sub>L (n - 1))")
apply (simp add:lift_lift_ml)
apply(rule ext)
apply(simp)
apply(subst closed_ML_subst_ML2[of "1"])
apply(simp)
apply(simp)
apply(simp)
done

subsection "An auxiliary substitution"

text\<open>This function is only introduced to prove the involved susbtitution
lemma \<open>kernel_subst1\<close> below.\<close>

fun subst_ml :: "(nat \<Rightarrow> nat) \<Rightarrow> ml \<Rightarrow> ml" where
"subst_ml \<sigma> (C\<^sub>M\<^sub>L nm) = C\<^sub>M\<^sub>L nm" |
"subst_ml \<sigma> (V\<^sub>M\<^sub>L X) = V\<^sub>M\<^sub>L X" |
"subst_ml \<sigma> (A\<^sub>M\<^sub>L v vs) = A\<^sub>M\<^sub>L (subst_ml \<sigma> v) (map (subst_ml \<sigma>) vs)" |
"subst_ml \<sigma> (Lam\<^sub>M\<^sub>L v) = Lam\<^sub>M\<^sub>L (subst_ml \<sigma> v)" |
"subst_ml \<sigma> (C\<^sub>U nm vs) = C\<^sub>U nm (map (subst_ml \<sigma>) vs)" |
"subst_ml \<sigma> (V\<^sub>U x vs) = V\<^sub>U (\<sigma> x) (map (subst_ml \<sigma>) vs)" |
"subst_ml \<sigma> (Clo v vs n) = Clo (subst_ml \<sigma> v) (map (subst_ml \<sigma>) vs) n" |
"subst_ml \<sigma> (apply u v) = apply (subst_ml \<sigma> u) (subst_ml \<sigma> v)"

lemma lift_ML_subst_ml:
  "lift\<^sub>M\<^sub>L k (subst_ml \<sigma> v) = subst_ml \<sigma> (lift\<^sub>M\<^sub>L k v)"
apply (induct \<sigma> v arbitrary: k rule:subst_ml.induct)
apply (simp_all add:list_eq_iff_nth_eq)
done

lemma subst_ml_subst_ML:
  "subst_ml \<sigma> (subst\<^sub>M\<^sub>L \<sigma>' v) = subst\<^sub>M\<^sub>L (subst_ml \<sigma> o \<sigma>') (subst_ml \<sigma> v)"
apply (induct \<sigma>' v arbitrary: \<sigma> rule: subst_ML.induct)
apply(simp_all add:list_eq_iff_nth_eq)
apply(subgoal_tac "(subst_ml \<sigma>' \<circ> V\<^sub>M\<^sub>L 0 ## \<sigma>) = V\<^sub>M\<^sub>L 0 ## (subst_ml \<sigma>' \<circ> \<sigma>)")
apply simp
apply(rule ext)
apply(simp add: lift_ML_subst_ml)
done


text\<open>Maybe this should be the def of lift:\<close>
lemma lift_is_subst_ml: "lift k v = subst_ml (\<lambda>n. if n<k then n else n+1) v"
by(induct k v rule:lift_ml.induct)(simp_all add:list_eq_iff_nth_eq)

lemma subst_ml_comp:  "subst_ml \<sigma> (subst_ml \<sigma>' v) = subst_ml (\<sigma> o \<sigma>') v"
by(induct \<sigma>' v rule:subst_ml.induct)(simp_all add:list_eq_iff_nth_eq)

lemma subst_kernel:
  "closed\<^sub>M\<^sub>L 0 v \<Longrightarrow>  subst (\<lambda>n. V(\<sigma> n)) (v!) = (subst_ml \<sigma> v)!"
apply (induct v arbitrary: \<sigma> rule:kernel.induct)
apply (simp_all add:list_eq_iff_nth_eq)
 apply(simp add: rev_nth)
defer
 apply(simp add: rev_nth)
 apply(simp add: rev_nth)
 apply(simp add: rev_nth)
apply(erule_tac x="\<lambda>n. case n of 0 \<Rightarrow> 0 | Suc k \<Rightarrow> Suc(\<sigma> k)" in meta_allE)
apply(erule_tac meta_impE)
apply(rule closed_ML_subst_ML2[where k="Suc 0"])
apply (metis closed_ML_lift)
apply simp
apply(subgoal_tac "(\<lambda>n. V(case n of 0 \<Rightarrow> 0 | Suc k \<Rightarrow> Suc (\<sigma> k))) = (V 0 ## (\<lambda>n. V(\<sigma> n)))")
apply (simp add:subst_ml_subst_ML)
defer
apply(simp add:fun_eq_iff split:nat.split)
apply(simp add:lift_is_subst_ml subst_ml_comp)
apply(rule arg_cong[where f = kernel])
apply(subgoal_tac "(case_nat 0 (\<lambda>k. Suc (\<sigma> k)) \<circ> Suc) = Suc o \<sigma>")
prefer 2 apply(simp add:fun_eq_iff split:nat.split)
apply(subgoal_tac "(subst_ml (case_nat 0 (\<lambda>k. Suc (\<sigma> k))) \<circ>
               (\<lambda>n. if n = 0 then V\<^sub>U 0 [] else V\<^sub>M\<^sub>L (n - 1)))
             = (\<lambda>n. if n = 0 then V\<^sub>U 0 [] else V\<^sub>M\<^sub>L (n - 1))")
apply simp
apply(simp add: fun_eq_iff)
done

lemma if_cong0: "If x y z = If x y z"
by simp

lemma kernel_subst1:
  "closed\<^sub>M\<^sub>L 0 v \<Longrightarrow> closed\<^sub>M\<^sub>L (Suc 0) u \<Longrightarrow>
   kernel(u[v/0]) = (kernel((lift 0 u)[V\<^sub>U 0 []/0]))[v!/0]"
proof(induct u arbitrary:v rule:kernel.induct)
  case (3 w)
  show ?case (is "?L = ?R")
  proof -
    have "?L = \<Lambda>(lift 0 (w[lift\<^sub>M\<^sub>L 0 v/Suc 0])[V\<^sub>U 0 []/0] !)"
      by (simp cong:if_cong0)
    also have "\<dots> = \<Lambda>((lift 0 w)[lift\<^sub>M\<^sub>L 0 (lift 0 v)/Suc 0][V\<^sub>U 0 []/0]!)"
      by(simp only: lift_subst_ML1 lift_lift_ML_comm)
    also have "\<dots> = \<Lambda>(subst\<^sub>M\<^sub>L (\<lambda>n. if n=0 then V\<^sub>U 0 [] else
            if n=Suc 0 then lift 0 v else V\<^sub>M\<^sub>L (n - 2)) (lift 0 w) !)"
      apply simp
      apply(rule arg_cong[where f = kernel])
      apply(rule subst_ML_comp2)
      using 3
      apply auto
      done
    also have "\<dots> = \<Lambda>((lift 0 w)[V\<^sub>U 0 []/0][lift 0 v/0]!)"
      apply simp
      apply(rule arg_cong[where f = kernel])
      apply(rule subst_ML_comp2[symmetric])
      using 3
      apply auto
      done
    also have "\<dots> = \<Lambda>((lift_ml 0 ((lift_ml 0 w)[V\<^sub>U 0 []/0]))[V\<^sub>U 0 []/0]![(lift 0 v)!/0])"
      apply(rule arg_cong[where f = \<Lambda>])
      apply(rule 3(1))
      apply (metis closed_ML_lift 3(2))
      apply(subgoal_tac "closed\<^sub>M\<^sub>L (Suc(Suc 0)) w")
      defer
      using 3
      apply force
      apply(subgoal_tac  "closed\<^sub>M\<^sub>L (Suc (Suc 0)) (lift 0 w)")
      defer
      apply(erule closed_ML_lift)
      apply(erule closed_ML_subst_ML2)
      apply simp
      done
    also have "\<dots> = \<Lambda>((lift_ml 0 (lift_ml 0 w)[V\<^sub>U 1 []/0])[V\<^sub>U 0 []/0]![(lift 0 v)!/0])" (is "_ = ?M")
      apply(subgoal_tac "lift_ml 0 (lift_ml 0 w[V\<^sub>U 0 []/0])[V\<^sub>U 0 []/0] =
                         lift_ml 0 (lift_ml 0 w)[V\<^sub>U 1 []/0][V\<^sub>U 0 []/0]")
      apply simp
      apply(subst lift_subst_ML)
      apply(simp add:comp_def if_distrib[where f="lift_ml 0"] cong:if_cong)
      done
    finally have "?L = ?M" .
    have "?R = \<Lambda> (subst (V 0 ## subst_decr 0 (v!))
          (lift 0 (lift_ml 0 w[V\<^sub>U 0 []/Suc 0])[V\<^sub>U 0 []/0]!))"
      apply(subgoal_tac "(V\<^sub>M\<^sub>L 0 ## (\<lambda>n. if n = 0 then V\<^sub>U 0 [] else V\<^sub>M\<^sub>L (n - Suc 0))) = subst_decr_ML (Suc 0) (V\<^sub>U 0 [])")
      apply(simp cong:if_cong)
      apply(simp add:fun_eq_iff cons_ML_def split:nat.splits)
      done
    also have "\<dots> = \<Lambda> (subst (V 0 ## subst_decr 0 (v!))
          ((lift 0 (lift_ml 0 w))[V\<^sub>U 1 []/Suc 0][V\<^sub>U 0 []/0]!))"
      apply(subgoal_tac "lift 0 (lift 0 w[V\<^sub>U 0 []/Suc 0]) = lift 0 (lift 0 w)[V\<^sub>U 1 []/Suc 0]")
      apply simp
      apply(subst lift_subst_ML)
      apply(simp add:comp_def if_distrib[where f="lift_ml 0"] cong:if_cong)
      done
    also have "(lift_ml 0 (lift_ml 0 w))[V\<^sub>U 1 []/Suc 0][V\<^sub>U 0 []/0] =
               (lift 0 (lift_ml 0 w))[V\<^sub>U 0 []/0][V\<^sub>U 1 []/ 0]" (is "?l = ?r")
    proof -
      have "?l = subst\<^sub>M\<^sub>L (\<lambda>n. if n= 0 then V\<^sub>U 0 [] else if n = 1 then V\<^sub>U 1 [] else
                      V\<^sub>M\<^sub>L (n - 2))
               (lift_ml 0 (lift_ml 0 w))"
      by(auto intro!:subst_ML_comp2)
    also have "\<dots> = ?r" by(auto intro!:subst_ML_comp2[symmetric])
    finally show ?thesis .
  qed
  also have "\<Lambda> (subst (V 0 ## subst_decr 0 (v!)) (?r !)) = ?M"
  proof-
    have "subst (subst_decr (Suc 0) (lift_tm 0 (kernel v))) (lift_ml 0 (lift_ml 0 w)[V\<^sub>U 0 []/0][V\<^sub>U 1 []/0]!) =
    subst (subst_decr 0 (kernel(lift_ml 0 v))) (lift_ml 0 (lift_ml 0 w)[V\<^sub>U 1 []/0][V\<^sub>U 0 []/0]!)" (is "?a = ?b")
    proof-
      define pi where "pi n = (if n = 0 then 1 else if n = 1 then 0 else n)" for n :: nat
      have "(\<lambda>i. V (pi i)[lift 0 (v!)/0]) = subst_decr (Suc 0) (lift 0 (v!))"
        by(rule ext)(simp add:pi_def)
      hence "?a =
  subst (subst_decr 0 (lift_tm 0 (kernel v))) (subst (\<lambda> n. V(pi n)) (lift_ml 0 (lift_ml 0 w)[V\<^sub>U 0 []/0][V\<^sub>U 1 []/0]!))"
        apply(subst subst_comp[OF _ _ refl])
        prefer 3 apply simp
        using 3(3)
        apply simp
        apply(rule pure_kernel)
        apply(rule closed_ML_subst_ML2[where k="Suc 0"])
        apply(rule closed_ML_subst_ML2[where k="Suc(Suc 0)"])
        apply simp
        apply simp
        apply simp
        apply simp
        done
      also have "\<dots> =
 (subst_ml pi (lift_ml 0 (lift_ml 0 w)[V\<^sub>U 0 []/0][V\<^sub>U 1 []/0]))![lift_tm 0 (v!)/0]"
        apply(subst subst_kernel)
        using 3 apply auto
        apply(rule closed_ML_subst_ML2[where k="Suc 0"])
        apply(rule closed_ML_subst_ML2[where k="Suc(Suc 0)"])
        apply simp
        apply simp
        apply simp
        done
      also have "\<dots> = (subst_ml pi (lift_ml 0 (lift_ml 0 w)[V\<^sub>U 0 []/0][V\<^sub>U 1 []/0]))![lift 0 v!/0]"
      proof -
        have "lift 0 (v!) = lift 0 v!" by (metis 3(2) kernel_lift_tm)
        thus ?thesis by (simp cong:if_cong)
      qed
      also have "\<dots> = ?b"
      proof-
        have 1: "subst_ml pi (lift 0 (lift 0 w)) = lift 0 (lift 0 w)"
          apply(simp add:lift_is_subst_ml subst_ml_comp)
          apply(subgoal_tac "pi \<circ> (Suc \<circ> Suc) = (Suc \<circ> Suc)")
          apply(simp)
          apply(simp add:pi_def fun_eq_iff)
          done
        have "subst_ml pi (lift_ml 0 (lift_ml 0 w)[V\<^sub>U 0 []/0][V\<^sub>U 1 []/0]) =
             lift_ml 0 (lift_ml 0 w)[V\<^sub>U 1 []/0][V\<^sub>U 0 []/0]"
          apply(subst subst_ml_subst_ML)
          apply(subst subst_ml_subst_ML)
          apply(subst 1)
          apply(subst subst_ML_comp)
          apply(rule subst_ML_comp2[symmetric])
          apply(auto simp:pi_def)
          done
        thus ?thesis by simp
      qed
      finally show ?thesis .
    qed
    thus ?thesis by(simp cong:if_cong0 add:shift_subst_decr)
  qed
  finally have "?R = ?M" .
  then show "?L = ?R" using \<open>?L = ?M\<close> by metis
qed
qed (simp_all add:list_eq_iff_nth_eq, (simp_all add:rev_nth)?)


section \<open>Compiler \label{sec:Compiler}\<close>

axiomatization arity :: "cname \<Rightarrow> nat"

primrec compile :: "tm \<Rightarrow> (nat \<Rightarrow> ml) \<Rightarrow> ml"
where
  "compile (V x) \<sigma> = \<sigma> x"
| "compile (C nm) \<sigma> =
    (if arity nm > 0 then Clo (C\<^sub>M\<^sub>L nm) [] (arity nm) else A\<^sub>M\<^sub>L (C\<^sub>M\<^sub>L nm) [])"
| "compile (s \<bullet> t) \<sigma> = apply (compile s \<sigma>) (compile t \<sigma>)"
| "compile (\<Lambda> t) \<sigma> = Clo (Lam\<^sub>M\<^sub>L (compile t (V\<^sub>M\<^sub>L 0 ## \<sigma>))) [] 1"

text\<open>Compiler for open terms and for terms with fixed free variables:\<close>

definition "comp_open t = compile t V\<^sub>M\<^sub>L"
abbreviation "comp_fixed t \<equiv> compile t (\<lambda>i. V\<^sub>U i [])"

text\<open>Compiled rules:\<close>

lemma size_args_less_size_tm[simp]: "s \<in> set (args_tm t) \<Longrightarrow> size s < size t"
by(induct t) auto

fun comp_pat where
"comp_pat t =
   (case head_tm t of
     C nm \<Rightarrow> C\<^sub>U nm (map comp_pat (rev (args_tm t)))
   | V X \<Rightarrow> V\<^sub>M\<^sub>L X)"

declare comp_pat.simps[simp del] size_args_less_size_tm[simp del]

lemma comp_pat_V[simp]: "comp_pat(V X) = V\<^sub>M\<^sub>L X"
by(simp add:comp_pat.simps)

lemma comp_pat_C[simp]:
  "comp_pat(C nm \<bullet>\<bullet> ts) = C\<^sub>U nm (map comp_pat (rev ts))"
by(simp add:comp_pat.simps)

lemma comp_pat_C_Nil[simp]: "comp_pat(C nm) = C\<^sub>U nm []"
by(simp add:comp_pat.simps)


overloading compR \<equiv> compR
begin
  definition "compR \<equiv> (\<lambda>(nm,ts,t). (nm, map comp_pat (rev ts), comp_open t)) ` R"
end


lemma fv_ML_comp_open: "pure t \<Longrightarrow> fv\<^sub>M\<^sub>L(comp_open t) = fv t"
by(induct t pred:pure) (simp_all add:comp_open_def)

lemma fv_ML_comp_pat: "pattern t \<Longrightarrow> fv\<^sub>M\<^sub>L(comp_pat t) = fv t"
by(induct t pred:pattern)(simp_all add:comp_open_def)

lemma fv_compR_aux:
  "(nm,ts,t') : R \<Longrightarrow> x \<in> fv\<^sub>M\<^sub>L (comp_open t')
   \<Longrightarrow> \<exists>t\<in>set ts. x \<in> fv\<^sub>M\<^sub>L(comp_pat t)"
apply(frule pure_R)
apply(simp add:fv_ML_comp_open)
apply(frule (1) fv_R)
apply clarsimp
apply(rule bexI) prefer 2 apply assumption
apply(drule pattern_R)
apply(simp add:fv_ML_comp_pat)
done

lemma fv_compR:
  "(nm,vs,v) : compR \<Longrightarrow> x \<in> fv\<^sub>M\<^sub>L v \<Longrightarrow> \<exists>u\<in>set vs. x \<in> fv\<^sub>M\<^sub>L u"
by(fastforce simp add:compR_def image_def dest: fv_compR_aux)

lemma lift_compile:
  "pure t \<Longrightarrow> \<forall>\<sigma> k. lift k (compile t \<sigma>) = compile t (lift k \<circ> \<sigma>)"
apply(induct pred:pure)
apply simp_all
apply clarsimp
apply(rule_tac f = "compile t" in arg_cong)
apply(rule ext)
apply (clarsimp simp: lift_lift_ML_comm)
done

lemma subst_ML_compile:
  "pure t \<Longrightarrow> subst\<^sub>M\<^sub>L \<sigma>' (compile t \<sigma>) = compile t (subst\<^sub>M\<^sub>L \<sigma>' o \<sigma>)"
apply(induct arbitrary: \<sigma> \<sigma>' pred:pure)
apply simp_all
apply(erule_tac x="V\<^sub>M\<^sub>L 0 ## \<sigma>'" in meta_allE)
apply(erule_tac x= "V\<^sub>M\<^sub>L 0 ## (lift\<^sub>M\<^sub>L 0 \<circ> \<sigma>)" in meta_allE)
apply(rule_tac f = "compile t" in arg_cong)
apply(rule ext)
apply (auto simp add:subst_ML_ext lift_ML_subst_ML)
done

theorem kernel_compile:
  "pure t \<Longrightarrow> \<forall>i. \<sigma> i = V\<^sub>U i [] \<Longrightarrow> (compile t \<sigma>)! = t"
apply(induct arbitrary: \<sigma> pred:pure)
apply simp_all
apply(subst lift_compile) apply simp
apply(subst subst_ML_compile) apply simp
apply(subgoal_tac "(subst\<^sub>M\<^sub>L (\<lambda>n. if n = 0 then V\<^sub>U 0 [] else V\<^sub>M\<^sub>L (n - 1)) \<circ>
               (lift 0 \<circ> V\<^sub>M\<^sub>L 0 ## \<sigma>)) = (\<lambda>a. V\<^sub>U a [])")
apply(simp)
apply(rule ext)
apply(simp)
done

lemma kernel_subst_ML_pat:
  "pure t \<Longrightarrow> pattern t \<Longrightarrow> \<forall>i. closed\<^sub>M\<^sub>L 0 (\<sigma> i) \<Longrightarrow>
   (subst\<^sub>M\<^sub>L \<sigma> (comp_pat t))! = subst (kernel \<circ> \<sigma>) t"
apply(induct arbitrary: \<sigma> pred:pure)
apply simp_all
apply(frule pattern_At_decomp)
apply(frule pattern_AtD12)
apply clarsimp
apply(subst comp_pat.simps)
apply(simp add: rev_map)
done

lemma kernel_subst_ML:
  "pure t \<Longrightarrow> \<forall>i. closed\<^sub>M\<^sub>L 0 (\<sigma> i) \<Longrightarrow>
   (subst\<^sub>M\<^sub>L \<sigma> (comp_open t))! = subst (kernel \<circ> \<sigma>) t"
proof(induct arbitrary: \<sigma> pred:pure)
  case (Lam t)
  have "lift 0 o V\<^sub>M\<^sub>L = V\<^sub>M\<^sub>L" by (simp add:fun_eq_iff)
  hence "(subst\<^sub>M\<^sub>L \<sigma> (comp_open (\<Lambda> t)))! =
    \<Lambda> (subst\<^sub>M\<^sub>L (lift 0 \<circ> V\<^sub>M\<^sub>L 0 ## \<sigma>) (comp_open t)[V\<^sub>U 0 []/0]!)"
    using Lam by(simp add: lift_subst_ML comp_open_def lift_compile)
  also have "\<dots> = \<Lambda> (subst (V 0 ## (kernel \<circ> \<sigma>)) t)" using Lam
    by(simp add: subst_ML_comp subst_ext kernel_lift_tm)
  also have "\<dots> = subst (kernel o \<sigma>) (\<Lambda> t)" by simp
  finally show ?case .
qed (simp_all add:comp_open_def)

lemma kernel_subst_ML_pat_map:
  "\<forall>t \<in> set ts. pure t \<Longrightarrow> patterns ts \<Longrightarrow> \<forall>i. closed\<^sub>M\<^sub>L 0 (\<sigma> i) \<Longrightarrow>
   map kernel (map (subst\<^sub>M\<^sub>L \<sigma>) (map comp_pat ts)) =
   map (subst (kernel \<circ> \<sigma>)) ts"
by(simp add:list_eq_iff_nth_eq kernel_subst_ML_pat)

lemma compR_Red_tm: "(nm, vs, v) : compR \<Longrightarrow> \<forall> i. closed\<^sub>M\<^sub>L 0 (\<sigma> i)
  \<Longrightarrow> C nm \<bullet>\<bullet> (map (subst\<^sub>M\<^sub>L \<sigma>) (rev vs))! \<rightarrow>* (subst\<^sub>M\<^sub>L \<sigma> v)!"
apply(auto simp add:compR_def rev_map simp del: map_map)
apply(frule pure_R)
apply(subst kernel_subst_ML) apply fast+
apply(subst kernel_subst_ML_pat_map)
 apply fast
 apply(fast dest:pattern_R)
 apply assumption
apply(rule r_into_rtrancl)
apply(erule Red_tm.intros)
done


section "Correctness"

(* Without this special rule one "also" in the next proof *diverges*,
   probably because of HOU. *)
lemma eq_Red_tm_trans: "s = t \<Longrightarrow> t \<rightarrow> t' \<Longrightarrow> s \<rightarrow> t'"
by simp

text\<open>Soundness of reduction:\<close>
theorem fixes v :: ml shows Red_ml_sound:
  "v \<Rightarrow> v' \<Longrightarrow> closed\<^sub>M\<^sub>L 0 v \<Longrightarrow> v! \<rightarrow>* v'! \<and> closed\<^sub>M\<^sub>L 0 v'" and
  "vs \<Rightarrow> vs' \<Longrightarrow> \<forall>v\<in>set vs. closed\<^sub>M\<^sub>L 0 v \<Longrightarrow>
   vs! \<rightarrow>* vs'! \<and> (\<forall>v'\<in>set vs'. closed\<^sub>M\<^sub>L 0 v')"
proof(induct rule:Red_ml_Red_ml_list.inducts)
  fix u v
  let ?v = "A\<^sub>M\<^sub>L (Lam\<^sub>M\<^sub>L u) [v]"
  assume cl: "closed\<^sub>M\<^sub>L 0 (A\<^sub>M\<^sub>L (Lam\<^sub>M\<^sub>L u) [v])"
  let ?u' = "(lift_ml 0 u)[V\<^sub>U 0 []/0]"
  have "?v! = (\<Lambda>((?u')!)) \<bullet> (v !)" by simp
  also have "\<dots> \<rightarrow> (?u' !)[v!/0]" (is "_ \<rightarrow> ?R") by(rule Red_tm.intros)
  also(eq_Red_tm_trans) have "?R = u[v/0]!" using cl
    apply(cut_tac u = "u" and v = "v" in kernel_subst1)
    apply(simp_all)
    done
  finally have "kernel(A\<^sub>M\<^sub>L (Lam\<^sub>M\<^sub>L u) [v]) \<rightarrow>* kernel(u[v/0])" (is ?A)
    by(rule r_into_rtrancl)
  moreover have "closed\<^sub>M\<^sub>L 0 (u[v/0])" (is "?C")
  proof -
    let ?\<sigma> = "\<lambda>n. if n = 0 then v else V\<^sub>M\<^sub>L (n - 1)"
    let ?\<sigma>' = "\<lambda>n. v"
    have clu: "closed\<^sub>M\<^sub>L (Suc 0) u" and clv: "closed\<^sub>M\<^sub>L 0 v" using cl by simp+
    have "closed\<^sub>M\<^sub>L 0 (subst\<^sub>M\<^sub>L ?\<sigma>' u)"
      by (metis closed_ML_subst_ML clv)
    hence "closed\<^sub>M\<^sub>L 0 (subst\<^sub>M\<^sub>L ?\<sigma> u)"
      using subst_ML_coincidence[OF clu, of ?\<sigma> ?\<sigma>'] by auto
    thus ?thesis by simp
  qed
  ultimately show "?A \<and> ?C" ..
next
  fix \<sigma> :: "nat \<Rightarrow> ml" and nm vs v
  assume \<sigma>: "\<forall>i. closed\<^sub>M\<^sub>L 0 (\<sigma> i)"  and compR: "(nm, vs, v) \<in> compR"
  have "map (subst V) (map (subst\<^sub>M\<^sub>L \<sigma>) (rev vs)!) = map (subst\<^sub>M\<^sub>L \<sigma>) (rev vs)!"
    by(simp add:list_eq_iff_nth_eq subst_V_kernel closed_ML_subst_ML[OF \<sigma>])
  with compR_Red_tm[OF compR \<sigma>]
  have "(C nm) \<bullet>\<bullet> ((map (subst\<^sub>M\<^sub>L \<sigma>) (rev vs)) !) \<rightarrow>* (subst\<^sub>M\<^sub>L \<sigma> v)!"
    by(simp add:subst_V_kernel closed_ML_subst_ML[OF \<sigma>])
  hence "A\<^sub>M\<^sub>L (C\<^sub>M\<^sub>L nm) (map (subst\<^sub>M\<^sub>L \<sigma>) vs)! \<rightarrow>* subst\<^sub>M\<^sub>L \<sigma> v!" (is ?A)
    by(simp add:rev_map)
  moreover
  have "closed\<^sub>M\<^sub>L 0 (subst\<^sub>M\<^sub>L \<sigma> v)" (is ?C) by(metis closed_ML_subst_ML \<sigma>)
  ultimately show "?A \<and> ?C" ..
qed (auto simp:Reds_tm_list_foldl_At Red_tm_rev rev_map[symmetric])

theorem Red_term_sound:
  "t \<Rightarrow> t' \<Longrightarrow> closed\<^sub>M\<^sub>L 0 t \<Longrightarrow> kernelt t \<rightarrow>* kernelt t'  \<and> closed\<^sub>M\<^sub>L 0 t'"
proof(induct rule:Red_term.inducts)
  case term_C thus ?case
    by (auto simp:closed_tm_ML_foldl_At)
next
  case term_V thus ?case
    by (auto simp:closed_tm_ML_foldl_At)
next
  case (term_Clo vf vs n)
  hence "(lift 0 vf!) \<bullet>\<bullet> map kernel (rev (map (lift 0) vs))
         = lift 0 (vf! \<bullet>\<bullet> (rev vs)!)"
    apply (simp add:kernel_lift_tm list_eq_iff_nth_eq)
    apply(simp add:rev_nth rev_map kernel_lift_tm)
    done
  hence "term (Clo vf vs n)! \<rightarrow>*
       \<Lambda> (term (apply (lift 0 (Clo vf vs n)) (V\<^sub>U 0 [])))!"
    using term_Clo
    by(simp del:lift_foldl_At add: r_into_rtrancl Red_tm.intros(2))
  moreover
  have "closed\<^sub>M\<^sub>L 0 (\<Lambda> (term (apply (lift 0 (Clo vf vs n)) (V\<^sub>U 0 []))))"
    using term_Clo by simp
  ultimately show ?case ..
next
  case ctxt_term thus ?case by simp (metis Red_ml_sound)
qed auto

corollary kernel_inv:
 "(t :: tm) \<Rightarrow>* t' \<Longrightarrow> closed\<^sub>M\<^sub>L 0 t \<Longrightarrow> t! \<rightarrow>* t'! \<and> closed\<^sub>M\<^sub>L 0 t' "
apply(induct rule: rtrancl.induct)
apply (metis rtrancl_eq_or_trancl)
apply (metis Red_term_sound rtrancl_trans)
done

lemma  closed_ML_compile:
  "pure t \<Longrightarrow> \<forall>i. closed\<^sub>M\<^sub>L n (\<sigma> i) \<Longrightarrow> closed\<^sub>M\<^sub>L n (compile t \<sigma>)"
proof(induct arbitrary:n \<sigma> pred:pure)
  case (Lam t)
  have 1: "\<forall>i. closed\<^sub>M\<^sub>L (Suc n) ((V\<^sub>M\<^sub>L 0 ## \<sigma>) i)" using Lam(3-)
    by (auto simp: closed_ML_Suc)
  show ?case using Lam(2)[OF 1] by (simp del:apply_cons_ML)
qed simp_all

theorem nbe_correct: fixes t :: tm
assumes "pure t" and "term (comp_fixed t) \<Rightarrow>* t'" and "pure t'" shows "t \<rightarrow>* t'"
proof -
  have ML_cl: "closed\<^sub>M\<^sub>L 0 (term (comp_fixed t))"
    by (simp add: closed_ML_compile[OF \<open>pure t\<close>])
  have "(term (comp_fixed t))! = t"
    using kernel_compile[OF \<open>pure t\<close>] by simp
  moreover have "term (comp_fixed t)! \<rightarrow>* t'!"
    using kernel_inv[OF assms(2) ML_cl] by auto
  ultimately have "t \<rightarrow>* t'!" by simp
  thus ?thesis using kernel_pure[OF \<open>pure t'\<close>] by simp
qed


section "Normal Forms"

inductive normal :: "tm \<Rightarrow> bool" where
"\<forall>t\<in>set ts. normal t \<Longrightarrow> normal(V x \<bullet>\<bullet> ts)" |
"normal t \<Longrightarrow> normal(\<Lambda> t)" |
"\<forall>t\<in>set ts. normal t \<Longrightarrow>
 \<forall>\<sigma>. \<forall>(nm',ls,r)\<in>R. \<not>(nm = nm' \<and> take (size ls) ts = map (subst \<sigma>) ls)
 \<Longrightarrow> normal(C nm \<bullet>\<bullet> ts)"

fun C_normal_ML :: "ml \<Rightarrow> bool" ("C'_normal\<^sub>M\<^sub>L") where
"C_normal\<^sub>M\<^sub>L(C\<^sub>U nm vs) =
  ((\<forall>v\<in>set vs. C_normal\<^sub>M\<^sub>L v) \<and> no_match_compR nm vs)" |
"C_normal\<^sub>M\<^sub>L (C\<^sub>M\<^sub>L _) = True" |
"C_normal\<^sub>M\<^sub>L (V\<^sub>M\<^sub>L _) = True" |
"C_normal\<^sub>M\<^sub>L (A\<^sub>M\<^sub>L v vs) = (C_normal\<^sub>M\<^sub>L v \<and> (\<forall>v \<in> set vs. C_normal\<^sub>M\<^sub>L v))" |
"C_normal\<^sub>M\<^sub>L (Lam\<^sub>M\<^sub>L v) = C_normal\<^sub>M\<^sub>L v" |
"C_normal\<^sub>M\<^sub>L (V\<^sub>U x vs) = (\<forall>v \<in> set vs. C_normal\<^sub>M\<^sub>L v)" |
"C_normal\<^sub>M\<^sub>L (Clo v vs _) = (C_normal\<^sub>M\<^sub>L v \<and> (\<forall>v \<in> set vs. C_normal\<^sub>M\<^sub>L v))" |
"C_normal\<^sub>M\<^sub>L (apply u v) = (C_normal\<^sub>M\<^sub>L u \<and> C_normal\<^sub>M\<^sub>L v)"

fun size_tm :: "tm \<Rightarrow> nat" where
"size_tm (C _) = 1" |
"size_tm (At s t) = size_tm s + size_tm t + 1" |
"size_tm _ = 0"

lemma size_tm_foldl_At: "size_tm(t \<bullet>\<bullet> ts) = size_tm t + size_list size_tm ts"
by (induct ts arbitrary:t) auto

lemma termination_no_match:
  "i < length ss \<Longrightarrow> ss ! i = C nm \<bullet>\<bullet> ts
   \<Longrightarrow> sum_list (map size_tm ts) < sum_list (map size_tm ss)"
apply(subgoal_tac "C nm \<bullet>\<bullet> ts : set ss")
 apply(drule sum_list_map_remove1[of _ _ size_tm])
apply(simp add:size_tm_foldl_At size_list_conv_sum_list)
apply (metis in_set_conv_nth)
done

declare conj_cong [fundef_cong]

function no_match :: "tm list \<Rightarrow> tm list \<Rightarrow> bool" where
"no_match ps ts =
  (\<exists>i < min (size ts) (size ps).
   \<exists>nm nm' rs rs'. ps!i = (C nm) \<bullet>\<bullet> rs \<and> ts!i = (C nm') \<bullet>\<bullet> rs' \<and>
      (nm=nm' \<longrightarrow> no_match rs rs'))"
by pat_completeness auto
termination
apply(relation "measure(%(ts::tm list,_). \<Sum>t\<leftarrow>ts. size_tm t)")
apply (auto simp:termination_no_match)
done

declare no_match.simps[simp del]

abbreviation
"no_match_R nm ts \<equiv> \<forall>(nm',ps,t)\<in> R. nm=nm' \<longrightarrow> no_match ps ts"


lemma no_match: "no_match ps ts \<Longrightarrow> \<not>(\<exists>\<sigma>. map (subst \<sigma>) ps = ts)"
proof(induct ps ts rule:no_match.induct)
  case (1 ps ts)
  thus ?case
    apply auto
    apply(subst (asm) no_match.simps[of ps])
    apply fastforce
    done
qed

lemma no_match_take: "no_match ps ts \<Longrightarrow> no_match ps (take (size ps) ts)"
apply(subst (asm) no_match.simps)
apply(subst no_match.simps)
apply fastforce
done

fun dterm_ML :: "ml \<Rightarrow> tm" ("dterm\<^sub>M\<^sub>L") where
"dterm\<^sub>M\<^sub>L (C\<^sub>U nm vs) = C nm \<bullet>\<bullet> map dterm\<^sub>M\<^sub>L (rev vs)" |
"dterm\<^sub>M\<^sub>L _ = V 0"

fun dterm :: "tm \<Rightarrow> tm" where
"dterm (V n) = V n" |
"dterm (C nm) = C nm" |
"dterm (s \<bullet> t) = dterm s \<bullet> dterm t" |
"dterm (\<Lambda> t) = \<Lambda> (dterm t)" |
"dterm (term v) = dterm\<^sub>M\<^sub>L v"

lemma dterm_pure[simp]: "pure t \<Longrightarrow> dterm t = t"
by (induct pred:pure) auto

lemma map_dterm_pure[simp]: "\<forall>t\<in>set ts. pure t \<Longrightarrow> map dterm ts = ts"
by (induct ts) auto

lemma map_dterm_term[simp]: "map dterm (map term vs) = map dterm\<^sub>M\<^sub>L vs"
by (induct vs) auto

lemma dterm_foldl_At[simp]: "dterm(t \<bullet>\<bullet> ts) = dterm t \<bullet>\<bullet> map dterm ts"
by(induct ts arbitrary: t) auto

lemma no_match_coincide:
  "no_match\<^sub>M\<^sub>L ps vs \<Longrightarrow>
  no_match (map dterm\<^sub>M\<^sub>L (rev ps)) (map dterm\<^sub>M\<^sub>L (rev vs))"
apply(induct ps vs rule:no_match_ML.induct)
apply(rotate_tac 1)
apply(subst (asm) no_match_ML.simps)
apply (elim exE conjE)
apply(case_tac "nm=nm'")
prefer 2
apply(subst no_match.simps)
apply(rule_tac x=i in exI)
apply rule
apply (simp (no_asm))
apply (metis min_less_iff_conj)
apply(simp add:min_less_iff_conj nth_map)
apply safe
apply(erule_tac x=i in meta_allE)
apply(erule_tac x=nm' in meta_allE)
apply(erule_tac x=nm' in meta_allE)
apply(erule_tac x="vs" in meta_allE)
apply(erule_tac x="vs'" in meta_allE)
apply(subst no_match.simps)
apply(rule_tac x=i in exI)
apply rule
apply (simp (no_asm))
apply (metis min_less_iff_conj)
apply(rule_tac x=nm' in exI)
apply(rule_tac x=nm' in exI)
apply(rule_tac x="map dterm\<^sub>M\<^sub>L (rev vs)" in exI)
apply(rule_tac x="map dterm\<^sub>M\<^sub>L (rev vs')" in exI)
apply(simp)
done

lemma dterm_ML_comp_patD:
  "pattern t \<Longrightarrow> dterm\<^sub>M\<^sub>L (comp_pat t) = C nm \<bullet>\<bullet> rs \<Longrightarrow> \<exists>ts. t = C nm \<bullet>\<bullet> ts"
by(induct pred:pattern) simp_all

lemma no_match_R_coincide_aux[rule_format]: "patterns ts \<Longrightarrow>
  no_match (map (dterm\<^sub>M\<^sub>L \<circ> comp_pat) ts) rs \<longrightarrow> no_match ts rs"
apply(induct ts rs rule:no_match.induct)
apply(subst (1 2) no_match.simps)
apply clarsimp
apply(rule_tac x=i in exI)
apply simp
apply(rule_tac x=nm in exI)
apply(cut_tac t = "ps!i" in dterm_ML_comp_patD, simp, assumption)
apply(clarsimp)
apply(erule_tac x = i in meta_allE)
apply(erule_tac x = nm' in meta_allE)
apply(erule_tac x = nm' in meta_allE)
apply(erule_tac x = tsa in meta_allE)
apply(erule_tac x = rs' in meta_allE)
apply (simp add:rev_map)
apply (metis in_set_conv_nth pattern_At_vecD)
done

lemma no_match_R_coincide:
  "no_match_compR nm (rev vs) \<Longrightarrow> no_match_R nm (map dterm\<^sub>M\<^sub>L vs)"
apply auto
apply(drule_tac x="(nm, map comp_pat (rev aa), comp_open b)" in bspec)
 unfolding compR_def
 apply (simp add:image_def) 
 apply (force)
apply (simp)
apply(drule no_match_coincide)
apply(frule pure_R)
apply(drule pattern_R)
apply(clarsimp simp add: rev_map no_match.simps[of _ "map dterm\<^sub>M\<^sub>L vs"])
apply(rule_tac x=i in exI)
apply simp
apply(cut_tac t = "aa!i" in dterm_ML_comp_patD, simp, assumption)
apply clarsimp
apply(auto simp: rev_map)
apply(rule no_match_R_coincide_aux)
prefer 2 apply assumption
apply (metis in_set_conv_nth pattern_At_vecD)
done


inductive C_normal :: "tm \<Rightarrow> bool" where
"\<forall>t\<in>set ts. C_normal t \<Longrightarrow> C_normal(V x \<bullet>\<bullet> ts)" |
"C_normal t \<Longrightarrow> C_normal(\<Lambda> t)" |
"C_normal\<^sub>M\<^sub>L v \<Longrightarrow> C_normal(term v)" |
"\<forall>t\<in>set ts. C_normal t \<Longrightarrow> no_match_R nm (map dterm ts)
 \<Longrightarrow> C_normal(C nm \<bullet>\<bullet> ts)"

declare C_normal.intros[simp]

lemma C_normal_term[simp]: "C_normal(term v) = C_normal\<^sub>M\<^sub>L v"
apply (auto)
apply(erule C_normal.cases)
apply auto
done

lemma [simp]: "C_normal(\<Lambda> t) = C_normal t"
apply (auto)
apply(erule C_normal.cases)
apply auto
done

lemma [simp]: "C_normal(V x)"
using C_normal.intros(1)[of "[]" x]
by simp

lemma [simp]: "dterm (dterm\<^sub>M\<^sub>L v) = dterm\<^sub>M\<^sub>L v"
apply(induct v rule:dterm_ML.induct)
apply simp_all
done

lemma "u\<Rightarrow>(v::ml) \<Longrightarrow> True" and
  Red_ml_list_length: "vs \<Rightarrow> vs' \<Longrightarrow> length vs = length vs'"
by(induct rule: Red_ml_Red_ml_list.inducts) simp_all

lemma "(v::ml) \<Rightarrow> v' \<Longrightarrow> True" and
  Red_ml_list_nth: "(vs::ml list) \<Rightarrow> vs'
  \<Longrightarrow> \<exists>v' k. k<size vs \<and> vs!k \<Rightarrow> v' \<and> vs' = vs[k := v']"
apply (induct rule: Red_ml_Red_ml_list.inducts)
apply (auto split:nat.splits)
done

lemma Red_ml_list_pres_no_match:
  "no_match\<^sub>M\<^sub>L ps vs \<Longrightarrow> vs \<Rightarrow> vs' \<Longrightarrow> no_match\<^sub>M\<^sub>L ps vs'"
proof(induct ps vs arbitrary: vs' rule:no_match_ML.induct)
  case (1 vs os)
  show ?case using 1(2-3)
apply-
apply(frule Red_ml_list_length)
apply(rotate_tac -2)
apply(subst (asm) no_match_ML.simps)
apply clarify
apply(rename_tac i nm nm' us us')
apply(subst no_match_ML.simps)
apply(rule_tac x=i in exI)
apply (simp)
apply(drule Red_ml_list_nth)
apply clarify
apply(rename_tac k)
apply(case_tac "k = length os - Suc i")
prefer 2
apply(rule_tac x=nm' in exI)
apply(rule_tac x=us' in exI)
apply (simp add: rev_nth nth_list_update)
apply (simp add: rev_nth)
apply(erule Red_ml.cases)
apply simp_all
apply(fastforce intro: 1(1) simp add:rev_nth)
done
qed

lemma no_match_ML_subst_ML[rule_format]:
  "\<forall>v\<in>set vs. \<forall>x\<in>fv\<^sub>M\<^sub>L v. C_normal\<^sub>M\<^sub>L (\<sigma> x) \<Longrightarrow>
   no_match\<^sub>M\<^sub>L ps vs \<longrightarrow> no_match\<^sub>M\<^sub>L ps (map (subst\<^sub>M\<^sub>L \<sigma>) vs)"
apply(induct ps vs rule:no_match_ML.induct)
apply simp
apply(subst (1 2) no_match_ML.simps)
apply clarsimp
apply(rule_tac x=i in exI)
apply simp
apply(rule_tac x=nm' in exI)
apply(rule_tac x="map (subst\<^sub>M\<^sub>L \<sigma>) vs'" in exI)
apply (auto simp:rev_nth)
apply(erule_tac x = i in meta_allE)
apply(erule_tac x = nm' in meta_allE)
apply(erule_tac x = nm' in meta_allE)
apply(erule_tac x = vs in meta_allE)
apply(erule_tac x = vs' in meta_allE)
apply simp
apply (metis UN_I fv_ML.simps(5) in_set_conv_nth length_rev rev_nth set_rev)
done

lemma lift_is_CUD:
  "lift\<^sub>M\<^sub>L k v = C\<^sub>U nm vs' \<Longrightarrow> \<exists>vs. v = C\<^sub>U nm vs \<and> vs' = map (lift\<^sub>M\<^sub>L k) vs"
by(cases v) auto

lemma no_match_ML_lift_ML:
  "no_match\<^sub>M\<^sub>L ps (map (lift\<^sub>M\<^sub>L k) vs) = no_match\<^sub>M\<^sub>L ps vs"
apply(induct ps vs rule:no_match_ML.induct)
apply simp
apply(subst (1 2) no_match_ML.simps)
apply rule
 apply clarsimp
 apply(rule_tac x=i in exI)
 apply (simp add:rev_nth)
 apply(drule lift_is_CUD)
 apply fastforce
apply clarsimp
apply(rule_tac x=i in exI)
apply simp
apply(rule_tac x=nm' in exI)
apply(rule_tac x="map (lift\<^sub>M\<^sub>L k) vs'" in exI)
apply (fastforce simp:rev_nth)
done

lemma C_normal_ML_lift_ML: "C_normal\<^sub>M\<^sub>L(lift\<^sub>M\<^sub>L k v) = C_normal\<^sub>M\<^sub>L v"
by(induct v arbitrary: k rule:C_normal_ML.induct)(auto simp:no_match_ML_lift_ML)

lemma no_match_compR_Cons:
  "no_match_compR nm vs \<Longrightarrow> no_match_compR nm (v # vs)"
apply auto
apply(drule bspec, assumption)
apply simp
apply(subst (asm) no_match_ML.simps)
apply(subst no_match_ML.simps)
apply clarsimp
apply(rule_tac x=i in exI)
apply (simp add:nth_append)
done

lemma C_normal_ML_comp_open: "pure t \<Longrightarrow> C_normal\<^sub>M\<^sub>L(comp_open t)"
by (induct pred:pure) (auto simp:comp_open_def)

lemma C_normal_compR_rhs: "(nm, vs, v) \<in> compR \<Longrightarrow> C_normal\<^sub>M\<^sub>L v"
by(auto simp: compR_def image_def Bex_def pure_R C_normal_ML_comp_open)


lemma C_normal_ML_subst_ML:
  "C_normal\<^sub>M\<^sub>L (subst\<^sub>M\<^sub>L \<sigma> v) \<Longrightarrow> (\<forall>x\<in>fv\<^sub>M\<^sub>L v. C_normal\<^sub>M\<^sub>L (\<sigma> x))"
proof(induct \<sigma> v rule:subst_ML.induct)
  case 4 thus ?case
    by(simp del:apply_cons_ML)(force simp add: C_normal_ML_lift_ML)
      (* weird - force suffices in apply style *)
qed auto

lemma C_normal_ML_subst_ML_iff: "C_normal\<^sub>M\<^sub>L v \<Longrightarrow>
  C_normal\<^sub>M\<^sub>L (subst\<^sub>M\<^sub>L \<sigma> v) \<longleftrightarrow> (\<forall>x\<in>fv\<^sub>M\<^sub>L v. C_normal\<^sub>M\<^sub>L (\<sigma> x))"
proof(induct \<sigma> v rule:subst_ML.induct)
  case 4 thus ?case
    by(simp del:apply_cons_ML)(force simp add: C_normal_ML_lift_ML)
      (* weird - force suffices in apply style *)
next
  case 5 thus ?case by simp (blast intro: no_match_ML_subst_ML)
qed auto

lemma C_normal_ML_inv: "v \<Rightarrow> v' \<Longrightarrow> C_normal\<^sub>M\<^sub>L v \<Longrightarrow> C_normal\<^sub>M\<^sub>L v'" and
      "vs \<Rightarrow> vs' \<Longrightarrow> \<forall>v\<in>set vs. C_normal\<^sub>M\<^sub>L v \<Longrightarrow> \<forall>v'\<in>set vs'. C_normal\<^sub>M\<^sub>L v'"
apply(induct rule:Red_ml_Red_ml_list.inducts)
apply(simp_all add: C_normal_ML_subst_ML_iff)
  apply(metis C_normal_ML_subst_ML C_normal_compR_rhs
        fv_compR C_normal_ML_subst_ML_iff)
 apply(blast intro!:no_match_compR_Cons)
apply(blast dest:Red_ml_list_pres_no_match)
done


lemma Red_term_hnf_induct[consumes 1]:
assumes "(t::tm) \<Rightarrow> t'"
  "\<And>nm vs ts. P ((term (C\<^sub>U nm vs)) \<bullet>\<bullet> ts) ((C nm \<bullet>\<bullet> map term (rev vs)) \<bullet>\<bullet> ts)"
  "\<And>x vs ts. P (term (V\<^sub>U x vs) \<bullet>\<bullet> ts) ((V x \<bullet>\<bullet> map term (rev vs)) \<bullet>\<bullet> ts)"
  "\<And>vf vs n ts.
    P (term (Clo vf vs n) \<bullet>\<bullet> ts)
     ((\<Lambda> (term (apply (lift 0 (Clo vf vs n)) (V\<^sub>U 0 [])))) \<bullet>\<bullet> ts)"
  "\<And>t t' ts. \<lbrakk>t \<Rightarrow> t'; P t t'\<rbrakk> \<Longrightarrow> P (\<Lambda> t \<bullet>\<bullet> ts) (\<Lambda> t' \<bullet>\<bullet> ts)"
  "\<And>v v' ts. v \<Rightarrow> v' \<Longrightarrow> P (term v \<bullet>\<bullet> ts) (term v' \<bullet>\<bullet> ts)"
  "\<And>x i t' ts. i<size ts \<Longrightarrow> ts!i \<Rightarrow> t' \<Longrightarrow> P (ts!i) (t')
    \<Longrightarrow> P (V x  \<bullet>\<bullet> ts) (V x \<bullet>\<bullet> ts[i:=t'])"
  "\<And>nm i t' ts. i<size ts \<Longrightarrow> ts!i \<Rightarrow> t' \<Longrightarrow> P (ts!i) (t')
    \<Longrightarrow> P (C nm  \<bullet>\<bullet> ts) (C nm \<bullet>\<bullet> ts[i:=t'])"
  "\<And>t i t' ts. i<size ts \<Longrightarrow> ts!i \<Rightarrow> t' \<Longrightarrow> P (ts!i) (t')
    \<Longrightarrow> P (\<Lambda> t \<bullet>\<bullet> ts) (\<Lambda> t \<bullet>\<bullet> ts[i:=t'])"
  "\<And>v i t' ts. i<size ts \<Longrightarrow> ts!i \<Rightarrow> t' \<Longrightarrow> P (ts!i) (t')
    \<Longrightarrow> P (term v  \<bullet>\<bullet> ts) (term v \<bullet>\<bullet> (ts[i:=t']))"
shows "P t t'"
proof-
  { fix ts from assms have "P (t \<bullet>\<bullet> ts) (t' \<bullet>\<bullet> ts)"
    proof(induct arbitrary: ts rule:Red_term.induct)
      case term_C thus ?case by metis
    next
      case term_V thus ?case by metis
    next
      case term_Clo thus ?case by metis
    next
      case ctxt_Lam thus ?case by simp (metis foldl_Nil)
    next
      case (ctxt_At1 s s' t ts)
      thus ?case using ctxt_At1(2)[of "t#ts"] by simp
    next
      case (ctxt_At2 t t' s ts)
      { fix n rs assume "s = V n \<bullet>\<bullet> rs"
        hence ?case using ctxt_At2(8)[of "size rs" "rs @ t # ts" t' n] ctxt_At2
          by simp (metis foldl_Nil)
      } moreover
      { fix nm rs assume "s = C nm \<bullet>\<bullet> rs"
        hence ?case using ctxt_At2(9)[of "size rs" "rs @ t # ts" t' nm] ctxt_At2
          by simp (metis foldl_Nil)
      } moreover
      { fix r rs assume "s = \<Lambda> r \<bullet>\<bullet> rs"
        hence ?case using ctxt_At2(10)[of "size rs" "rs @ t # ts" t'] ctxt_At2
          by simp (metis foldl_Nil)
      } moreover
      { fix v rs assume "s = term v \<bullet>\<bullet> rs"
        hence ?case using ctxt_At2(11)[of "size rs" "rs @ t # ts" t'] ctxt_At2
          by simp (metis foldl_Nil)
      } ultimately show ?case using tm_vector_cases[of s] by blast
    qed
  }
  from this[of "[]"] show ?thesis by simp
qed

corollary Red_term_hnf_cases[consumes 1]:
assumes "(t::tm) \<Rightarrow> t'"
  "\<And>nm vs ts.
  t = term (C\<^sub>U nm vs) \<bullet>\<bullet> ts \<Longrightarrow> t' = (C nm \<bullet>\<bullet> map term (rev vs)) \<bullet>\<bullet> ts \<Longrightarrow> P"
  "\<And>x vs ts.
  t = term (V\<^sub>U x vs) \<bullet>\<bullet> ts \<Longrightarrow> t' = (V x \<bullet>\<bullet> map term (rev vs)) \<bullet>\<bullet> ts \<Longrightarrow> P"
  "\<And>vf vs n ts. t = term (Clo vf vs n) \<bullet>\<bullet> ts \<Longrightarrow>
     t' = \<Lambda> (term (apply (lift 0 (Clo vf vs n)) (V\<^sub>U 0 []))) \<bullet>\<bullet> ts \<Longrightarrow> P"
  "\<And>s s' ts. t = \<Lambda> s \<bullet>\<bullet> ts \<Longrightarrow> t' = \<Lambda> s' \<bullet>\<bullet> ts \<Longrightarrow> s \<Rightarrow> s' \<Longrightarrow> P"
  "\<And>v v' ts. t = term v \<bullet>\<bullet> ts \<Longrightarrow> t' = term v' \<bullet>\<bullet> ts \<Longrightarrow> v \<Rightarrow> v' \<Longrightarrow> P"
  "\<And>x i r' ts. i<size ts \<Longrightarrow> ts!i \<Rightarrow> r'
    \<Longrightarrow> t = V x  \<bullet>\<bullet> ts \<Longrightarrow> t' = V x \<bullet>\<bullet> ts[i:=r'] \<Longrightarrow> P"
  "\<And>nm i r' ts. i<size ts \<Longrightarrow> ts!i \<Rightarrow> r'
    \<Longrightarrow> t = C nm  \<bullet>\<bullet> ts \<Longrightarrow> t' = C nm \<bullet>\<bullet> ts[i:=r'] \<Longrightarrow> P"
  "\<And>s i r' ts. i<size ts \<Longrightarrow> ts!i \<Rightarrow> r'
    \<Longrightarrow> t = \<Lambda> s \<bullet>\<bullet> ts \<Longrightarrow> t' = \<Lambda> s \<bullet>\<bullet> ts[i:=r'] \<Longrightarrow> P"
  "\<And>v i r' ts. i<size ts \<Longrightarrow> ts!i \<Rightarrow> r'
    \<Longrightarrow> t = term v  \<bullet>\<bullet> ts \<Longrightarrow> t' = term v \<bullet>\<bullet> (ts[i:=r']) \<Longrightarrow> P"
shows "P" using assms
apply -
apply(induct rule:Red_term_hnf_induct)
apply metis+
done


lemma [simp]: "C_normal(term v \<bullet>\<bullet> ts) \<longleftrightarrow> C_normal\<^sub>M\<^sub>L v \<and> ts = []"
by(fastforce elim: C_normal.cases)

lemma [simp]: "C_normal(\<Lambda> t \<bullet>\<bullet> ts) \<longleftrightarrow> C_normal t \<and> ts = []"
by(fastforce elim: C_normal.cases)

lemma [simp]: "C_normal(C nm \<bullet>\<bullet> ts) \<longleftrightarrow>
  (\<forall>t\<in>set ts. C_normal t) \<and> no_match_R nm (map dterm ts)"
by(fastforce elim: C_normal.cases)

lemma [simp]: "C_normal(V x \<bullet>\<bullet> ts) \<longleftrightarrow> (\<forall>t \<in> set ts. C_normal t)"
by(fastforce elim: C_normal.cases)

lemma no_match_ML_lift:
  "no_match\<^sub>M\<^sub>L ps vs \<longrightarrow> no_match\<^sub>M\<^sub>L ps (map (lift k) vs)"
apply(induct ps vs rule:no_match_ML.induct)
apply simp
apply(subst (1 2) no_match_ML.simps)
apply clarsimp
apply(rule_tac x=i in exI)
apply simp
apply(rule_tac x=nm' in exI)
apply(rule_tac x="map (lift k) vs'" in exI)
apply (fastforce simp:rev_nth)
done

lemma no_match_compR_lift:
  "no_match_compR nm vs \<Longrightarrow> no_match_compR nm (map (lift k) vs)"
by (fastforce simp: no_match_ML_lift)

lemma [simp]: "C_normal\<^sub>M\<^sub>L v \<Longrightarrow> C_normal\<^sub>M\<^sub>L(lift k v)"
apply(induct v arbitrary:k rule:lift_ml.induct)
apply(simp_all add:no_match_compR_lift)
done

declare [[simp_depth_limit = 10]]

lemma Red_term_pres_no_match:
  "\<lbrakk>i < length ts; ts ! i \<Rightarrow> t'; no_match ps dts; dts = (map dterm ts)\<rbrakk>
   \<Longrightarrow> no_match ps (map dterm (ts[i := t']))"
proof(induct ps dts arbitrary: ts i t' rule:no_match.induct)
  case (1 ps dts ts i t')
  from \<open>no_match ps dts\<close> \<open>dts = map dterm ts\<close>
  obtain j nm nm' rs rs' where ob: "j < size ts" "j < size ps"
    "ps!j = C nm \<bullet>\<bullet> rs" "dterm (ts!j) = C nm' \<bullet>\<bullet> rs'"
    "nm = nm' \<longrightarrow> no_match rs rs'"
    by (subst (asm) no_match.simps) fastforce
  show ?case
  proof (subst no_match.simps)
    show "\<exists>k<min (length (map dterm (ts[i := t']))) (length ps).
       \<exists>nm nm' rs rs'. ps!k  = C nm \<bullet>\<bullet> rs \<and>
         map dterm (ts[i := t']) ! k = C nm' \<bullet>\<bullet> rs' \<and>
        (nm = nm' \<longrightarrow> no_match rs rs')"
      (is "\<exists>k < ?m. ?P k")
    proof-
      { assume [simp]: "j=i"
        have "\<exists>rs'. dterm t' = C nm' \<bullet>\<bullet> rs' \<and> (nm = nm' \<longrightarrow> no_match rs rs')"
          using \<open>ts ! i \<Rightarrow> t'\<close>
        proof(cases rule:Red_term_hnf_cases)
          case (5 v v' ts'')
          then obtain vs where [simp]:
            "v = C\<^sub>U nm' vs" "rs' = map dterm\<^sub>M\<^sub>L (rev vs) @ map dterm ts''"
            using ob by(cases v) auto
          obtain vs' where [simp]: "v' = C\<^sub>U nm' vs'" "vs \<Rightarrow> vs'"
            using \<open>v\<Rightarrow>v'\<close> by(rule Red_ml.cases) auto
          obtain v' k where [arith]: "k<size vs" and "vs!k \<Rightarrow> v'"
            and [simp]: "vs' = vs[k := v']"
            using Red_ml_list_nth[OF \<open>vs\<Rightarrow>vs'\<close>] by fastforce
          show ?thesis (is "\<exists>rs'. ?P rs' \<and> ?Q rs'")
          proof
            let ?rs' = "map dterm ((map term (rev vs) @ ts'')[(size vs - k - 1):=term v'])"
            have "?P ?rs'" using ob 5
              by(simp add: list_update_append map_update[symmetric] rev_update)
            moreover have "?Q ?rs'"
              apply rule
              apply(rule "1.hyps"[OF _ ob(3)])
              using "1.prems" 5 ob
              apply (auto simp:nth_append rev_nth ctxt_term[OF \<open>vs!k \<Rightarrow> v'\<close>] simp del: map_map)
              done
            ultimately show "?P ?rs' \<and> ?Q ?rs'" ..
          qed
        next
          case (7 nm'' k r' ts'')
          show ?thesis (is "\<exists>rs'. ?P rs'")
          proof
            show "?P(map dterm (ts''[k := r']))"
              using 7 ob
              apply clarsimp
              apply(rule "1.hyps"[OF _ ob(3)])
              using 7 "1.prems" ob apply auto
              done
          qed
        next
          case (9 v k r' ts'')
          then obtain vs where [simp]: "v = C\<^sub>U nm' vs" "rs' = map dterm\<^sub>M\<^sub>L (rev vs) @ map dterm ts''"
            using ob by(cases v) auto
          show ?thesis (is "\<exists>rs'. ?P rs' \<and> ?Q rs'")
          proof
            let ?rs' = "map dterm ((map term (rev vs) @ ts'')[k+size vs:=r'])"
            have "?P ?rs'" using ob 9 by (auto simp: list_update_append)
            moreover have "?Q ?rs'"
              apply rule
              apply(rule "1.hyps"[OF _ ob(3)])
              using 9 "1.prems" ob by (auto simp:nth_append simp del: map_map)
            ultimately show "?P ?rs' \<and> ?Q ?rs'" ..
          qed
        qed (insert ob, auto simp del: map_map)
      }
      hence "\<exists>rs'. dterm (ts[i := t'] ! j) = C nm' \<bullet>\<bullet> rs' \<and> (nm = nm' \<longrightarrow> no_match rs rs')"
        using \<open>i < size ts\<close> ob by(simp add:nth_list_update)
      hence "?P j" using ob by auto
      moreover have "j < ?m" using \<open>j < length ts\<close> \<open>j < size ps\<close> by simp
      ultimately show ?thesis by blast
    qed
  qed
qed

declare [[simp_depth_limit = 50]]

lemma Red_term_pres_no_match_it:
  "\<lbrakk> \<forall> i < length ts. (ts ! i, ts' ! i) : Red_term ^^ (ns!i);
    size ts' = size ts; size ns = size ts;
    no_match ps (map dterm ts)\<rbrakk>
   \<Longrightarrow> no_match ps (map dterm ts')"
proof(induct "sum_list ns" arbitrary: ts ns)
  case 0
  hence "\<forall>i < size ts. ns!i = 0" by simp
  with 0 show ?case by simp (metis nth_equalityI)
next
  case (Suc n)
  then have "sum_list ns \<noteq> 0" by arith
  then obtain k l where "k<size ts" and [simp]: "ns!k = Suc l"
    by simp (metis \<open>length ns = length ts\<close> gr0_implies_Suc in_set_conv_nth)
  let ?ns = "ns[k := l]"
  have "n = sum_list ?ns" using \<open>Suc n = sum_list ns\<close> \<open>k<size ts\<close> \<open>size ns = size ts\<close>
    by (simp add:sum_list_update)
  obtain t' where "ts!k \<Rightarrow> t'" "(t', ts'!k) : Red_term^^l"
    using Suc(3) \<open>k<size ts\<close> \<open>size ns = size ts\<close> \<open>ns!k = Suc l\<close>
    by (metis relpow_Suc_E2)
  then have 1: "\<forall>i<size(ts[k:=t']). (ts[k:=t']!i, ts'!i) : Red_term^^(?ns!i)"
    using Suc(3) \<open>k<size ts\<close> \<open>size ns = size ts\<close>
    by (auto simp add:nth_list_update)
  note nm1 = Red_term_pres_no_match[OF \<open>k<size ts\<close> \<open>ts!k \<Rightarrow> t'\<close> \<open>no_match ps (map dterm ts)\<close>]
  show ?case by(rule Suc(1)[OF \<open>n = sum_list ?ns\<close> 1 _ _ nm1])
               (simp_all add: \<open>size ts' = size ts\<close> \<open>size ns = size ts\<close>)
qed


lemma Red_term_pres_no_match_star:
assumes "\<forall>i < length(ts::tm list). ts ! i \<Rightarrow>* ts' ! i" and "size ts' = size ts"
    and "no_match ps (map dterm ts)"
shows "no_match ps (map dterm ts')"
proof-
  let ?P = "%ns. size ns = size ts \<and>
   (\<forall>i < length ts.(ts!i, ts'!i) : Red_term^^(ns!i))"
  have "\<exists>ns. ?P ns" using assms(1)
    by(subst Skolem_list_nth[symmetric])
      (simp add:rtrancl_power)
  from someI_ex[OF this] show ?thesis
    by(fast intro: Red_term_pres_no_match_it[OF _ assms(2) _ assms(3)])
qed

lemma not_pure_term[simp]: "\<not> pure(term v)"
proof
  assume "pure(term v)" thus False
    by cases
qed

abbreviation RedMLs :: "tm list \<Rightarrow> tm list \<Rightarrow> bool" (infix "[\<Rightarrow>*]" 50) where
"ss [\<Rightarrow>*] ts  \<equiv>  size ss = size ts \<and> (\<forall>i<size ss. ss!i \<Rightarrow>* ts!i)"


fun C_U_args :: "tm \<Rightarrow> tm list" ("C\<^sub>U'_args") where
"C\<^sub>U_args(s \<bullet> t) = C\<^sub>U_args s @ [t]" |
"C\<^sub>U_args(term(C\<^sub>U nm vs)) = map term (rev vs)" |
"C\<^sub>U_args _ = []"

lemma [simp]: "C\<^sub>U_args(C nm \<bullet>\<bullet> ts) = ts"
by (induct ts rule:rev_induct) auto

lemma redts_term_cong: "v \<Rightarrow>* v' \<Longrightarrow> term v \<Rightarrow>* term v'"
apply(erule converse_rtrancl_induct)
apply(rule rtrancl_refl)
apply(fast intro: converse_rtrancl_into_rtrancl dest: ctxt_term)
done

lemma C_Red_term_ML:
  "v \<Rightarrow> v' \<Longrightarrow> C_normal\<^sub>M\<^sub>L v \<Longrightarrow> dterm\<^sub>M\<^sub>L v = C nm \<bullet>\<bullet> ts
   \<Longrightarrow> dterm\<^sub>M\<^sub>L v' = C nm \<bullet>\<bullet> map dterm (C\<^sub>U_args(term v')) \<and>
      C\<^sub>U_args(term v) [\<Rightarrow>*] C\<^sub>U_args(term v') \<and>
      ts = map dterm (C\<^sub>U_args(term v))" and
  "(vs:: ml list) \<Rightarrow> vs' \<Longrightarrow> i < length vs \<Longrightarrow> vs ! i \<Rightarrow>* vs' ! i"
apply(induct arbitrary: nm ts and i rule:Red_ml_Red_ml_list.inducts)
apply(simp_all add:Red_ml_list_length del: map_map)
  apply(frule Red_ml_list_length)
  apply(simp add: redts_term_cong rev_nth del: map_map)
 apply(simp add:nth_Cons' r_into_rtrancl del: map_map)
apply(simp add:nth_Cons')
done


lemma C_normal_subterm:
  "C_normal t \<Longrightarrow> dterm t = C nm \<bullet>\<bullet> ts \<Longrightarrow> s \<in> set(C\<^sub>U_args t) \<Longrightarrow> C_normal s"
apply(induct rule: C_normal.induct)
apply auto
apply(case_tac v)
apply auto
done

lemma C_normal_subterms:
  "C_normal t \<Longrightarrow> dterm t = C nm \<bullet>\<bullet> ts \<Longrightarrow> ts = map dterm (C\<^sub>U_args t)"
apply(induct rule: C_normal.induct)
apply auto
apply(case_tac v)
apply auto
done

lemma C_redt: "t \<Rightarrow> t' \<Longrightarrow> C_normal t \<Longrightarrow> 
    C_normal t' \<and> (dterm t = C nm \<bullet>\<bullet> ts \<longrightarrow>
    (\<exists>ts'. ts' = map dterm (C\<^sub>U_args t') \<and> dterm t' = C nm \<bullet>\<bullet> ts' \<and>
     C\<^sub>U_args t [\<Rightarrow>*] C\<^sub>U_args t'))"
apply(induct arbitrary: ts nm rule:Red_term_hnf_induct)
apply (simp_all del: map_map)
   apply (metis no_match_R_coincide rev_rev_ident)
  apply clarsimp
  apply rule
   apply (metis C_normal_ML_inv)
  apply clarify
  apply(drule (2) C_Red_term_ML)
  apply clarsimp
 apply clarsimp
 apply (metis insert_iff subsetD set_update_subset_insert)
apply clarsimp
apply(rule)
 apply (metis insert_iff subsetD set_update_subset_insert)
apply rule
 apply clarify
 apply(drule bspec, assumption)
 apply simp
 apply(subst no_match.simps)
 apply(subst (asm) no_match.simps)
 apply clarsimp
 apply(rename_tac j nm nm' rs rs')
 apply(rule_tac x=j in exI)
 apply simp
 apply(case_tac "i=j")
  apply(erule_tac x=rs' in meta_allE)
  apply(erule_tac x=nm' in meta_allE)
  apply (clarsimp simp: all_set_conv_all_nth)
  apply(metis C_normal_subterms Red_term_pres_no_match_star)
 apply (auto simp:nth_list_update)
done


lemma C_redts: "t \<Rightarrow>* t' \<Longrightarrow> C_normal t \<Longrightarrow>
    C_normal t' \<and> (dterm t = C nm \<bullet>\<bullet> ts \<longrightarrow>
    (\<exists>ts'. dterm t' = C nm \<bullet>\<bullet> ts' \<and> C\<^sub>U_args t [\<Rightarrow>*] C\<^sub>U_args t' \<and>
     ts' = map dterm (C\<^sub>U_args t')))"
apply(induct arbitrary: nm ts rule:converse_rtrancl_induct)
apply simp
using tm_vector_cases[of t']
apply(elim disjE)
apply clarsimp
apply clarsimp
apply clarsimp
apply clarsimp
apply(case_tac v)
apply simp
apply simp
apply simp
apply simp
apply clarsimp
apply simp
apply simp
apply simp
apply simp
apply(frule_tac nm=nm and ts="ts" in C_redt)
apply assumption
apply clarify
apply rule
apply metis
apply clarify
apply simp
apply rule
apply (metis rtrancl_trans)
done

lemma no_match_preserved:
  "\<forall>t\<in>set ts. C_normal t \<Longrightarrow> ts [\<Rightarrow>*] ts'
   \<Longrightarrow> no_match ps os \<Longrightarrow> os = map dterm ts \<Longrightarrow> no_match ps (map dterm ts')"
proof(induct ps os arbitrary: ts ts' rule: no_match.induct)
  case (1 ps os)
  obtain i nm nm' ps' os' where a: "ps!i = C nm  \<bullet>\<bullet> ps'" "i < size ps"
      "i < size os" "os!i = C nm' \<bullet>\<bullet> os'" "nm=nm' \<longrightarrow> no_match ps' os'"
    using 1(4) no_match.simps[of ps os] by fastforce
  note 1(5)[simp]
  have "C_normal (ts ! i)" using 1(2) \<open>i < size os\<close> by auto
  have "ts!i \<Rightarrow>* ts'!i" using 1(3) \<open>i < size os\<close> by auto
  have "dterm (ts ! i) = C nm' \<bullet>\<bullet> os'" using \<open>os!i = C nm' \<bullet>\<bullet> os'\<close> \<open>i < size os\<close>
    by (simp add:nth_map)
  with C_redts [OF \<open>ts!i \<Rightarrow>* ts'!i\<close> \<open>C_normal (ts!i)\<close>]
    C_normal_subterm[OF \<open>C_normal (ts!i)\<close>]
    C_normal_subterms[OF \<open>C_normal (ts!i)\<close>]
  obtain ss' rs rs' :: "tm list" where b: "\<forall>t\<in>set rs. C_normal t"
    "dterm (ts' ! i) = C nm' \<bullet>\<bullet> ss'" "length rs = length rs'"
    "\<forall>i<length rs. rs ! i \<Rightarrow>* rs' ! i" "ss' = map dterm rs'" "os' = map dterm rs"
    by fastforce
  show ?case
    apply(subst no_match.simps)
    apply(rule_tac x=i in exI)
    using 1(2-5) a b
    apply clarsimp
    apply(rule 1(1)[of i nm' _ nm' "map dterm rs" rs])
    apply simp_all
    done
qed

lemma Lam_Red_term_itE:
  "(\<Lambda> t, t') : Red_term^^i \<Longrightarrow> \<exists>t''. t' = \<Lambda> t'' \<and> (t,t'') : Red_term^^i"
apply(induct i arbitrary: t')apply simp
apply(erule relpow_Suc_E)
apply(erule Red_term.cases)
apply (simp_all)
apply blast+
done


lemma Red_term_it: "(V x \<bullet>\<bullet> rs, r) : Red_term^^i
  \<Longrightarrow> \<exists>ts is. r = V x \<bullet>\<bullet> ts \<and> size ts = size rs & size is = size rs \<and>
       (\<forall>j<size ts. (rs!j, ts!j) : Red_term^^(is!j) \<and> is!j <= i)"
proof(induct i arbitrary:rs)
  case 0
  moreover
  have "\<exists>is. length is = length rs \<and>
   (\<forall>j<size rs. (rs!j, rs!j) \<in> Red_term ^^ is!j \<and> is!j = 0)" (is "\<exists>is. ?P is")
  proof
    show "?P(replicate (size rs) 0)" by simp
  qed
  ultimately show ?case by auto
next
  case (Suc i rs)
  from \<open>(V x \<bullet>\<bullet> rs, r) \<in> Red_term ^^ Suc i\<close>
  obtain r' where r': "V x \<bullet>\<bullet> rs \<Rightarrow> r'" and "(r',r) \<in> Red_term ^^ i"
    by (metis relpow_Suc_D2)
  from r' have "\<exists>k<size rs. \<exists>s. rs!k \<Rightarrow> s \<and> r' = V x \<bullet>\<bullet> rs[k:=s]"
  proof(induct rs arbitrary: r' rule:rev_induct)
    case Nil thus ?case by(fastforce elim: Red_term.cases)
  next
    case (snoc r rs)
    hence "(V x \<bullet>\<bullet> rs) \<bullet> r \<Rightarrow> r'" by simp
    thus ?case
    proof(cases rule:Red_term.cases)
      case (ctxt_At1 s')
      then obtain k s'' where aux: "k<length rs" "rs ! k \<Rightarrow> s''" "s' = V x \<bullet>\<bullet> rs[k := s'']"
        using snoc(1) by force
      show ?thesis (is "\<exists>k < ?n. \<exists>s. ?P k s")
      proof-
        have "k<?n \<and> ?P k s''" using ctxt_At1 aux
          by (simp add:nth_append) (metis last_snoc butlast_snoc list_update_append1)
        thus ?thesis by blast
      qed
    next
      case (ctxt_At2 t')
      show ?thesis (is "\<exists>k < ?n. \<exists>s. ?P k s")
      proof-
        have "size rs<?n \<and> ?P (size rs) t'" using ctxt_At2 by simp
        thus ?thesis by blast
      qed
    qed
  qed
  then obtain k s where "k<size rs" "rs!k \<Rightarrow> s" and [simp]: "r' = V x \<bullet>\<bullet> rs[k:=s]" by metis
  from Suc(1)[of "rs[k:=s]"] \<open>(r',r) \<in> Red_term ^^ i\<close>
  show ?case using \<open>k<size rs\<close> \<open>rs!k \<Rightarrow> s\<close>
    apply auto
    apply(rule_tac x="is[k := Suc(is!k)]" in exI)
    apply (auto simp:nth_list_update)
    apply(erule_tac x=k in allE)
    apply auto
    apply (metis relpow_Suc_I2 relpow.simps(2))
    done
qed

lemma C_Red_term_it:  "(C nm \<bullet>\<bullet> rs, r) : Red_term^^i
  \<Longrightarrow> \<exists>ts is. r = C nm \<bullet>\<bullet> ts \<and> size ts = size rs \<and> size is = size rs \<and>
        (\<forall>j<size ts. (rs!j, ts!j) \<in> Red_term^^(is!j) \<and> is!j \<le> i)"
proof(induct i arbitrary:rs)
  case 0
  moreover
  have "\<exists>is. length is = length rs \<and>
   (\<forall>j<size rs. (rs!j, rs!j) \<in> Red_term ^^ is!j \<and> is!j = 0)" (is "\<exists>is. ?P is")
  proof
    show "?P(replicate (size rs) 0)" by simp
  qed
  ultimately show ?case by auto
next
  case (Suc i rs)
  from \<open>(C nm \<bullet>\<bullet> rs, r) \<in> Red_term ^^ Suc i\<close>
  obtain r' where r': "C nm \<bullet>\<bullet> rs \<Rightarrow> r'" and "(r',r) \<in> Red_term ^^ i"
    by (metis relpow_Suc_D2)
  from r' have "\<exists>k<size rs. \<exists>s. rs!k \<Rightarrow> s \<and> r' = C nm \<bullet>\<bullet> rs[k:=s]"
  proof(induct rs arbitrary: r' rule:rev_induct)
    case Nil thus ?case by(fastforce elim: Red_term.cases)
  next
    case (snoc r rs)
    hence "(C nm \<bullet>\<bullet> rs) \<bullet> r \<Rightarrow> r'" by simp
    thus ?case
    proof(cases rule:Red_term.cases)
      case (ctxt_At1 s')
      then obtain k s'' where aux: "k<length rs" "rs ! k \<Rightarrow> s''" "s' = C nm \<bullet>\<bullet> rs[k := s'']"
        using snoc(1) by force
      show ?thesis (is "\<exists>k < ?n. \<exists>s. ?P k s")
      proof-
        have "k<?n \<and> ?P k s''" using ctxt_At1 aux
          by (simp add:nth_append) (metis last_snoc butlast_snoc list_update_append1)
        thus ?thesis by blast
      qed
    next
      case (ctxt_At2 t')
      show ?thesis (is "\<exists>k < ?n. \<exists>s. ?P k s")
      proof-
        have "size rs<?n \<and> ?P (size rs) t'" using ctxt_At2 by simp
        thus ?thesis by blast
      qed
    qed
  qed
  then obtain k s where "k<size rs" "rs!k \<Rightarrow> s" and [simp]: "r' = C nm \<bullet>\<bullet> rs[k:=s]" by metis
  from Suc(1)[of "rs[k:=s]"] \<open>(r',r) \<in> Red_term ^^ i\<close>
  show ?case using \<open>k<size rs\<close> \<open>rs!k \<Rightarrow> s\<close>
    apply auto
    apply(rule_tac x="is[k := Suc(is!k)]" in exI)
    apply (auto simp:nth_list_update)
    apply(erule_tac x=k in allE)
    apply auto
    apply (metis relpow_Suc_I2 relpow.simps(2))
    done
qed


lemma pure_At[simp]: "pure(s \<bullet> t) \<longleftrightarrow> pure s \<and> pure t"
by(fastforce elim: pure.cases)

lemma pure_foldl_At[simp]: "pure(s \<bullet>\<bullet> ts) \<longleftrightarrow> pure s \<and> (\<forall>t\<in>set ts. pure t)"
by(induct ts arbitrary: s) auto

lemma nbe_C_normal_ML:
  assumes "term v \<Rightarrow>* t'" "C_normal\<^sub>M\<^sub>L v" "pure t'" shows "normal t'"
proof -
  { fix t t' i v
    assume "(t,t') : Red_term^^i"
    hence "t = term v \<Longrightarrow> C_normal\<^sub>M\<^sub>L v \<Longrightarrow> pure t' \<Longrightarrow> normal t'"
    proof(induct i arbitrary: t t' v rule:less_induct)
    case (less k)
    show ?case
    proof (cases k)
      case 0 thus ?thesis using less by auto
    next
      case (Suc i)
      then obtain i' s where "t \<Rightarrow> s" and red: "(s,t') : Red_term^^i'" and [arith]: "i' <= i"
        by (metis eq_imp_le less(5) Suc relpow_Suc_D2)
      hence "term v \<Rightarrow> s" using Suc less by simp
      thus ?thesis
      proof cases
        case (term_C nm vs)
        with less have 0:"no_match_compR nm vs" by auto
        let ?n = "size vs"
        have 1: "(C nm \<bullet>\<bullet> map term (rev vs),t') : Red_term^^i'"
          using term_C \<open>(s,t') : Red_term^^i'\<close> by simp
        with C_Red_term_it[OF 1] 
        obtain ts ks where [simp]: "t' = C nm \<bullet>\<bullet> ts"
          and sz: "size ts = ?n \<and> size ks = ?n \<and>
          (\<forall>i<?n. (term((rev vs)!i), ts!i) : Red_term^^(ks!i) \<and> ks ! i \<le> i')"
          by(auto cong:conj_cong)
        have pure_ts: "\<forall>t\<in>set ts. pure t" using \<open>pure t'\<close> by simp
        { fix i assume "i<size vs"
          moreover hence "(term((rev vs)!i), ts!i) : Red_term^^(ks!i)" by(metis sz)
          ultimately have "normal (ts!i)"
            apply -
            apply(rule less(1))
            prefer 5 apply assumption
            using sz Suc apply fastforce
            apply(rule refl)
            using less term_C
            apply(auto)
            apply (metis in_set_conv_nth length_rev set_rev)
            apply (metis in_set_conv_nth pure_ts sz)
            done
        } note 2 = this
        have 3: "no_match_R nm (map dterm (map term (rev vs)))"
          apply(subst map_dterm_term)
          apply(rule no_match_R_coincide) using 0 by simp
        have 4: "map term (rev vs) [\<Rightarrow>*] ts"
        proof -
          have "(C nm \<bullet>\<bullet> map term (rev vs),t'): Red_term^^i'"
            using red term_C by auto
          from C_Red_term_it[OF this] obtain ts' "is" where "t' = C nm  \<bullet>\<bullet> ts'"
            and "length ts' = ?n \<and> length is =?n \<and>
              (\<forall>j< ?n. (map term (rev vs) ! j, ts' ! j) \<in> Red_term ^^ is ! j \<and> is ! j \<le> i')"
            using sz by auto
          from \<open>t' = C nm \<bullet>\<bullet> ts'\<close> \<open>t' = C nm \<bullet>\<bullet> ts\<close> have "ts = ts'" by simp
          show ?thesis using sz by (auto  simp: rtrancl_is_UN_relpow)
        qed
        have 5: "\<forall>t\<in>set(map term vs). C_normal t"
          using less term_C by auto
        have "no_match_R nm (map dterm ts)"
          apply auto
          apply(subgoal_tac "no_match aa (map dterm (map term (rev vs)))")
          prefer 2
          using 3 apply blast 
          using 4 5 no_match_preserved[OF _ _ _ refl, of "map term (rev vs)" "ts"] by simp
        hence 6: "no_match_R nm ts" by(metis map_dterm_pure[OF pure_ts])
        then show "normal t'"
          apply(simp)
          apply(rule normal.intros(3))
          using 2 sz apply(fastforce simp:set_conv_nth)
          apply auto
          apply(subgoal_tac "no_match aa (take (size aa) ts)")
          apply (metis no_match)
          apply(fastforce intro:no_match_take)
          done
      next
        case (term_V x vs)
        let ?n = "size vs"
        have 1: "(V x \<bullet>\<bullet> map term (rev vs),t') : Red_term^^i'"
          using term_V \<open>(s,t') : Red_term^^i'\<close> by simp
        with Red_term_it[OF 1] obtain ts "is" where [simp]: "t' = V x \<bullet>\<bullet> ts"
          and 2: "length ts = ?n \<and>
            length is = ?n \<and> (\<forall>j<?n. (term (rev vs ! j), ts ! j) \<in> Red_term ^^ is ! j \<and>
            is ! j \<le> i')"
          by (auto cong:conj_cong)
        have "\<forall>j<?n. normal(ts!j)"
        proof(clarify)
          fix j assume 0: "j < ?n"
          then have "is!j < k" using \<open>k=Suc i\<close> 2 by auto
          have red: "(term (rev vs ! j), ts ! j) \<in> Red_term ^^ is ! j" using \<open>j < ?n\<close> 2 by auto
          have pure: "pure (ts ! j)" using \<open>pure t'\<close> 0 2 by auto
          have Cnm: "C_normal\<^sub>M\<^sub>L (rev vs ! j)" using less term_V
            by simp (metis 0 in_set_conv_nth length_rev set_rev)
          from less(1)[OF \<open>is!j < k\<close> refl Cnm pure red] show "normal(ts!j)" .
        qed
        note 3=this
        show ?thesis by simp (metis normal.intros(1) in_set_conv_nth 2 3)
      next
        case (term_Clo f vs n)
        let ?u = "apply (lift 0 (Clo f vs n)) (V\<^sub>U 0 [])"
        from term_Clo \<open>(s,t') : Red_term^^i'\<close>
        obtain t'' where [simp]: "t' = \<Lambda> t''" and 1: "(term ?u, t'') : Red_term^^i'"
          by(metis Lam_Red_term_itE)
        have "i' < k" using \<open>k = Suc i\<close> by arith
        have "pure t''" using \<open>pure t'\<close> by simp
        have "C_normal\<^sub>M\<^sub>L ?u" using less term_Clo by(simp)
        from less(1)[OF \<open>i' < k\<close> refl \<open>C_normal\<^sub>M\<^sub>L ?u\<close> \<open>pure t''\<close> 1]
        show ?thesis by(simp add:normal.intros)
      next
        case (ctxt_term u')
        have "i' < k" using \<open>k = Suc i\<close> by arith
        have "C_normal\<^sub>M\<^sub>L u'" by (rule C_normal_ML_inv) (insert less ctxt_term, simp_all)
        have "(term u', t') \<in> Red_term ^^ i'" using red ctxt_term by auto
        from less(1)[OF \<open>i' < k\<close> refl \<open>C_normal\<^sub>M\<^sub>L u'\<close> \<open>pure t'\<close> this] show ?thesis .
      qed
    qed
  qed
  }
  thus ?thesis using assms(2-) rtrancl_imp_relpow[OF assms(1)] by blast
qed

lemma C_normal_ML_compile:
  "pure t \<Longrightarrow> \<forall>i. C_normal\<^sub>M\<^sub>L(\<sigma> i) \<Longrightarrow> C_normal\<^sub>M\<^sub>L (compile t \<sigma>)"
by(induct t arbitrary: \<sigma>) (simp_all add: C_normal_ML_lift_ML)

corollary nbe_normal:
  "pure t \<Longrightarrow> term(comp_fixed t) \<Rightarrow>* t' \<Longrightarrow> pure t' \<Longrightarrow> normal t'"
apply(erule nbe_C_normal_ML)
apply(simp add: C_normal_ML_compile)
apply assumption
done

section\<open>Refinements\<close>

text\<open>We ensure that all occurrences of @{term "C\<^sub>U nm vs"} satisfy
the invariant @{prop"size vs = arity nm"}.\<close>

text\<open>A constructor value:\<close>

fun C\<^sub>Us :: "ml \<Rightarrow> bool" where
"C\<^sub>Us(C\<^sub>U nm vs) = (size vs = arity nm \<and> (\<forall>v\<in>set vs. C\<^sub>Us v))" |
"C\<^sub>Us _ = False"

lemma size_foldl_At: "size(C nm \<bullet>\<bullet> ts) = size ts + sum_list(map size ts)"
by(induct ts rule:rev_induct) auto


lemma termination_linpats:
  "i < length ts \<Longrightarrow> ts!i = C nm \<bullet>\<bullet> ts'
   \<Longrightarrow> length ts' + sum_list (map size ts') < length ts + sum_list (map size ts)"
apply(subgoal_tac "C nm \<bullet>\<bullet> ts' : set ts")
 prefer 2 apply (metis in_set_conv_nth)
apply(drule sum_list_map_remove1[of _ _ size])
apply(simp add:size_foldl_At)
apply (metis gr_implies_not0 length_0_conv)
done

text\<open>Linear patterns:\<close>

function linpats :: "tm list \<Rightarrow> bool" where
"linpats ts \<longleftrightarrow>
 (\<forall>i<size ts. (\<exists>x. ts!i = V x) \<or>
    (\<exists>nm ts'. ts!i = C nm \<bullet>\<bullet> ts' \<and> arity nm = size ts' \<and> linpats ts')) \<and>
 (\<forall>i<size ts. \<forall>j<size ts. i\<noteq>j \<longrightarrow> fv(ts!i) \<inter> fv(ts!j) = {})"
by pat_completeness auto
termination
apply(relation "measure(%ts. size ts + (SUM t<-ts. size t))")
apply (auto simp:termination_linpats)
done

declare linpats.simps[simp del]

(* FIXME move *)
lemma eq_lists_iff_eq_nth:
  "size xs = size ys \<Longrightarrow> (xs=ys) = (\<forall>i<size xs. xs!i = ys!i)"
by (metis nth_equalityI)

lemma pattern_subst_ML_coincidence:
 "pattern t \<Longrightarrow> \<forall>i\<in>fv t. \<sigma> i = \<sigma>' i
  \<Longrightarrow> subst_ML \<sigma> (comp_pat t) = subst_ML \<sigma>' (comp_pat t)"
by(induct pred:pattern) auto

lemma linpats_pattern: "linpats ts \<Longrightarrow> patterns ts"
proof(induct ts rule:linpats.induct)
  case (1 ts)
  show ?case
  proof
    fix t assume "t : set ts"
    then obtain i where "i < size ts" and [simp]: "t = ts!i"
      by (auto simp: in_set_conv_nth)
    hence "(\<exists>x. t = V x) \<or> (\<exists>nm ts'. t = C nm \<bullet>\<bullet> ts' \<and> arity nm = size ts' & linpats ts')"
      (is "?V | ?C")
      using 1(2) by(simp add:linpats.simps[of ts])
    thus "pattern t"
    proof
      assume "?V" thus ?thesis by(auto simp:pat_V)
    next
      assume "?C" thus ?thesis using 1(1) \<open>i < size ts\<close>
        by auto (metis pat_C)
    qed
  qed
qed

lemma no_match_ML_swap_rev:
  "length ps = length vs \<Longrightarrow> no_match\<^sub>M\<^sub>L ps (rev vs) \<Longrightarrow> no_match\<^sub>M\<^sub>L (rev ps) vs"
apply(clarsimp simp: no_match_ML.simps[of ps] no_match_ML.simps[of _ vs])
apply(rule_tac x="size ps - i - 1" in exI)
apply (fastforce simp:rev_nth)
done

lemma no_match_ML_aux:
  "\<forall>v \<in> set cvs. C\<^sub>Us v \<Longrightarrow> linpats ps \<Longrightarrow> size ps = size cvs \<Longrightarrow>
  \<forall>\<sigma>. map (subst\<^sub>M\<^sub>L \<sigma>) (map comp_pat ps) \<noteq> cvs \<Longrightarrow>
  no_match\<^sub>M\<^sub>L (map comp_pat ps) cvs"
apply(induct ps arbitrary: cvs rule:linpats.induct)
apply(frule linpats_pattern)
apply(subst (asm) linpats.simps) back
apply auto
apply(case_tac "\<forall>i<size ts. \<exists>\<sigma>. subst\<^sub>M\<^sub>L \<sigma> (comp_pat (ts!i)) = cvs!i")
 apply(clarsimp simp:Skolem_list_nth)
 apply(rename_tac "\<sigma>s")
 apply(erule_tac x="%x. (\<sigma>s!(THE i. i<size ts & x : fv(ts!i)))x" in allE)
 apply(clarsimp simp:eq_lists_iff_eq_nth)
 apply(rotate_tac -3)
 apply(erule_tac x=i in allE)
 apply simp
 apply(rotate_tac -1)
 apply(drule sym)
 apply simp
 apply(erule contrapos_np)
 apply(rule pattern_subst_ML_coincidence)
  apply (metis in_set_conv_nth)
 apply clarsimp
 apply(rule_tac a=i in theI2)
   apply simp
  apply (metis disjoint_iff_not_equal)
 apply (metis disjoint_iff_not_equal)
apply clarsimp
apply(subst no_match_ML.simps)
apply(rule_tac x="size ts - i - 1" in exI)
apply simp
apply rule
 apply simp
apply(subgoal_tac "\<not>(\<exists>x. ts!i = V x)")
 prefer 2
 apply fastforce
apply(subgoal_tac "\<exists>nm ts'. ts!i = C nm \<bullet>\<bullet> ts' & size ts' = arity nm & linpats ts'")
 prefer 2
 apply fastforce
apply clarsimp
apply(rule_tac x=nm in exI)
apply(subgoal_tac "\<exists>nm' vs'. cvs!i = C\<^sub>U nm' vs' & size vs' = arity nm' & (\<forall>v' \<in> set vs'. C\<^sub>Us v')")
 prefer 2
 apply(drule_tac x="cvs!i" in bspec)
  apply simp
   apply(case_tac "cvs!i")
apply simp_all
apply (clarsimp simp:rev_nth rev_map[symmetric])
apply(erule_tac x=i in meta_allE)
apply(erule_tac x=nm' in meta_allE)
apply(erule_tac x="ts'" in meta_allE)
apply(erule_tac x="rev vs'" in meta_allE)
apply simp
apply(subgoal_tac "no_match\<^sub>M\<^sub>L (map comp_pat ts') (rev vs')")
 apply(rule no_match_ML_swap_rev)
  apply simp
 apply assumption
apply(erule_tac meta_mp)
apply (metis rev_rev_ident)
done



(*<*)
end
(*>*)
