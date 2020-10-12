(*  Title:      Containers/Collection_Eq.thy
    Author:     Andreas Lochbihler, KIT
                René Thiemann, UIBK *)
theory Collection_Eq imports
  Containers_Auxiliary
  Containers_Generator
  Deriving.Equality_Instances
begin

section \<open>A type class for optional equality testing\<close>

class ceq =
  fixes ceq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) option"
  assumes ceq: "ceq = Some eq \<Longrightarrow> eq = (=)"
begin

lemma ceq_equality: "ceq = Some eq \<Longrightarrow> equality eq"
  by (drule ceq, rule Equality_Generator.equalityI, simp)

lemma ID_ceq: "ID ceq = Some eq \<Longrightarrow> eq = (=)"
unfolding ID_def id_apply by(rule ceq)

abbreviation ceq' :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where "ceq' \<equiv> the (ID ceq)"

end

syntax "_CEQ" :: "type => logic"  ("(1CEQ/(1'(_')))")

parse_translation \<open>
let
  fun ceq_tr [ty] =
     (Syntax.const @{syntax_const "_constrain"} $ Syntax.const @{const_syntax "ceq"} $
       (Syntax.const @{type_syntax option} $ 
         (Syntax.const @{type_syntax fun} $ ty $ 
           (Syntax.const @{type_syntax fun} $ ty $ Syntax.const @{type_syntax bool}))))
    | ceq_tr ts = raise TERM ("ceq_tr", ts);
in [(@{syntax_const "_CEQ"}, K ceq_tr)] end
\<close>

typed_print_translation \<open>
let
  fun ceq_tr' ctxt
    (Type (@{type_name option}, [Type (@{type_name fun}, [T, _])])) ts =
    Term.list_comb (Syntax.const @{syntax_const "_CEQ"} $ Syntax_Phases.term_of_typ ctxt T, ts)
  | ceq_tr' _ _ _ = raise Match;
in [(@{const_syntax ceq}, ceq_tr')]
end
\<close>

definition is_ceq :: "'a :: ceq itself \<Rightarrow> bool"
where "is_ceq _ \<longleftrightarrow> ID CEQ('a) \<noteq> None"

subsection \<open>Generator for the @{class ceq}-class\<close>

text \<open>
This generator registers itself at the derive-manager for the class @{class ceq}.
To be more precise, one can choose whether one wants to take @{term "(=)"} as function
for @{term ceq} by passing "eq" as parameter, 
whether equality should not be supported by passing "no" as parameter,
or whether an own definition for equality should be derived by not passing
any parameters. The last possibility only works for datatypes.

\begin{itemize}
\item \texttt{instantiation type :: (type,\ldots,type) (eq) ceq}
\item \texttt{instantiation type :: (type,\ldots,type) (no) ceq}
\item \texttt{instantiation datatype :: (ceq,\ldots,ceq) ceq}
\end{itemize}

If the parameter "no" is not used, then the corresponding
@{term is_ceq}-theorem is also automatically generated and attributed with 
\texttt{[simp, code-post]}.
\<close>


text \<open>
This generator can be used for arbitrary types, not just datatypes. 
\<close>

lemma equality_subst: "c1 = c2 \<Longrightarrow> equality c1 \<Longrightarrow> equality c2" by blast

ML_file \<open>ceq_generator.ML\<close>

subsection \<open>Type class instances for HOL types\<close>

derive (eq) ceq unit
lemma [code]: "CEQ(unit) = Some (\<lambda>_ _. True)"
  unfolding ceq_unit_def by (simp, intro ext, auto)
derive (eq) ceq
  bool
  nat
  int
  Enum.finite_1
  Enum.finite_2
  Enum.finite_3
  Enum.finite_4
  Enum.finite_5
  integer
  natural
  char
  String.literal
derive ceq sum prod list option
derive (no) ceq "fun"

lemma is_ceq_fun [simp]: "\<not> is_ceq TYPE('a \<Rightarrow> 'b)"
  by(simp add: is_ceq_def ceq_fun_def ID_None) 

definition set_eq :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" 
where [code del]: "set_eq = (=)"

lemma set_eq_code:
  shows [code]: "set_eq A B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A"
  and [code_unfold]: "(=) = set_eq"
unfolding set_eq_def by blast+

instantiation set :: (ceq) ceq begin
definition "CEQ('a set) = (case ID CEQ('a) of None \<Rightarrow> None | Some _ \<Rightarrow> Some set_eq)"
instance by(intro_classes)(simp add: ceq_set_def set_eq_def split: option.splits)
end

lemma is_ceq_set [simp, code_post]: "is_ceq TYPE('a set) \<longleftrightarrow> is_ceq TYPE('a :: ceq)"
by(simp add: is_ceq_def ceq_set_def ID_None ID_Some split: option.split)

lemma ID_ceq_set_not_None_iff [simp]: "ID CEQ('a set) \<noteq> None \<longleftrightarrow> ID CEQ('a :: ceq) \<noteq> None"
by(simp add: ceq_set_def ID_def split: option.splits)

text \<open>Instantiation for @{typ "'a Predicate.pred"}\<close>

context fixes eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" begin

definition member_pred :: "'a Predicate.pred \<Rightarrow> 'a \<Rightarrow> bool"
where "member_pred P x \<longleftrightarrow> (\<exists>y. eq x y \<and> Predicate.eval P y)"

definition member_seq :: "'a Predicate.seq \<Rightarrow> 'a \<Rightarrow> bool"
where "member_seq xp = member_pred (Predicate.pred_of_seq xp)"

lemma member_seq_code [code]: 
  "member_seq seq.Empty x \<longleftrightarrow> False"
  "member_seq (seq.Insert y P) x \<longleftrightarrow> eq x y \<or> member_pred P x"
  "member_seq (seq.Join Q xq) x \<longleftrightarrow> member_pred Q x \<or> member_seq xq x"
by(auto simp add: member_seq_def member_pred_def)

lemma member_pred_code [code]:
  "member_pred (Predicate.Seq f) = member_seq (f ())"
by(simp add: member_seq_def Seq_def)

definition leq_pred :: "'a Predicate.pred \<Rightarrow> 'a Predicate.pred \<Rightarrow> bool"
where "leq_pred P Q \<longleftrightarrow> (\<forall>x. Predicate.eval P x \<longrightarrow> (\<exists>y. eq x y \<and> Predicate.eval Q y))"

definition leq_seq :: "'a Predicate.seq \<Rightarrow> 'a Predicate.pred \<Rightarrow> bool"
where "leq_seq xp Q \<longleftrightarrow> leq_pred (Predicate.pred_of_seq xp) Q"

lemma leq_seq_code [code]:
  "leq_seq seq.Empty Q \<longleftrightarrow> True"
  "leq_seq (seq.Insert x P) Q \<longleftrightarrow> member_pred Q x \<and> leq_pred P Q"
  "leq_seq (seq.Join P xp) Q \<longleftrightarrow> leq_pred P Q \<and> leq_seq xp Q"
by(auto simp add: leq_seq_def leq_pred_def member_pred_def)

lemma leq_pred_code [code]:
  "leq_pred (Predicate.Seq f) Q \<longleftrightarrow> leq_seq (f ()) Q"
by(simp add: leq_seq_def Seq_def)

definition predicate_eq :: "'a Predicate.pred \<Rightarrow> 'a Predicate.pred \<Rightarrow> bool"
where "predicate_eq P Q \<longleftrightarrow> leq_pred P Q \<and> leq_pred Q P"

context assumes eq: "eq = (=)" begin

lemma member_pred_eq: "member_pred = Predicate.eval"
unfolding fun_eq_iff member_pred_def by(simp add: eq)

lemma member_seq_eq: "member_seq = Predicate.member"
by(simp add: member_seq_def fun_eq_iff eval_member member_pred_eq)

lemma leq_pred_eq: "leq_pred = (\<le>)"
unfolding fun_eq_iff leq_pred_def by(auto simp add: eq less_eq_pred_def)

lemma predicate_eq_eq: "predicate_eq = (=)"
unfolding predicate_eq_def fun_eq_iff by(auto simp add: leq_pred_eq)

end
end

instantiation Predicate.pred :: (ceq) ceq begin
definition "CEQ('a Predicate.pred) = map_option predicate_eq (ID CEQ('a))"
instance by(intro_classes)(auto simp add: ceq_pred_def predicate_eq_eq dest: ID_ceq)
end

end
