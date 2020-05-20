(*<*)
theory TAO_3_Quantifiable
imports TAO_2_Semantics
begin
(*>*)

section\<open>General Quantification\<close>
text\<open>\label{TAO_Quantifiable}\<close>

text\<open>
\begin{remark}
  In order to define general quantifiers that can act
  on individuals as well as relations a type class
  is introduced which assumes the semantics of the all quantifier.
  This type class is then instantiated for individuals and
  relations.
\end{remark}
\<close>

subsection\<open>Type Class\<close>
text\<open>\label{TAO_Quantifiable_Class}\<close>

class quantifiable = fixes forall :: "('a\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>" [8] 9)
  assumes quantifiable_T8: "(w \<Turnstile> (\<^bold>\<forall> x . \<psi> x)) = (\<forall> x . (w \<Turnstile> (\<psi> x)))"
begin
end

lemma (in Semantics) T8: shows "(w \<Turnstile> \<^bold>\<forall> x . \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
  using quantifiable_T8 .

subsection\<open>Instantiations\<close>
text\<open>\label{TAO_Quantifiable_Instantiations}\<close>

instantiation \<nu> :: quantifiable
begin
  definition forall_\<nu> :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<nu> \<equiv> forall\<^sub>\<nu>"
  instance proof
    fix w :: i and \<psi> :: "\<nu>\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<nu>_def using Semantics.T8_\<nu> .
  qed
end

instantiation \<o> :: quantifiable
begin
  definition forall_\<o> :: "(\<o>\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<o> \<equiv> forall\<^sub>\<o>"
  instance proof
    fix w :: i and \<psi> :: "\<o>\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<o>_def using Semantics.T8_\<o> .
  qed
end

instantiation \<Pi>\<^sub>1 :: quantifiable
begin
  definition forall_\<Pi>\<^sub>1 :: "(\<Pi>\<^sub>1\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<Pi>\<^sub>1 \<equiv> forall\<^sub>1"
  instance proof
    fix w :: i and \<psi> :: "\<Pi>\<^sub>1\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<Pi>\<^sub>1_def using Semantics.T8_1 .
  qed
end

instantiation \<Pi>\<^sub>2 :: quantifiable
begin
  definition forall_\<Pi>\<^sub>2 :: "(\<Pi>\<^sub>2\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<Pi>\<^sub>2 \<equiv> forall\<^sub>2"
  instance proof
    fix w :: i and \<psi> :: "\<Pi>\<^sub>2\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<Pi>\<^sub>2_def using Semantics.T8_2 .
  qed
end

instantiation \<Pi>\<^sub>3 :: quantifiable
begin
  definition forall_\<Pi>\<^sub>3 :: "(\<Pi>\<^sub>3\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<Pi>\<^sub>3 \<equiv> forall\<^sub>3"
  instance proof
    fix w :: i and \<psi> :: "\<Pi>\<^sub>3\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<Pi>\<^sub>3_def using Semantics.T8_3 .
  qed
end

(*<*)
end
(*>*)
