(*<*)
theory TAO_6_Identifiable
imports TAO_5_MetaSolver
begin
(*>*)

section\<open>General Identity\<close>
text\<open>\label{TAO_Identifiable}\<close>

text\<open>
\begin{remark}
  In order to define a general identity symbol that can act
  on all types of terms a type class is introduced
  which assumes the substitution property which
  is needed to derive the corresponding axiom.
  This type class is instantiated for all relation types, individual terms
  and individuals.
\end{remark}
\<close>

subsection\<open>Type Classes\<close>
text\<open>\label{TAO_Identifiable_Class}\<close>

class identifiable =
fixes identity :: "'a\<Rightarrow>'a\<Rightarrow>\<o>" (infixl "\<^bold>=" 63)
assumes l_identity:
  "w \<Turnstile> x \<^bold>= y \<Longrightarrow> w \<Turnstile> \<phi> x \<Longrightarrow> w \<Turnstile> \<phi> y"
begin
  abbreviation notequal (infixl "\<^bold>\<noteq>" 63) where
    "notequal \<equiv> \<lambda> x y . \<^bold>\<not>(x \<^bold>= y)"
end

class quantifiable_and_identifiable = quantifiable + identifiable
begin
  definition exists_unique::"('a\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<exists>!" [8] 9) where
    "exists_unique \<equiv> \<lambda> \<phi> . \<^bold>\<exists> \<alpha> . \<phi> \<alpha> \<^bold>& (\<^bold>\<forall>\<beta>. \<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>)"
  
  declare exists_unique_def[conn_defs]
end

subsection\<open>Instantiations\<close>
text\<open>\label{TAO_Identifiable_Instantiation}\<close>

instantiation \<kappa> :: identifiable
begin
  definition identity_\<kappa> where "identity_\<kappa> \<equiv> basic_identity\<^sub>\<kappa>"
  instance proof
    fix x y :: \<kappa> and w \<phi>
    show "[x \<^bold>= y in w] \<Longrightarrow> [\<phi> x in w] \<Longrightarrow> [\<phi> y in w]"
      unfolding identity_\<kappa>_def
      using MetaSolver.Eq\<kappa>_prop ..
  qed
end

instantiation \<nu> :: identifiable
begin
  definition identity_\<nu> where "identity_\<nu> \<equiv> \<lambda> x y . x\<^sup>P \<^bold>= y\<^sup>P"
  instance proof
    fix \<alpha> :: \<nu> and \<beta> :: \<nu> and v \<phi>
    assume "v \<Turnstile> \<alpha> \<^bold>= \<beta>"
    hence "v \<Turnstile> \<alpha>\<^sup>P \<^bold>= \<beta>\<^sup>P"
      unfolding identity_\<nu>_def by auto
    hence "\<And>\<phi>.(v \<Turnstile> \<phi> (\<alpha>\<^sup>P)) \<Longrightarrow> (v \<Turnstile> \<phi> (\<beta>\<^sup>P))"
      using l_identity by auto
    hence "(v \<Turnstile> \<phi> (rep (\<alpha>\<^sup>P))) \<Longrightarrow> (v \<Turnstile> \<phi> (rep (\<beta>\<^sup>P)))"
      by meson
    thus "(v \<Turnstile> \<phi> \<alpha>) \<Longrightarrow> (v \<Turnstile> \<phi> \<beta>)"
      by (simp only: rep_proper_id)
  qed
end

instantiation \<Pi>\<^sub>1 :: identifiable
begin
  definition identity_\<Pi>\<^sub>1 where "identity_\<Pi>\<^sub>1 \<equiv> basic_identity\<^sub>1"
  instance proof
    fix F G :: \<Pi>\<^sub>1 and w \<phi>
    show "(w \<Turnstile> F \<^bold>= G) \<Longrightarrow> (w \<Turnstile> \<phi> F) \<Longrightarrow> (w \<Turnstile> \<phi> G)"
      unfolding identity_\<Pi>\<^sub>1_def using MetaSolver.Eq\<^sub>1_prop ..
  qed
end

instantiation \<Pi>\<^sub>2 :: identifiable
begin
  definition identity_\<Pi>\<^sub>2 where "identity_\<Pi>\<^sub>2 \<equiv> basic_identity\<^sub>2"
  instance proof
    fix F G :: \<Pi>\<^sub>2 and w \<phi>
    show "(w \<Turnstile> F \<^bold>= G) \<Longrightarrow> (w \<Turnstile> \<phi> F) \<Longrightarrow> (w \<Turnstile> \<phi> G)"
      unfolding identity_\<Pi>\<^sub>2_def using MetaSolver.Eq\<^sub>2_prop ..
  qed
end

instantiation \<Pi>\<^sub>3 :: identifiable
begin
  definition identity_\<Pi>\<^sub>3 where "identity_\<Pi>\<^sub>3 \<equiv> basic_identity\<^sub>3"
  instance proof
    fix F G :: \<Pi>\<^sub>3 and w \<phi>
    show "(w \<Turnstile> F \<^bold>= G) \<Longrightarrow> (w \<Turnstile> \<phi> F) \<Longrightarrow> (w \<Turnstile> \<phi> G)"
      unfolding identity_\<Pi>\<^sub>3_def using MetaSolver.Eq\<^sub>3_prop ..
  qed
end

instantiation \<o> :: identifiable
begin
  definition identity_\<o> where "identity_\<o> \<equiv> basic_identity\<^sub>0"
  instance proof
    fix F G :: \<o> and w \<phi>
    show "(w \<Turnstile> F \<^bold>= G) \<Longrightarrow> (w \<Turnstile> \<phi> F) \<Longrightarrow> (w \<Turnstile> \<phi> G)"
      unfolding identity_\<o>_def using MetaSolver.Eq\<^sub>0_prop ..
  qed
end

instance \<nu> :: quantifiable_and_identifiable ..
instance \<Pi>\<^sub>1 :: quantifiable_and_identifiable ..
instance \<Pi>\<^sub>2 :: quantifiable_and_identifiable ..
instance \<Pi>\<^sub>3 :: quantifiable_and_identifiable ..
instance \<o> :: quantifiable_and_identifiable ..

subsection\<open>New Identity Definitions\<close>
text\<open>\label{TAO_Identifiable_Definitions}\<close>

text\<open>
\begin{remark}
  The basic definitions of identity use type specific quantifiers
  and identity symbols. Equivalent definitions that
  use the general identity symbol and general quantifiers are provided.
\end{remark}
\<close>

named_theorems identity_defs
lemma identity\<^sub>E_def[identity_defs]:
  "basic_identity\<^sub>E \<equiv> \<^bold>\<lambda>\<^sup>2 (\<lambda>x y. \<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<lparr>O!,y\<^sup>P\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>))"
  unfolding basic_identity\<^sub>E_def forall_\<Pi>\<^sub>1_def by simp
lemma identity\<^sub>E_infix_def[identity_defs]:
  "x \<^bold>=\<^sub>E y \<equiv> \<lparr>basic_identity\<^sub>E,x,y\<rparr>" using basic_identity\<^sub>E_infix_def .
lemma identity\<^sub>\<kappa>_def[identity_defs]:
  "(\<^bold>=) \<equiv> \<lambda>x y. x \<^bold>=\<^sub>E y \<^bold>\<or> \<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F. \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>)"
  unfolding identity_\<kappa>_def basic_identity\<^sub>\<kappa>_def forall_\<Pi>\<^sub>1_def by simp
lemma identity\<^sub>\<nu>_def[identity_defs]:
  "(\<^bold>=) \<equiv> \<lambda>x y. (x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P) \<^bold>\<or> \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P,F\<rbrace>)"
  unfolding identity_\<nu>_def identity\<^sub>\<kappa>_def by simp
lemma identity\<^sub>1_def[identity_defs]:
  "(\<^bold>=) \<equiv> \<lambda>F G. \<^bold>\<box>(\<^bold>\<forall> x . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>P,G\<rbrace>)"
  unfolding identity_\<Pi>\<^sub>1_def basic_identity\<^sub>1_def forall_\<nu>_def by simp
lemma identity\<^sub>2_def[identity_defs]:
  "(\<^bold>=) \<equiv> \<lambda>F G. \<^bold>\<forall> x. (\<^bold>\<lambda>y. \<lparr>F,x\<^sup>P,y\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>y. \<lparr>G,x\<^sup>P,y\<^sup>P\<rparr>)
                    \<^bold>& (\<^bold>\<lambda>y. \<lparr>F,y\<^sup>P,x\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>y. \<lparr>G,y\<^sup>P,x\<^sup>P\<rparr>)"
  unfolding identity_\<Pi>\<^sub>2_def identity_\<Pi>\<^sub>1_def basic_identity\<^sub>2_def forall_\<nu>_def by simp
lemma identity\<^sub>3_def[identity_defs]:
  "(\<^bold>=) \<equiv> \<lambda>F G. \<^bold>\<forall> x y. (\<^bold>\<lambda>z. \<lparr>F,z\<^sup>P,x\<^sup>P,y\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>G,z\<^sup>P,x\<^sup>P,y\<^sup>P\<rparr>)
                      \<^bold>& (\<^bold>\<lambda>z. \<lparr>F,x\<^sup>P,z\<^sup>P,y\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>G,x\<^sup>P,z\<^sup>P,y\<^sup>P\<rparr>)
                      \<^bold>& (\<^bold>\<lambda>z. \<lparr>F,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>G,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>)"
  unfolding identity_\<Pi>\<^sub>3_def identity_\<Pi>\<^sub>1_def basic_identity\<^sub>3_def forall_\<nu>_def by simp
lemma identity\<^sub>\<o>_def[identity_defs]: "(\<^bold>=) \<equiv> \<lambda>F G. (\<^bold>\<lambda>y. F) \<^bold>= (\<^bold>\<lambda>y. G)"
  unfolding identity_\<o>_def identity_\<Pi>\<^sub>1_def basic_identity\<^sub>0_def by simp

(*<*)
end
(*>*)
