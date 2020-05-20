section\<open>The Axiom of Extensionality in $M[G]$\<close>
theory Extensionality_Axiom
imports
  Names
begin

context forcing_data
begin
  
lemma extensionality_in_MG : "extensionality(##(M[G]))"
proof -
  {
    fix x y z
    assume 
      asms: "x\<in>M[G]" "y\<in>M[G]" "(\<forall>w\<in>M[G] . w \<in> x \<longleftrightarrow> w \<in> y)"
    from \<open>x\<in>M[G]\<close> have
      "z\<in>x \<longleftrightarrow> z\<in>M[G] \<and> z\<in>x"
      using transitivity_MG by auto
    also have
      "... \<longleftrightarrow> z\<in>y"
      using asms transitivity_MG by auto
    finally have
      "z\<in>x \<longleftrightarrow> z\<in>y" .
  }
  then have
    "\<forall>x\<in>M[G] . \<forall>y\<in>M[G] . (\<forall>z\<in>M[G] . z \<in> x \<longleftrightarrow> z \<in> y) \<longrightarrow> x = y"
    by blast
  then show ?thesis unfolding extensionality_def by simp
qed
 
end  (* context forcing_data *)
end