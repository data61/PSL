section\<open>The Axiom of Foundation in $M[G]$\<close>
theory Foundation_Axiom
imports
  Names
begin

context forcing_data
begin
  
(* Slick proof essentially by Paulson (adapted from L) *)  
lemma foundation_in_MG : "foundation_ax(##(M[G]))"
  unfolding foundation_ax_def
  by (rule rallI, cut_tac A=x in foundation, auto intro: transitivity_MG)

(* Same theorem as above, declarative proof, 
   without using transitivity *)
lemma "foundation_ax(##(M[G]))"
proof -
  {   
    fix x 
    assume "x\<in>M[G]" "\<exists>y\<in>M[G] . y\<in>x"
    then 
    have "\<exists>y\<in>M[G] . y\<in>x\<inter>M[G]" by simp
    then 
    obtain y where "y\<in>x\<inter>M[G]" "\<forall>z\<in>y. z \<notin> x\<inter>M[G]" 
      using foundation[of "x\<inter>M[G]"]  by blast
    then 
    have "\<exists>y\<in>M[G] . y \<in> x \<and> (\<forall>z\<in>M[G] . z \<notin> x \<or> z \<notin> y)"by auto
  }
  then show ?thesis
    unfolding foundation_ax_def by auto
qed
    
end  (* context forcing_data *)
end