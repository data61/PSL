theory Nielson_VCGi_complete
imports Nielson_VCG Nielson_VCGi
begin
  
subsubsection "Completeness"
  
text \<open>As the improved VCG for the Nielson logic is only more liberal in the sense that
      the S annotation is only checked for "interesting" variables, if we specify the
      set of interesting variables to be all variables we basically get the same
      verification conditions as for the normal VCG.
      In that sense, we can prove the completeness of the improved VCG with the completeness
      theorem of the normal VCG. 

      For that, we formulate some translation functions and in the end show completeness of the
      improved VCG:\<close>
  
fun transl :: "Nielson_VCG.acom \<Rightarrow> Nielson_VCGi.acom" where
  "transl SKIP = SKIP" |
  "transl (x ::= a) = (x ::= a)" |
  "transl (C\<^sub>1;; C\<^sub>2) = (transl C\<^sub>1;; transl C\<^sub>2)" |
  "transl (IF b THEN C\<^sub>1 ELSE C\<^sub>2) = (IF b THEN transl C\<^sub>1 ELSE transl C\<^sub>2)" |
  "transl ({A/B/D} CONSEQ C) = ({(A,UNIV)/(B,UNIV)/(D,UNIV)} CONSEQ transl C)" |
  "transl ({(I,S,E)} WHILE b DO C) = ({((I,UNIV),S,E,UNIV,(\<lambda>v. UNIV))} WHILE b DO transl C)"

lemma qdeps_UNIV: "qdeps (transl C) UNIV = UNIV"
  apply(induct C) apply auto done

lemma fune_UNIV: "fune (transl C) UNIV = UNIV"
  apply(induct C) apply auto done 

lemma pre_transl: "Nielson_VCGi.pre (transl C) Q = Nielson_VCG.pre C Q"
  apply(induct C arbitrary: Q) by (auto)

lemma preT_transl: "Nielson_VCGi.preT (transl C) E = Nielson_VCG.preT C E"
  apply(induct C arbitrary: E) by (auto)

lemma postQ_transl: "Nielson_VCGi.postQ (transl C) = Nielson_VCG.postQ C"
  apply(induct C) by (auto)

lemma time_transl: "Nielson_VCGi.time (transl C)  = Nielson_VCG.time C"
  apply(induct C ) by(auto simp: preT_transl)


lemma vc_transl: "Nielson_VCG.vc C Q \<Longrightarrow> Nielson_VCGi.vc (transl C) Q UNIV UNIV"
proof (induct C arbitrary: Q) 
next
  case (Aconseq x1 x2 x3 C)
  then show ?case apply (auto simp: pre_transl time_transl) apply presburger+ done
next
  case (Awhile A b C)
  obtain I S E where "A=(I,S,E)" using prod_cases3 by blast
  with Awhile show ?case apply (auto simp: pre_transl preT_transl time_transl postQ_transl) apply presburger+ done
qed (auto simp: qdeps_UNIV fune_UNIV pre_transl) 
  
lemma strip_transl: "Nielson_VCGi.strip (transl C) = Nielson_VCG.strip C"
  by (induct C, auto)

   
lemma vc_restrict_complete:
  assumes  "\<turnstile>\<^sub>1 {P} c { e \<Down> Q}"
  shows "\<exists>C. Nielson_VCGi.strip C = c \<and> Nielson_VCGi.vc C Q UNIV UNIV 
  \<and> (\<forall>l s. P l s \<longrightarrow> Nielson_VCGi.pre C Q l s \<and> Q l (Nielson_VCGi.postQ C s))
  \<and> (\<exists>k. \<forall>l s. P l s \<longrightarrow>  Nielson_VCGi.time C s \<le> k * e s)  "
  (is "\<exists>C. ?G P c Q C e")
proof -
  obtain C where C: "Nielson_VCG.strip C = c" "Nielson_VCG.vc C Q" "(\<forall>l s. P l s \<longrightarrow> Nielson_VCG.pre C Q l s \<and> Q l (Nielson_VCG.postQ C s))"
        "(\<exists>k. \<forall>l s. P l s \<longrightarrow> Nielson_VCG.time C s \<le> k * e s)" using vc_complete[OF assms] by blast
  let ?C="transl C"
  from C have "?G P c Q ?C e" 
    by(auto simp: strip_transl vc_transl pre_transl postQ_transl time_transl)
  then show ?thesis ..
qed



end