theory well_founded_continued

(* N. Peltier - http://membres-lig.imag.fr/peltier/ *)

imports Main

begin

subsection \<open>Well-Founded Sets\<close>

text \<open>Most useful lemmata are already proven in the Well\_Founded theory available in Isabelle. 
We only establish a few convenient results for constructing well-founded sets and relations.\<close>

lemma measure_wf:
  assumes "wf (r :: ('a \<times> 'a) set)"
  assumes "r' = { (x,y). ((m x),(m y)) \<in> r }"
  shows "wf r'"
proof -
  have "(\<forall>Q::'b set. \<forall>x:: 'b. x\<in>Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (y,z)\<in> r' --> y\<notin>Q))"
  proof  ((rule allI)+,(rule impI))
    fix Q:: "'b set" fix x:: 'b assume "x\<in>Q"
    let ?Q' = "(m ` Q)"
    from \<open>x \<in> Q\<close> have Q'_not_empty: "m x \<in> ?Q'" by auto
    from assms(1) and Q'_not_empty obtain z' where "z' \<in> ?Q'" and z'min: "\<forall>y. (y,z')\<in> r 
      \<longrightarrow> y\<notin>?Q'" using wf_eq_minimal [of r] by blast
    from \<open>z' \<in> ?Q'\<close> obtain z where "z' = (m z)" and "z \<in> Q" by auto
    have "\<forall>y. (y,z)\<in> r' \<longrightarrow> y\<notin>Q"
    proof ((rule allI),(rule impI))
      fix y assume "(y,z)\<in> r'"
      from assms(2) and this and \<open>z' = (m z)\<close> have "((m y),z') \<in> r" by auto
      from this and z'min have "(m y) \<notin> ?Q'" by auto
      then show "y\<notin>Q" by auto
    qed
    from this and \<open>z \<in> Q\<close> show "(\<exists>z\<in>Q. \<forall>y. (y,z)\<in> r' --> y\<notin>Q)"  by auto
  qed
  then show ?thesis using wf_eq_minimal by auto
qed

lemma finite_proj_wf:
  assumes "finite E"
  assumes "x \<in> E"
  assumes "acyclic r"
  shows "(\<exists> y. y \<in> E \<and> (\<forall> z. (z, y) \<in> r \<longrightarrow> z \<notin> E))"
proof -
  let ?r = "{ (u,v). (u \<in> E \<and> v \<in> E \<and> (u,v) \<in> r) }"
  from assms(1) have "finite (E \<times> E)" by auto
  have "?r \<subseteq> (E \<times> E)" by auto
  have "?r \<subseteq> r" by auto
  from \<open>?r \<subseteq> (E \<times> E)\<close> and \<open>finite (E \<times> E)\<close> have "finite ?r" using finite_subset by auto
  from assms(3) and \<open>?r \<subseteq> r\<close> have "acyclic ?r" unfolding acyclic_def using trancl_mono by blast 
  from \<open>acyclic ?r\<close> \<open>finite ?r\<close> have "wf ?r" using finite_acyclic_wf by auto
  from this assms(2) obtain y where "y \<in> E" and i: "\<And>z. (z, y) \<in> ?r \<Longrightarrow> z \<notin> E"  
    using wfE_min [of "?r" x E] by blast
  have "\<forall>z. (z, y) \<in> r \<longrightarrow> z \<notin> E"
  proof (rule allI,rule impI)
    fix z assume "(z,y) \<in> r"
    show "z \<notin> E"
    proof 
      assume "z \<in> E"
      from this and \<open>y \<in> E\<close> and \<open>(z,y) \<in> r\<close> have "(z,y) \<in> ?r" by auto
      from this and i [of z] and \<open>z \<in> E\<close> show False by auto
    qed
  qed
  from this and \<open>y \<in> E\<close> show ?thesis by auto
qed

end
