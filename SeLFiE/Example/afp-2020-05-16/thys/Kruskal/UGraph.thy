section \<open>UGraph - undirected graph with Uprod edges\<close>

theory UGraph
  imports 
    "Automatic_Refinement.Misc"
    "Collections.Partial_Equivalence_Relation"
    "HOL-Library.Uprod"   
begin

subsection "Edge path"

fun epath :: "'a uprod set \<Rightarrow> 'a \<Rightarrow> ('a uprod) list \<Rightarrow> 'a \<Rightarrow> bool"  where
  "epath E u [] v = (u = v)"
| "epath E u (x#xs) v \<longleftrightarrow> (\<exists>w. u\<noteq>w \<and> Upair u w = x \<and> epath E w xs v) \<and> x\<in>E"  

lemma [simp,intro!]: "epath E u [] u" by simp

lemma epath_subset_E: "epath E u p v \<Longrightarrow> set p \<subseteq> E"
  apply(induct p arbitrary: u) by auto 

lemma path_append_conv[simp]: "epath E u (p@q) v \<longleftrightarrow> (\<exists>w. epath E u p w \<and> epath E w q v)"
  apply(induct p arbitrary: u) by auto

lemma epath_rev[simp]: "epath E y (rev p) x = epath E x p y"
  apply(induct p arbitrary: x) by auto

lemma "epath E x p y \<Longrightarrow> \<exists>p. epath E y p x"
  apply(rule exI[where x="rev p"]) by simp

lemma epath_mono: "E \<subseteq> E' \<Longrightarrow> epath E u p v \<Longrightarrow> epath E' u p v"
  apply(induct p arbitrary: u) by auto

lemma epath_restrict: "set p \<subseteq> I \<Longrightarrow> epath E u p v \<Longrightarrow> epath (E\<inter>I) u p v"
  apply(induct p arbitrary: u)
  by auto

lemma assumes "A\<subseteq>A'" "~ epath A u p v" "epath A' u p v"
  shows epath_diff_edge: "(\<exists>e. e\<in>set p - A)"
proof (rule ccontr)
  assume "\<not>(\<exists>e. e \<in> set p - A)" 
  then have i: "set p \<subseteq> A"
    by auto
  have ii: "A = A' \<inter> A" using assms(1) by auto
  have "epath A u p v" 
    apply(subst ii) 
    apply(rule epath_restrict  ) by fact+
  with assms(2) show "False" by auto    
qed


lemma epath_restrict': "epath (insert e E) u p v \<Longrightarrow>  e\<notin>set p \<Longrightarrow> epath E u p v"
proof -
  assume a: "epath (insert e E) u p v" and "e\<notin>set p"
  then have b: "set p \<subseteq> E" by(auto dest: epath_subset_E)
  have e: "insert e E \<inter> E = E " by auto   
  show ?thesis apply(rule epath_restrict[where I=E and E="insert e E", simplified e] )
    using a b by auto
qed

lemma epath_not_direct:
  assumes ep: "epath E u p v" and unv: "u \<noteq> v"
    and edge_notin: "Upair u v \<notin> E" 
  shows "length p \<ge> 2"
proof (rule ccontr)
  from ep have setp: "set p \<subseteq> E" using epath_subset_E by fast
  assume "\<not>length p \<ge> 2"
  then have "length p <2" by auto
  moreover
  {
    assume "length p = 0"
    then have "p=[]" by auto
    with ep unv have "False" by auto
  } moreover {
    assume "length p = 1"
    then obtain e where p: "p = [e]"
      using list_decomp_1 by blast 
    with ep have i: "e=Upair u v" by auto
    from p i setp and edge_notin have "False" by auto
  }
  ultimately show "False" by linarith
qed


lemma epath_decompose:
  assumes e: "epath G v p v'"
    and elem :"Upair a b \<in> set p"
  shows  "\<exists> u u' p' p'' . u \<in> {a, b} \<and> u' \<in> {a, b} \<and> epath G v p' u \<and> epath G u' p'' v' \<and>
          length p' < length p \<and> length p'' < length p"
proof -
  from elem obtain p' p'' where p: "p = p' @ (Upair a b) # p''" using in_set_conv_decomp
    by metis
  from p have "epath G v (p' @ (Upair a b) # p'') v'" using e by auto
  then obtain z z' where pr: "epath G v p' z"  "epath G z' p'' v'" and u: "Upair z z'=Upair a b"   by auto 
  from u have u': "z \<in> {a, b} \<and> z' \<in> {a, b}" by auto
  have len: "length p' < length p"  "length p'' < length p" using p by auto    
  from len pr u' show ?thesis by auto
qed

lemma epath_decompose':
  assumes e: "epath G v p v'"
    and elem :"Upair a b \<in> set p"
  shows  "\<exists> u u' p' p'' . Upair a b = Upair u u' \<and> epath G v p' u \<and> epath G u' p'' v' \<and>
          length p' < length p \<and> length p'' < length p"
proof -
  from elem obtain p' p'' where p: "p = p' @ (Upair a b) # p''" using in_set_conv_decomp
    by metis
  from p have "epath G v (p' @ (Upair a b) # p'') v'" using e by auto
  then obtain z z' where pr: "epath G v p' z"  "epath G z' p'' v'" and u: "Upair z z'=Upair a b"   by auto 
  have len: "length p' < length p"  "length p'' < length p" using p by auto    
  from len pr u show ?thesis by auto
qed


(* adapted from Julian's is_path_undir_split_distinct *)
lemma epath_split_distinct:
  assumes "epath G v p v'"
  assumes "Upair a b \<in> set p"
  shows "(\<exists>p' p'' u u'.
            epath G v p' u \<and> epath G u' p'' v' \<and>
            length p' < length p \<and> length p'' < length p \<and>
            (u \<in> {a, b} \<and> u' \<in> {a, b}) \<and>
            Upair a b \<notin> set p' \<and> Upair a b \<notin> set p'')"
  using assms
proof (induction n == "length p" arbitrary: p v v' rule: nat_less_induct)
  case 1
  obtain u u' p' p'' where u: "u \<in> {a, b} \<and> u' \<in> {a, b}"
    and p': "epath G v p' u" and p'': "epath G u' p'' v'"
    and len_p': "length p' < length p" and len_p'': "length p'' < length p"
    using epath_decompose[OF 1(2,3)] by blast
  from 1 len_p' p' have "Upair a b \<in> set p' \<longrightarrow> (\<exists>p'2 u2.
            epath G v p'2 u2 \<and>
            length p'2 < length p' \<and>
            u2 \<in> {a, b} \<and>
            Upair a b \<notin> set p'2)"
    by metis
  with len_p' p' u have p': "\<exists>p' u. epath G v p' u \<and> length p' < length p \<and>
      u \<in> {a,b} \<and> Upair a b \<notin> set p' \<and> Upair a b \<notin> set p'"
    by fastforce
  from 1 len_p'' p'' have "Upair a b \<in> set p'' \<longrightarrow> (\<exists>p''2 u'2.
            epath G u'2 p''2 v' \<and>
            length p''2 < length p'' \<and>
            u'2 \<in> {a, b} \<and>
            Upair a b \<notin> set p''2 \<and> Upair a b \<notin> set p''2)"
    by metis
  with len_p'' p'' u have "\<exists>p'' u'. epath G u' p'' v'\<and> length p'' < length p \<and>
      u' \<in> {a,b} \<and> Upair a b \<notin> set p'' \<and> Upair a b \<notin> set p''"
    by fastforce
  with p' show ?case by auto
qed

 

subsection "Distinct edge path"


definition "depath E u dp v \<equiv> epath E u dp v \<and> distinct dp"      

lemma epath_to_depath: "set p \<subseteq> I \<Longrightarrow> epath E u p v \<Longrightarrow> \<exists>dp. depath E u dp v \<and> set dp \<subseteq> I"
proof (induction p rule: length_induct)
  case (1 p)
  hence IH: "\<And>p'. \<lbrakk>length p' < length p; set p' \<subseteq> I; epath E u p' v\<rbrakk> 
    \<Longrightarrow> \<exists>p'. depath E u p' v \<and> set p' \<subseteq> I"
    and PATH: "epath E u p v"
    and set: "set p \<subseteq> I"
    by auto

  show "\<exists>p. depath E u p v \<and> set p \<subseteq> I"  
  proof cases
    assume "distinct p"
    thus ?thesis using PATH set by (auto simp: depath_def)
  next
    assume "\<not>(distinct p)"  
    then obtain pv1 pv2 pv3 w where p: "p = pv1@w#pv2@w#pv3" 
      by (auto dest: not_distinct_decomp) 
    with PATH obtain a where 1: "epath E u pv1 a" and 2:"epath E a (w#pv2@w#pv3) v" by auto
    then obtain b where ab: "w=Upair a b" "a\<noteq>b" by auto 
    with 2 have "epath E b (pv2@w#pv3) v" by auto
    then obtain c where 3: "epath E b pv2 c" and 4: "epath E c (w#pv3) v" by auto
    then have cw: "c\<in>set_uprod w" by auto
    { assume "c=a"
      then have "length (pv1@w#pv3) < length p" "set (pv1@w#pv3) \<subseteq> I" "epath E u (pv1@w#pv3) v"
        using 1 4 p set by auto
      hence "\<exists>p'. depath E u p' v \<and> set p' \<subseteq> I" by (rule IH)
    }
    moreover
    { assume "c\<noteq>a"
      with ab cw have "c=b" by auto
      with 4 ab have "epath E a pv3 v" by auto
      then have "length (pv1@pv3) < length p" "set (pv1@pv3) \<subseteq> I" "epath E u (pv1@pv3) v" using p 1 set by auto
      hence "\<exists>p'. depath E u p' v \<and> set p' \<subseteq> I" by (rule IH)
    }
    ultimately show ?case by auto
  qed
qed

lemma epath_to_depath': "epath E u p v \<Longrightarrow> \<exists>dp. depath E u dp v"
  using epath_to_depath[where I="set p"] by blast

definition "decycle E u p == epath E u p u \<and> length p > 2 \<and> distinct p"

subsection "Connectivity in undirected Graphs"    

definition "uconnected E \<equiv> {(u,v). \<exists>p. epath E u p v}"  

lemma uconnectedempty: "uconnected {} = {(a,a)|a. True}"
  unfolding uconnected_def 
  using epath.elims(2) by fastforce    

lemma uconnected_refl: "refl (uconnected E)"
  by(auto simp: refl_on_def uconnected_def)  

lemma uconnected_sym: "sym (uconnected E)"
  apply(clarsimp simp: sym_def uconnected_def) 
  subgoal for x y p apply (rule exI[where x="rev p"]) by (auto) done
lemma uconnected_trans: "trans (uconnected E)"
  apply(clarsimp simp: trans_def uconnected_def) 
  subgoal for x y p z q by (rule exI[where x="p@q"], auto) done

lemma uconnected_symI: "(u,v) \<in> uconnected E \<Longrightarrow> (v,u) \<in> uconnected E"    
  using uconnected_sym sym_def by fast

lemma "equiv UNIV (uconnected E)"
  apply (rule equivI)
  subgoal by (auto simp: refl_on_def uconnected_def) 
  subgoal apply(clarsimp simp: sym_def uconnected_def) subgoal for x y p apply (rule exI[where x="rev p"]) by auto done
  by (fact uconnected_trans)


lemma uconnected_refcl: "(uconnected E)\<^sup>* = (uconnected E)\<^sup>="
  apply(rule trans_rtrancl_eq_reflcl)
  by (fact uconnected_trans)

lemma uconnected_transcl: "(uconnected E)\<^sup>* = uconnected E"
  apply (simp only: uconnected_refcl)
  by (auto simp: uconnected_def)

lemma uconnected_mono: "A\<subseteq>A' \<Longrightarrow> uconnected A \<subseteq> uconnected A'"
  unfolding uconnected_def apply(auto)
    using epath_mono by metis



lemma findaugmenting_edge: assumes "epath E1 u p v"
  and "\<not>(\<exists>p. epath E2 u p v)"
shows "\<exists>a b. (a,b) \<notin> uconnected E2 \<and> Upair a b \<notin> E2 \<and> Upair a b \<in> E1"
  using assms
proof (induct p arbitrary: u)
  case Nil 
  then show ?case by auto
next
  case (Cons a p)
  then obtain w where axy: "a=Upair u w" "u\<noteq>w" and e': "epath E1 w p v"
      and uwE1: "Upair u w \<in> E1" by auto
  show ?case
  proof (cases "a\<in>E2")
    case True
    have e2': "\<not>(\<exists>p. epath E2 w p v)"
    proof (rule ccontr, clarsimp)
      fix p2
      assume "epath E2 w p2 v"
      with True axy have "epath E2 u (a#p2) v" by auto
      with Cons(3) show False by blast
    qed
    from Cons(1)[OF e' e2'] show ?thesis .
  next
    case False
    {
      assume e2': "\<not>(\<exists>p. epath E2 w p v)"
      from Cons(1)[OF e' e2'] have ?thesis .
    } moreover {
      assume e2': "\<exists>p. epath E2 w p v"
      then obtain p1 where p1: "epath E2 w p1 v" by auto  

      from False axy have "Upair u w\<notin>E2" by auto
      moreover
      have "(u,w) \<notin> uconnected E2"
      proof(rule ccontr, auto simp add: uconnected_def)
        fix p2 
        assume "epath E2 u p2 w"
        with p1 have "epath E2 u (p2@p1) v" by auto
        then show "False" using Cons(3) by blast
      qed
      moreover
      note uwE1   
      ultimately have ?thesis by auto
    }
    ultimately show ?thesis by auto
  qed
qed


subsection "Forest"

definition "forest E \<equiv> ~(\<exists>u p. decycle E u p)"

lemma forest_mono: "Y \<subseteq> X \<Longrightarrow> forest X \<Longrightarrow> forest Y"  
  unfolding forest_def decycle_def apply (auto) using epath_mono by metis

lemma forrest2_E: assumes "(u,v) \<in> uconnected E"
  and "Upair u v \<notin> E"                    
  and "u \<noteq> v" 
shows "~ forest (insert (Upair u v) E)"
proof -
  from assms[unfolded uconnected_def] obtain p' where "epath E u p' v" by blast
  then obtain p where ep: "epath E u p v" and dep: "distinct p" using epath_to_depath' unfolding depath_def by fast
  from ep have setp: "set p \<subseteq> E" using epath_subset_E by fast

  have lengthp: "length p \<ge> 2" apply(rule epath_not_direct) by fact+

  from epath_mono[OF _ ep] have ep': "epath (insert (Upair u v) E) u p v" by auto

  have "epath (insert (Upair u v) E) v ((Upair u v)#p) v" "length ((Upair u v)#p) > 2"  "distinct ((Upair u v)#p)"
    using ep' assms(3) lengthp dep setp assms(2) by auto
  then have "decycle (insert (Upair u v) E) v ((Upair u v)#p)" unfolding decycle_def by auto
  then show ?thesis unfolding forest_def by auto
qed

lemma insert_stays_forest_means_not_connected: assumes "forest (insert (Upair u v) E)"
  and "(Upair u v) \<notin> E"
  and "u \<noteq> v"
shows "~ (u,v) \<in> uconnected E"
  using forrest2_E assms by metis 

lemma epath_singleton: "epath F a [e] b \<Longrightarrow> e = Upair a b"
  by auto

lemma forest_alt1: 
  assumes " Upair a b \<in> F" "forest F" "\<And>e. e\<in>F \<Longrightarrow> proper_uprod e"
  shows "(a,b) \<notin>  uconnected (F - {Upair a b})"
proof (rule ccontr)
  from assms(1,3) have anb: "a\<noteq>b" by force
  assume "\<not> (a, b) \<notin> uconnected (F - {Upair a b})"
  then obtain p where "epath (F - {Upair a b}) a p b" unfolding uconnected_def  by blast
  then obtain p' where dp: "depath (F - {Upair a b}) a p' b" using epath_to_depath' by force
  then have ab: "Upair a b \<notin> set p'" by(auto simp: depath_def dest: epath_subset_E)
  from anb dp have n0: "length p' \<noteq> 0" by (auto simp: depath_def)
  from ab dp have n1: "length p' \<noteq> 1" by (auto simp: depath_def simp del: One_nat_def dest!: list_decomp_1)
  from n0 n1 have l: "length p' \<ge> 2" by linarith
  from dp have "epath F a p' b" by (auto intro: epath_mono simp: depath_def)
  then have e: "epath F b (Upair a b#p') b" using assms(1) anb by auto
  from dp ab have d: "distinct (Upair a b#p')" by (auto simp: depath_def)
  from d e l have "decycle F b (Upair a b#p')" by (auto simp: decycle_def)
  with assms(2) show "False" by (simp add: forest_def)
qed


lemma forest_alt2: 
  assumes "\<And>e. e\<in>F \<Longrightarrow> proper_uprod e"
    and "\<And>a b. Upair a b \<in> F \<Longrightarrow> (a,b) \<notin>  uconnected (F - {Upair a b})"
  shows "forest F"
proof (rule ccontr)
  assume "\<not> forest F"  
  then obtain a p where e: "epath F a p a" "length p > 2" "distinct p"
    unfolding decycle_def forest_def by auto
  then obtain b p' where p': "p = Upair a b # p'" 
    by (metis Suc_1 epath.simps(2) less_imp_not_less list.size(3) neq_NilE zero_less_Suc)
  then have u: "Upair a b\<in>F" using e(1) by auto
  then have F: "(insert (Upair a b) F) = F" by auto
  have "epath (F - {Upair a b}) b p' a"
    apply(rule epath_restrict'[where e="Upair a b"]) using e  p' by (auto simp: F)
  then have "epath (F - {Upair a b}) a (rev p') b" by auto
  with   assms(2)[OF u]
  show "False" unfolding uconnected_def by blast
qed


lemma forest_alt:
  assumes "\<And>e. e\<in>F \<Longrightarrow> proper_uprod e"
  shows "forest F \<longleftrightarrow> (\<forall>a b. Upair a b \<in> F \<longrightarrow> (a,b) \<notin>  uconnected (F - {Upair a b})) "
  using assms forest_alt1 forest_alt2
  by metis
  


lemma augment_forest_overedges: 
  assumes "F\<subseteq>E" "forest F" "(Upair u v) \<in> E" "(u,v) \<notin> uconnected F"
    and notsame: "u\<noteq>v"
  shows "forest (insert (Upair u v) F)"
  unfolding forest_def 
proof (rule ccontr, clarsimp simp: decycle_def )
  fix w p 
  assume d: "distinct p" and v: "epath (insert (Upair u v) F) w p w" and p: "2 < length p"

  have setep: "set p \<subseteq> insert (Upair u v) F" using epath_subset_E v
    by metis

  have uvF: "(Upair u v)\<notin>F"
  proof(rule ccontr, clarsimp)
    assume "(Upair u v) \<in> F"
    then have "epath F u [(Upair u v)] v" using notsame by auto
    then have "(u,v) \<in> uconnected F" unfolding  uconnected_def by blast
    then show "False" using assms(4) by auto
  qed
  have k: "insert (Upair u v) F \<inter> F = F" by auto

  show False
  proof (cases)
    assume "(Upair u v) \<in> set p"
    then obtain as bs where ep: "p = as @ (Upair u v) # bs" using in_set_conv_decomp
      by metis
    then have "epath (insert (Upair u v) F) w (as @ (Upair u v) # bs) w" using v by auto
    then obtain z where pr: "epath (insert (Upair u v) F) w as z"   "epath (insert (Upair u v) F) z ((Upair u v) # bs) w"   by auto  
    from d ep have uvas: "(Upair u v) \<notin> set (as@bs)" by auto
    then have setasbs: "set (bs@as) \<subseteq> F" using ep setep by auto
    { assume "z=u"
      with pr have "epath (insert (Upair u v) F) w as u"   "epath (insert(Upair u v) F) v bs w" by auto
      then have "epath (insert (Upair u v) F) v (bs@as) u" by auto
      from epath_restrict[where I=F, OF setasbs this] have "epath F v (bs@as) u" using uvF by auto
      then have "(v,u) \<in> uconnected F" using uconnected_def
        by blast
      then have "(u,v) \<in> uconnected F" by (rule uconnected_symI)
    } moreover
    { assume "z\<noteq>u"
      then have "z=v" using pr(2) by auto
      with pr have "epath (insert (Upair u v) F) w as v"   "epath (insert (Upair u v) F) u bs w" by auto
      then have "epath (insert (Upair u v) F) u (bs@as) v" by auto
      from epath_restrict[where I=F, OF setasbs this] have "epath F u (bs@as) v" using uvF by auto
      then have "(u,v) \<in> uconnected F" using uconnected_def
        by fast  
    }
    ultimately have "(u,v) \<in> uconnected F" by auto 
    then show "False" using assms by auto 
  next
    assume "(Upair u v) \<notin> set p" 
    with setep have "set p \<subseteq> F" by auto
    then have "epath (insert (Upair u v) F \<inter> F) w p w" using epath_restrict[OF _ v, where I="F"] by auto
    then have "epath F w p w" using k by auto 
    with \<open>forest F\<close> show "False" unfolding forest_def decycle_def using p d
      by auto
  qed
qed


subsection "uGraph locale"

locale uGraph =
  fixes E :: "'a uprod set"   
    and w :: "'a uprod \<Rightarrow> 'c::{linorder, ordered_comm_monoid_add}"
  assumes ecard2: "\<And>e. e\<in>E \<Longrightarrow> proper_uprod e" 
    and finiteE[simp]: "finite E"
begin

abbreviation "uconnected_on E' V \<equiv> uconnected E' \<inter> (V\<times>V)"

abbreviation "verts \<equiv> \<Union>(set_uprod ` E)"

lemma set_uprod_nonemptyY[simp]: "set_uprod x  \<noteq> {}" apply(cases x) by auto
 

abbreviation "uconnectedV E' \<equiv> Restr (uconnected E') verts"


lemma equiv_unconnected_on: "equiv V (uconnected_on E' V)"
  apply (rule equivI)
  subgoal by (auto simp: refl_on_def uconnected_def) 
  subgoal apply(clarsimp simp: sym_def uconnected_def) subgoal for x y p apply (rule exI[where x="rev p"]) by (auto) done
  subgoal apply(clarsimp simp: trans_def uconnected_def) subgoal for x y z p q apply (rule exI[where x="p@q"]) by auto done
  done

lemma uconnectedV_refl: "E'\<subseteq>E \<Longrightarrow> refl_on verts (uconnectedV E')"
  by(auto simp: refl_on_def uconnected_def) 

lemma uconnectedV_trans: "trans (uconnectedV E')"
  apply(clarsimp simp: trans_def uconnected_def) subgoal for x y z p a b c q apply (rule exI[where x="p@q"]) by auto done
lemma uconnectedV_sym: "sym (uconnectedV E')"
  apply(clarsimp simp: sym_def uconnected_def) subgoal for x y p apply (rule exI[where x="rev p"]) by (auto) done

lemma equiv_vert_uconnected: "equiv verts (uconnectedV E')"
  using equiv_unconnected_on by auto



lemma uconnectedV_tracl: "(uconnectedV F)\<^sup>* = (uconnectedV F)\<^sup>="
  apply(rule trans_rtrancl_eq_reflcl)
  by (fact uconnectedV_trans) 

lemma uconnectedV_cl: "(uconnectedV F)\<^sup>+ = (uconnectedV F)"
  apply(rule trancl_id)
  by (fact uconnectedV_trans) 

lemma uconnectedV_Restrcl: "Restr ((uconnectedV F)\<^sup>*) verts = (uconnectedV F)"
  apply(simp only: uconnectedV_tracl)
  apply auto unfolding uconnected_def by auto

lemma restr_ucon: "F \<subseteq> E \<Longrightarrow> uconnected F = uconnectedV F \<union> Id"
  unfolding uconnected_def apply auto  
proof (goal_cases)
  case (1 a b p)
  then have "p\<noteq>[]" by auto
  then obtain e es where "p=e#es"
    using list.exhaust by blast 
  with 1(2) have "a\<in> set_uprod e" "e\<in>F" by auto    
  then show ?case using 1(1)
    by blast
next
  case (2 a b p)
  then have "rev p\<noteq>[]" "epath F b (rev p) a" by auto
  then obtain e es where "rev p=e#es"
    using list.exhaust by metis
  with 2(2) have "b\<in> set_uprod e" "e\<in>F" by auto    
  then show ?case using 2(1)
    by blast
qed

lemma relI:
  assumes "\<And>a b. (a,b) \<in> F \<Longrightarrow> (a,b) \<in> G"
    and "\<And>a b. (a,b) \<in> G \<Longrightarrow> (a,b) \<in> F" shows "F=G"
  using assms by auto

lemma in_per_union: "u \<in> {x, y} \<Longrightarrow>  u' \<in> {x, y} \<Longrightarrow>  x\<in>V \<Longrightarrow> y\<in>V \<Longrightarrow>
    refl_on V R \<Longrightarrow> part_equiv R  \<Longrightarrow> (u, u') \<in> per_union R x y"
  by (auto simp: per_union_def dest: refl_onD) 

lemma uconnectedV_mono: " (a,b)\<in>uconnectedV F \<Longrightarrow> F\<subseteq>F' \<Longrightarrow> (a,b)\<in>uconnectedV F'"
  unfolding uconnected_def by (auto intro: epath_mono)

lemma per_union_subs: "x \<in> S \<Longrightarrow> y\<in>S \<Longrightarrow> R\<subseteq>S \<times> S \<Longrightarrow> per_union R x y \<subseteq> S \<times> S"
  unfolding per_union_def by auto

(* adapted preserve_corresponding_union_find_add by Julian Biendarra *)
lemma insert_uconnectedV_per: 
  assumes  "x\<noteq>y" and inV: "x\<in>verts" "y\<in>verts" and subE: "F\<subseteq>E"
  shows "uconnectedV (insert (Upair x y) F) = per_union (uconnectedV F) x y"
    (is "uconnectedV ?F' = per_union ?uf x y")
proof -
  have PER: "part_equiv (uconnectedV F)" unfolding part_equiv_def 
    using uconnectedV_sym uconnectedV_trans by auto
  from PER have PER': "part_equiv (per_union (uconnectedV F) x y)"
    by (auto simp: union_part_equivp)
  have ref: "refl_on verts (uconnectedV F)" using uconnectedV_refl assms(4) by auto

  show ?thesis
  proof (rule relI)
    fix a b
    assume "(a,b) \<in> uconnectedV ?F'"
    then obtain p where p: "epath ?F' a p b" and ab: "a\<in>verts" "b\<in>verts"
      unfolding uconnected_def 
      by blast
    show "(a,b)\<in>per_union (uconnectedV F) x y"
    proof (cases "Upair x y\<in>set p")
      case True
      obtain p' p'' u u' where
        "epath ?F' a p' u" "epath ?F' u' p'' b"and
        u: "u\<in>{x,y} \<and> u'\<in>{x,y}" and
        "Upair x y \<notin> set p'" "Upair x y \<notin> set p''"
        using epath_split_distinct[OF p True] by blast
      then have "epath F a p' u" "epath F u' p'' b" by(auto intro: epath_restrict')
      then have a: "(a,u)\<in>(uconnectedV F)" and b: "(u',b)\<in>(uconnectedV F)"
        unfolding uconnected_def using u ab assms by auto

      from a 
      have "(a,u)\<in>per_union ?uf x y" by (auto simp: per_union_def)
      also 
      have "(u,u')\<in>per_union ?uf x y" apply (rule in_per_union) using u inV ref PER by auto
      also (part_equiv_trans[OF PER'])
      have "(u',b)\<in>per_union ?uf x y" using b by (auto simp: per_union_def) 
      finally (part_equiv_trans[OF PER'])
      show "(a,b)\<in>per_union ?uf x y" .
    next
      case False
      with p have "epath F a p b" by(auto intro: epath_restrict')
      then have "(a,b)\<in>uconnectedV F" using ab by (auto simp: uconnected_def)
      then show ?thesis unfolding per_union_def by auto 
    qed
  next
    fix a b
    assume asm: "(a,b)\<in>per_union ?uf x y" 
    have "per_union ?uf x y \<subseteq> verts \<times> verts" apply(rule per_union_subs)
      using inV by auto 
    with asm have ab: "a\<in>verts" "b\<in>verts" by auto
    have "Upair x y \<in> ?F'" by simp
    show "(a,b) \<in> uconnectedV ?F'"
    proof (cases "(a, b) \<in> ?uf")
      case True
      then show ?thesis using uconnectedV_mono by blast
    next
      case False
      with asm part_equiv_sym[OF PER]
      have "(a,x) \<in> ?uf \<and> (y,b) \<in> ?uf  \<or>  (a,y) \<in> ?uf \<and> (x,b) \<in> ?uf"
        by (auto simp: per_union_def)
      with assms(1) \<open>x\<in>verts\<close> \<open>y\<in>verts\<close> inV  obtain p q p' q'
        where "epath F a p x \<and> epath F y q b  \<or>  epath F a p' y \<and> epath F x q' b"
        unfolding uconnected_def
        by fastforce
      then have "epath ?F' a p x \<and> epath ?F' y q b  \<or>  epath ?F' a p' y \<and> epath ?F' x q' b"
        by (auto intro: epath_mono)
      then have 2: "epath ?F' a (p @ Upair x y # q) b \<or>  epath ?F' a (p' @ Upair x y # q') b"
        using assms(1) by auto 
      then show ?thesis unfolding uconnected_def
        using ab by blast
    qed
  qed
qed


lemma epath_filter_selfloop: "epath (insert (Upair x x) F) a p b \<Longrightarrow> \<exists>p. epath F a p b"
proof (induction n == "length p" arbitrary: p  rule: nat_less_induct)
  case 1
  from 1(1) have indhyp:
      "\<And>xa. length xa < length p \<Longrightarrow> epath (insert (Upair x x) F) a xa b \<Longrightarrow> (\<exists>p. epath F a p b)" by auto
  
  from 1(2) have k: "set p \<subseteq> (insert (Upair x x) F)" using epath_subset_E by fast
  { assume a: "set p \<subseteq> F"
    have F: "(insert (Upair x x) F \<inter> F) = F" by auto
    from epath_restrict[OF a 1(2)] F have "epath F a p b" by simp
    then have "(\<exists>p. epath F a p b)" by auto
  } moreover
  { assume "\<not> set p \<subseteq> F"
    with k have "Upair x x \<in> set p" by auto
    then obtain xs ys where p: "p = xs @ Upair x x # ys"  
      by (meson split_list_last) 
    then have "epath (insert (Upair x x) F) a xs x"  "epath (insert (Upair x x) F) x ys b" 
      using "1.prems" by auto  
    then have "epath (insert (Upair x x) F) a (xs@ys) b" by auto
    from indhyp[OF _ this] p have "(\<exists>p. epath F a p b)" by simp
  }
  ultimately show ?thesis by auto
qed


lemma uconnectedV_insert_selfloop: "x\<in>verts \<Longrightarrow> uconnectedV (insert (Upair x x) F) = uconnectedV F"
  apply(rule)
   apply auto 
  subgoal unfolding uconnected_def apply auto using epath_filter_selfloop by metis
  subgoal by (meson subsetCE subset_insertI uconnected_mono) 
  done

lemma equiv_selfloop_per_union_id: "equiv S F \<Longrightarrow> x\<in>S \<Longrightarrow> per_union F x x = F"
  apply rule
  subgoal unfolding per_union_def     
    using equiv_class_eq_iff by fastforce 
  subgoal unfolding per_union_def by auto
  done
  

lemma insert_uconnectedV_per_eq: 
  assumes    inV: "x\<in>verts"   and subE: "F\<subseteq>E"
  shows "uconnectedV (insert (Upair x x) F) = per_union (uconnectedV F) x x"
  using assms
  by(simp add: uconnectedV_insert_selfloop equiv_selfloop_per_union_id[OF equiv_vert_uconnected])

lemma insert_uconnectedV_per': 
  assumes  inV: "x\<in>verts" "y\<in>verts" and subE: "F\<subseteq>E"
  shows "uconnectedV (insert (Upair x y) F) = per_union (uconnectedV F) x y"
  apply(cases "x=y")
  subgoal using assms insert_uconnectedV_per_eq by simp 
  subgoal using assms insert_uconnectedV_per by simp
  done


definition "subforest F \<equiv> forest F \<and> F \<subseteq> E"

definition spanningForest where "spanningForest X \<longleftrightarrow> subforest X \<and> (\<forall>x \<in> E - X. \<not> subforest (insert x X))"

definition "minSpanningForest F \<equiv> spanningForest F \<and> (\<forall>F'. spanningForest F' \<longrightarrow> sum w F \<le> sum w F')"

end

end