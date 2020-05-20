chapter "Rotational Symmetries of the Tetrahedron"

theory Tetrahedron
imports Orbit_Stabiliser
begin

section "Definition of the Tetrahedron and its Rotations"

text \<open>
  In this section we will use the orbit-stabiliser theorem to count the number of rotational symmetries
  of a tetrahedron.

  The tetrahedron will be defined as a set of four vertices, labelled A, B, C, and D. A rotation
  is defined as a function between the vertices.
\<close>

datatype Vertex = A | B | C | D
definition vertices :: "Vertex set" where
  "vertices = {A, B, C, D}"

type_synonym Rotation = "(Vertex \<Rightarrow> Vertex)"

text \<open>
We define four primitive rotations explicitly. The axis of each rotation is the line through a vertex
that is perpendicular to the face opposite to the vertex. Every rotation is by 120 degrees counter clockwise.

We also define the identity as a possible rotation.
\<close>

definition rotate_A :: Rotation where
  "rotate_A = (\<lambda>v. (case v of A \<Rightarrow> A | B \<Rightarrow> C | C \<Rightarrow> D | D \<Rightarrow> B))"
definition rotate_B :: Rotation where
  "rotate_B = (\<lambda>v. (case v of A \<Rightarrow> D | B \<Rightarrow> B | C \<Rightarrow> A | D \<Rightarrow> C))"
definition rotate_C :: Rotation where
  "rotate_C = (\<lambda>v. (case v of A \<Rightarrow> B | B \<Rightarrow> D | C \<Rightarrow> C | D \<Rightarrow> A))"
definition rotate_D :: Rotation where
  "rotate_D = (\<lambda>v. (case v of A \<Rightarrow> C | B \<Rightarrow> A | C \<Rightarrow> B | D \<Rightarrow> D))"

named_theorems simple_rotations
declare rotate_A_def [simple_rotations] rotate_B_def [simple_rotations] rotate_C_def [simple_rotations] rotate_D_def [simple_rotations] 

definition simple_rotations :: "Rotation set" where
  "simple_rotations = {id, rotate_A, rotate_B, rotate_C, rotate_D}"

text \<open>
All other rotations are combinations of the previously defined simple rotations. We define these
inductively.
\<close>
inductive_set complex_rotations :: "Rotation set" where
  simp: "r \<in> simple_rotations \<Longrightarrow> r \<in> complex_rotations" |
  comp: "r \<in> simple_rotations \<Longrightarrow> s \<in> complex_rotations \<Longrightarrow> (r \<circ> s) \<in> complex_rotations"
  
section "Properties of Rotations"

text \<open>
In this section we prove some basic properties of rotations that will be useful later.
We begin by showing that rotations are bijections.
\<close>

lemma simple_rotations_inj:
  assumes r:"r \<in> simple_rotations"
  shows "inj r"  
  using r unfolding simple_rotations_def
  by safe
     (rule injI; rename_tac a b; case_tac a; case_tac b;
      simp add: simple_rotations
     )+

lemma simple_rotations_surj:
  assumes r:"r \<in> simple_rotations"
  shows "surj r"  
  using r unfolding simple_rotations_def
  by safe
     (rename_tac a; case_tac a;
      auto simp add: simple_rotations Vertex.split
     )+

lemma simple_rotations_bij:
  assumes r:"r \<in> simple_rotations"
  shows "bij r"
  by (simp add: r bij_def simple_rotations_surj simple_rotations_inj)

lemma complex_rotations_bij: "r \<in> complex_rotations \<Longrightarrow> bij r"
proof(induction r rule: complex_rotations.induct)
  case (simp r) then show ?case using simple_rotations_bij by simp
next
  case (comp r s) then show ?case using bij_comp simple_rotations_bij by blast
qed

lemma simple_rotation_bij_corollary: "r \<in> simple_rotations \<Longrightarrow> r x \<noteq> r y \<longleftrightarrow> x \<noteq> y"
  using bij_def simple_rotations_bij inj_eq by metis

lemma rotation_bij_corollary: "r \<in> complex_rotations \<Longrightarrow> r x \<noteq> r y \<longleftrightarrow> x \<noteq> y"
  using bij_def complex_rotations_bij inj_eq by metis
    
lemma complex_rotations_comp: 
  "r \<in> complex_rotations \<Longrightarrow> s \<in> complex_rotations \<Longrightarrow> (r \<circ> s) \<in> complex_rotations"
apply(induction arbitrary: s rule: complex_rotations.induct)
apply(auto simp add: comp_assoc complex_rotations.comp)
done
    
text \<open>
Next, we show that simple rotations (except the identity) keep exactly one vertex fixed.
\<close>    

lemma simple_rotations_fix:
  assumes r:"r \<in> simple_rotations"
  shows "\<exists>v. r v = v"
  using r unfolding simple_rotations_def 
  by (auto simp add: simple_rotations split: Vertex.split)

lemma simple_rotations_fix_unique:
  assumes r:"r \<in> simple_rotations"
  shows "r \<noteq> id \<Longrightarrow> r v = v \<Longrightarrow> r w = w \<Longrightarrow> v = w"
  using r unfolding simple_rotations_def 
  by safe 
     (case_tac v; case_tac w; 
      auto simp add: simple_rotations
     )+
   
text \<open>
We also show that simple rotations do not contain cycles of length 2. 
\<close>  
   
lemma simple_rotations_cycle:
  assumes r:"r \<in> simple_rotations"
  shows "r \<noteq> id \<Longrightarrow> r v = w \<Longrightarrow> v \<noteq> w \<Longrightarrow> r w \<noteq> v"
  using r unfolding simple_rotations_def
  by safe
     (case_tac v;
      auto simp add: simple_rotations
     )+ 

text \<open>
The following lemmas are all variations on the fact that any property that holds for 4 distinct
vertices holds for all vertices. This is necessary to avoid having to use Vertex.exhaust as much
as possible.
\<close>  
   
lemma distinct_vertices: "distinct[(a::Vertex),b,c,d] \<Longrightarrow> (\<forall> e. e \<in> {a,b,c,d})"
apply(safe)
apply(case_tac a)
apply(auto simp add: distinct_def)
apply(metis Vertex.exhaust)+
done  
  
lemma distinct_map: "r \<in> complex_rotations \<Longrightarrow> distinct[a,b,c,d] \<Longrightarrow> (\<forall> e \<in> {a,b,c}. r e \<noteq> f) \<Longrightarrow> r d = f"
proof -
  assume r:"r \<in> complex_rotations" and dist:"distinct [a,b,c,d]" and notf:"\<forall> e \<in> {a,b,c}. r e \<noteq> f"
  then have 1:"(\<forall> v. v \<in> {a,b,c,d})" using distinct_vertices by simp
  from complex_rotations_bij have "\<exists> v. r v = f" using r bij_pointE by metis
  then have "\<exists> v \<in> {a,b,c,d}. r v = f" using 1 by blast
  then show "r d = f" using notf by simp
qed
  
lemma distinct_map': "r \<in> complex_rotations \<Longrightarrow> distinct[a,b,c,d] \<Longrightarrow> (\<forall> e \<in> {a,b,c}. r f \<noteq> e) \<Longrightarrow> r f = d"
proof -
  assume r:"r \<in> complex_rotations" and dist:"distinct [a,b,c,d]" and notf:"\<forall> e \<in> {a,b,c}. r f \<noteq> e"
  then have 1:"(\<forall> v. v \<in> {a,b,c,d})" using distinct_vertices by simp
  have "\<exists> v. r f = v" by simp
  then have "\<exists> v \<in> {a,b,c,d}. r f = v" using 1 by blast
  then show "r f = d" using notf by simp
qed 
  
lemma cycle_map: "r \<in> complex_rotations \<Longrightarrow> distinct[a,b,c,d] \<Longrightarrow> 
  r a = b \<Longrightarrow> r b = a \<Longrightarrow> r c = d \<Longrightarrow> r d = c \<Longrightarrow> \<forall> v w. r v = w \<longrightarrow> r w = v"
  using distinct_map' rotation_bij_corollary by fastforce
  
lemma simple_distinct_map: "r \<in> simple_rotations \<Longrightarrow> distinct[a,b,c,d] \<Longrightarrow> (\<forall> e \<in> {a,b,c}. r e \<noteq> f) \<Longrightarrow> r d = f"
  using complex_rotations.simp distinct_map by simp

lemma simple_distinct_map': "r \<in> simple_rotations \<Longrightarrow> distinct[a,b,c,d] \<Longrightarrow> (\<forall> e \<in> {a,b,c}. r f \<noteq> e) \<Longrightarrow> r f = d"
  using complex_rotations.simp distinct_map' by simp
  
lemma simple_distinct_ident: "r \<in> simple_rotations \<Longrightarrow> distinct[a,b,c,d] \<Longrightarrow> (\<forall> e \<in> {a,b,c}. r e \<noteq> e) \<Longrightarrow> r d = d"
  using simple_rotations_fix simple_distinct_map' by metis

lemma id_decomp: 
  assumes distinct:"distinct [(a::Vertex),b,c,d]" and ident:"(\<forall> x \<in> {a,b,c,d}. r x = x)"
  shows "r = id"
proof -
  from distinct_vertices have "\<forall> e. e \<in> set [a,b,c,d]" using distinct by simp
  then have "\<forall> e. r e = e" using ident by auto
  then show "r = id" by auto
qed 
 
text \<open>
Here we show that two invariants hold for rotations. Firstly, any rotation that does not fix a vertex consists
of 2-cycles. Secondly, the only rotation that fixes more than one vertex is the identity.

This proof is very long in part because both invariants have to be proved simultaneously because
they depend on each other.
\<close>    
  
lemma complex_rotations_invariants: 
  "r \<in> complex_rotations \<Longrightarrow> (((\<forall> v. r v \<noteq> v) \<longrightarrow> r v = w \<longrightarrow> r w = v) \<and> (r v = v \<longrightarrow> r w = w \<longrightarrow> v \<noteq> w \<longrightarrow> r = id)) "
proof(induction r arbitrary: v w rule: complex_rotations.induct)
  case (simp r)
  assume r:"r \<in> simple_rotations"
  show ?case
  proof 
    have "\<exists> v. r v = v" using simple_rotations_fix r by simp
    then have "\<not> (\<forall> v. r v \<noteq> v)" by simp
    then show "(\<forall> v. r v \<noteq> v) \<longrightarrow> r v = w \<longrightarrow> r w = v" by blast
        
    show "r v = v \<longrightarrow> r w = w \<longrightarrow> v \<noteq> w \<longrightarrow> r = id" using simple_rotations_fix_unique simp by blast
  qed
next
  case (comp r s)  
  assume r:"r \<in> simple_rotations"
  assume s:"s \<in> complex_rotations"
  have fix_unique:"\<forall> v w. s v = v \<longrightarrow> s w = w \<longrightarrow> v \<noteq> w \<longrightarrow> s = id" using comp by blast
  show ?case 
  proof
    show "(\<forall>x. (r \<circ> s) x \<noteq> x) \<longrightarrow> (r \<circ> s) v = w \<longrightarrow> (r \<circ> s) w = v"
    proof (rule impI)+
      assume nofixrs:"\<forall> x.(r \<circ> s) x \<noteq> x"
      assume "(r \<circ> s) v = w"
      show "(r \<circ> s) w = v"
      proof (cases "\<forall> x. s x \<noteq> x")
        assume nofixs:"\<forall> x. s x \<noteq> x"
        then have cycle:"\<forall> x y. (s x = y \<longrightarrow> s y = x)" using comp.IH by blast
        then show ?thesis
        proof (cases "r = id")
          assume id:"r = id"
          then have "s v = w" using  \<open>(r \<circ> s) v = w\<close> by simp
          then have "s w = v" using cycle by blast
          then show "(r \<circ> s) w = v" using id by simp
        next
          assume notid:"r \<noteq> id"
          obtain a where "s v = a" and "s a = v" and "a \<noteq> v" using comp.IH nofixs by blast
          obtain b where "s w = b" and "s b = w" and "b \<noteq> w" using comp.IH nofixs by blast
          have "v \<noteq> w" using \<open>(r \<circ> s) v = w\<close> nofixrs by blast    
          then have "a \<noteq> b" using comp.hyps rotation_bij_corollary \<open>s a = v\<close> \<open>s b = w\<close> by auto
          have "r a = w" using \<open>s v = a\<close> \<open>(r \<circ> s) v = w\<close> by auto 
          then show ?thesis
          proof (cases "a = w")
            assume "a = w"
            then have "r a = a" using \<open>r a = w\<close> by simp
            then have "s v = w" using \<open>a = w\<close> \<open>s v = a\<close> by simp
            then have "b = v" using \<open>s b = w\<close> rotation_bij_corollary comp.hyps by blast
            then have "s w = v" using \<open>s w = b\<close> by simp
            then have "r v \<noteq> v" using simple_rotations_fix_unique notid \<open>r a = a\<close> \<open>a \<noteq> v\<close> 
                comp.hyps(1) by auto
            obtain c d where "s c = d" and "c \<noteq> v" and "c \<noteq> w"
              using \<open>a \<noteq> v\<close> \<open>r a = w\<close> \<open>r v \<noteq> v\<close> comp.hyps(1) simple_rotation_bij_corollary by blast 
            then have "d \<noteq> v" and "d \<noteq> w"
              using \<open>s w = v\<close> \<open>c \<noteq> v\<close> \<open>s c = d\<close> \<open>s v = w\<close> comp.hyps(2) rotation_bij_corollary by auto
            then have "s d = c" using \<open>s c = d\<close> comp.IH nofixs by blast 
            then have "c \<noteq> d" using nofixs by auto
            then show ?thesis
            proof(cases "r v = c")
              assume "r v = c"
              then have "r c \<noteq> v" using \<open>c \<noteq> v\<close> simple_rotations_cycle comp.hyps(1) notid by simp
              have "r c \<noteq> w" 
                using \<open>r a = a\<close> \<open>c \<noteq> w\<close> \<open>r a = w\<close> simple_rotation_bij_corollary comp.hyps(1) by auto 
              have "r c \<noteq> c" using \<open>a = w\<close> \<open>c \<noteq> w\<close> \<open>r a = a\<close>
                comp.hyps(1) simple_rotations_fix_unique notid by blast 
              have dist:"distinct [v,w,c,d]" using \<open>c \<noteq> v\<close> \<open>c \<noteq> w\<close> \<open>c \<noteq> d\<close> \<open>d \<noteq> v\<close> \<open>d \<noteq> w\<close> \<open>v \<noteq> w\<close> by simp
              then have "\<forall> v \<in> {v,w,c}. r c \<noteq> v" using \<open>r c \<noteq> c\<close> \<open>r c \<noteq> v\<close> \<open>r c \<noteq> w\<close> by auto 
              then have "r c = d" using simple_distinct_map' comp.hyps(1) dist by auto    
              then have "(r \<circ> s) d = d" using \<open>s d = c\<close> by simp
              then have False using nofixrs by blast 
              then show ?thesis by simp
            next
              assume "r v \<noteq> c"
              then have "r v \<noteq> w" 
                using \<open>r a = a\<close> \<open>v \<noteq> w\<close> \<open>r a = w\<close> simple_rotation_bij_corollary comp.hyps(1) by auto
              then have "r v \<noteq> v" using \<open>a = w\<close> \<open>r a = a\<close>
                comp.hyps(1) simple_rotations_fix_unique notid by blast 
              have dist:"distinct [w,c,v,d]" using \<open>c \<noteq> v\<close> \<open>c \<noteq> w\<close> \<open>c \<noteq> d\<close> \<open>d \<noteq> v\<close> \<open>d \<noteq> w\<close> \<open>v \<noteq> w\<close> by simp
              then have "\<forall> x \<in> {w,c,v}. r v \<noteq> x" using \<open>r v \<noteq> c\<close> \<open>r v \<noteq> v\<close> \<open>r v \<noteq> w\<close> by auto 
              then have "r v = d" using simple_distinct_map' comp.hyps(1) dist by auto 
              then have "r d \<noteq> v" using \<open>d \<noteq> v\<close> simple_rotations_cycle comp.hyps(1) notid by simp   
              have "r d \<noteq> w"
                using \<open>r a = a\<close> \<open>d \<noteq> w\<close> \<open>r a = w\<close> simple_rotation_bij_corollary comp.hyps(1) by auto 
              have "r d \<noteq> d" using \<open>a = w\<close> \<open>d \<noteq> w\<close> \<open>r a = a\<close>
                comp.hyps(1) simple_rotations_fix_unique notid by blast 
              have dist':"distinct [w,v,d,c]" using \<open>c \<noteq> v\<close> \<open>c \<noteq> w\<close> \<open>c \<noteq> d\<close> \<open>d \<noteq> v\<close> \<open>d \<noteq> w\<close> \<open>v \<noteq> w\<close> by simp
              then have "\<forall> v \<in> {w,v,d}. r d \<noteq> v" using \<open>r d \<noteq> d\<close> \<open>r d \<noteq> w\<close> \<open>r d \<noteq> v\<close> by auto 
              then have "r d = c" using simple_distinct_map' comp.hyps(1) dist' by auto 
              then have "(r \<circ> s) c = c" using \<open>s c = d\<close> by simp
              then have False using nofixrs by blast 
              then show ?thesis by simp
            qed
          next
            assume "a \<noteq> w"
            then have "r a \<noteq> a" using \<open>r a = w\<close> by simp
            have "b \<noteq> v" using \<open>a \<noteq> w\<close> \<open>s b = w\<close> \<open>s v = a\<close> by auto 
            have "r w \<noteq> w" using \<open>a \<noteq> w\<close> \<open>r a = w\<close> comp.hyps(1) simple_rotation_bij_corollary by auto
            from nofixs have "s w \<noteq> w" by simp
            then have "r v \<noteq> w" using \<open>a \<noteq> v\<close> \<open>r a = w\<close> comp.hyps simple_rotation_bij_corollary by blast   
            have "s v \<noteq> w" using \<open>r a = w\<close> \<open>r a \<noteq> a\<close> \<open>s v = a\<close> by blast 
            then show ?thesis
            proof (cases "r b = b")
              assume "r b = b"
              then have "r b \<noteq> a" using \<open>a \<noteq> b\<close> by simp
              have "r w \<noteq> a" using \<open>r a = w\<close> \<open>r w \<noteq> w\<close> comp.hyps(1) notid simple_rotations_cycle by blast 
              have dist:"distinct [a,b,w,v]" using \<open>a \<noteq> w\<close> \<open>a \<noteq> b\<close> \<open>a \<noteq> v\<close> \<open>b \<noteq> w\<close> \<open>b \<noteq> v\<close> \<open>v \<noteq> w\<close> by simp
              then have "\<forall> x \<in> {a,b,w}. r x \<noteq> a" using \<open>r a \<noteq> a\<close> \<open>r b \<noteq> a\<close> \<open>r w \<noteq> a\<close> by auto 
              then have "r v = a" using simple_distinct_map comp.hyps(1) dist by auto 
              then show ?thesis using \<open>s a = v\<close> nofixrs comp_apply by metis
            next
              assume "r b \<noteq> b"
              have dist:"distinct [w,a,b,v]" using \<open>a \<noteq> w\<close> \<open>a \<noteq> b\<close> \<open>a \<noteq> v\<close> \<open>b \<noteq> w\<close> \<open>b \<noteq> v\<close> \<open>v \<noteq> w\<close> by simp
              then have "\<forall> x \<in> {w,a,b}. r x \<noteq> x" using \<open>r w \<noteq> w\<close> \<open>r a \<noteq> a\<close> \<open>r b \<noteq> b\<close> by auto 
              then have "r v = v" using simple_distinct_ident comp.hyps(1) dist by auto 
              have "r w \<noteq> a" using \<open>a \<noteq> w\<close> simple_rotations_cycle comp.hyps(1) notid \<open>r a = w\<close> by simp
              have "r w \<noteq> v" using \<open>r v = v\<close> \<open>v \<noteq> w\<close> comp.hyps(1) simple_rotation_bij_corollary by blast 
              have dist':"distinct [a,v,w,b]" using \<open>a \<noteq> w\<close> \<open>a \<noteq> b\<close> \<open>a \<noteq> v\<close> \<open>b \<noteq> w\<close> \<open>b \<noteq> v\<close> \<open>v \<noteq> w\<close> by simp
              then have "\<forall> x \<in> {a,v,w}. r w \<noteq> x" using \<open>r w \<noteq> a\<close> \<open>r w \<noteq> v\<close> \<open>r w \<noteq> w\<close> by auto 
              then have "r w = b" using simple_distinct_map' comp.hyps(1) dist' by auto
              then show ?thesis using \<open>s b = w\<close> nofixrs comp_apply by metis
            qed
          qed
        qed        
    next
      assume "\<not> (\<forall> v. s v \<noteq> v)"
      then have fix1:"\<exists> v. s v = v" by blast
      then obtain a where a:"s a = a" by blast
      then show ?thesis
      proof (cases "r = id")
        assume id:"r = id"
        then have "(r \<circ> s) a = a" using a by simp
        then have False using nofixrs by auto
        then show ?thesis by simp
      next
        assume notid: "r \<noteq> id"
        then have fix1:"\<exists> v. r v = v" using simple_rotations_fix comp.hyps by simp
        then obtain b where b:"r b = b" by blast
        then show ?thesis
        proof (cases "a = b")
          assume "a = b"
          then have "(r \<circ> s) a = a" using a b by simp
          then have False using nofixrs by blast
          then show ?thesis by simp
        next
          assume "a \<noteq> b"
          have "r a \<noteq> a" using \<open>a \<noteq> b\<close> b comp.hyps(1) notid simple_rotations_fix_unique by blast 
          have "r a \<noteq> b" using \<open>a \<noteq> b\<close> b comp.hyps(1) simple_rotation_bij_corollary by auto 
          then obtain c where "r a = c" and "a \<noteq> c" and "b \<noteq> c" using \<open>r a \<noteq> a\<close> by auto
          have "s b \<noteq> a" using \<open>a \<noteq> b\<close> a comp.hyps(2) rotation_bij_corollary by blast 
          have "s b \<noteq> b" using b nofixrs comp_apply by metis
          then obtain d where "s b = d" and "a \<noteq> d" and "b \<noteq> d" using \<open>s b \<noteq> a\<close> by auto
          have "r c \<noteq> a" using simple_rotations_cycle \<open>a \<noteq> c\<close> \<open>r a = c\<close> comp.hyps(1) notid by blast
          have "r c \<noteq> b" using \<open>b \<noteq> c\<close> b comp.hyps(1) simple_rotation_bij_corollary by blast 
          have "r c \<noteq> c" using \<open>b \<noteq> c\<close> b comp.hyps(1) notid simple_rotations_fix_unique by blast
          then show ?thesis
          proof (cases "c = d")
            assume "c = d"
            then have "s c \<noteq> c" using \<open>b \<noteq> c\<close> \<open>s b = d\<close> rotation_bij_corollary s by auto
            obtain e where "r c = e" and "a \<noteq> e" and "b \<noteq> e" and "c \<noteq> e" and "d \<noteq> e" 
              using \<open>r c \<noteq> a\<close> \<open>r c \<noteq> b\<close> \<open>r c \<noteq> c\<close> \<open>c = d\<close> by auto
            have "r e \<noteq> b" using \<open>b \<noteq> e\<close> b r simple_rotation_bij_corollary by blast 
            have "r e \<noteq> c" using \<open>a \<noteq> e\<close> \<open>r a = c\<close> r simple_rotation_bij_corollary by blast 
            have "r e \<noteq> e" using \<open>b \<noteq> e\<close> b notid r simple_rotations_fix_unique by blast                
            then have dist:"distinct [b,c,e,a]" using \<open>a \<noteq> b\<close> \<open>a \<noteq> c\<close> \<open>a \<noteq> e\<close> \<open>b \<noteq> c\<close> \<open>b \<noteq> e\<close> \<open>c \<noteq> e\<close> by simp
            then have "\<forall> x \<in> {b,c,e}. r e \<noteq> x" using \<open>r e \<noteq> b\<close> \<open>r e \<noteq> c\<close> \<open>r e \<noteq> e\<close> by auto 
            then have "r e = a" using simple_distinct_map' comp.hyps(1) dist by auto               
            have dist:"distinct [a,b,c,e]" using \<open>a \<noteq> b\<close> \<open>a \<noteq> c\<close> \<open>a \<noteq> e\<close> \<open>b \<noteq> c\<close> \<open>b \<noteq> e\<close> \<open>c \<noteq> e\<close> by simp
            then have "\<forall> x \<in> {a,b,c}. r c \<noteq> x" using \<open>r c \<noteq> a\<close> \<open>r c \<noteq> b\<close> \<open>r c \<noteq> c\<close> by auto 
            then have "r c = e" using simple_distinct_map' comp.hyps(1) dist by auto  
            have "s e \<noteq> a" using \<open>a \<noteq> e\<close> a rotation_bij_corollary s by blast 
            have "s e \<noteq> c" using \<open>b \<noteq> e\<close> \<open>c = d\<close> \<open>s b = d\<close> rotation_bij_corollary s by blast 
            have "s e \<noteq> e" using \<open>a \<noteq> e\<close> \<open>s b \<noteq> b\<close> a fix_unique by fastforce                
            then have dist:"distinct [a,c,e,b]" using \<open>a \<noteq> b\<close> \<open>a \<noteq> c\<close> \<open>a \<noteq> e\<close> \<open>b \<noteq> c\<close> \<open>b \<noteq> e\<close> \<open>c \<noteq> e\<close> by simp
            then have "\<forall> x \<in> {a,c,e}. s e \<noteq> x" using \<open>s e \<noteq> a\<close> \<open>s e \<noteq> c\<close> \<open>s e \<noteq> e\<close> by auto 
            then have "s e = b" using distinct_map' comp.hyps(2) dist by auto
            have "s c \<noteq> a" using \<open>a \<noteq> c\<close> a rotation_bij_corollary s by blast 
            have "s c \<noteq> b" using \<open>c \<noteq> e\<close> \<open>s e = b\<close> rotation_bij_corollary s by blast        
            then have dist:"distinct [a,b,c,e]" using \<open>a \<noteq> b\<close> \<open>a \<noteq> c\<close> \<open>a \<noteq> e\<close> \<open>b \<noteq> c\<close> \<open>b \<noteq> e\<close> \<open>c \<noteq> e\<close> by simp
            then have "\<forall> x \<in> {a,b,c}. s c \<noteq> x" using \<open>s c \<noteq> a\<close> \<open>s c \<noteq> b\<close> \<open>s c \<noteq> c\<close> by auto 
            then have "s c = e" using distinct_map' comp.hyps(2) dist by auto    
            
            have rsa:"(r \<circ> s) a = c" using  \<open>r a = c\<close> a by simp 
            have rsb:"(r \<circ> s) b = e" using \<open>c = d\<close> \<open>r c = e\<close> \<open>s b = d\<close> by auto    
            have rsc:"(r \<circ> s) c = a" using \<open>r e = a\<close> \<open>s c = e\<close> by auto 
            have rse:"(r \<circ> s) e = b" using \<open>s e = b\<close> b by simp
            then have dist:"distinct [a,c,b,e]" using \<open>a \<noteq> b\<close> \<open>a \<noteq> c\<close> \<open>a \<noteq> e\<close> \<open>b \<noteq> c\<close> \<open>b \<noteq> e\<close> \<open>c \<noteq> e\<close> by simp   
            have comprs:"r \<circ> s \<in> complex_rotations" using complex_rotations.comp r s by simp
            show ?thesis using cycle_map[OF comprs dist rsa rsc rsb rse] \<open>(r \<circ> s) v = w\<close> by blast            
          next
            assume "c \<noteq> d"
            then have dist:"distinct [a,b,c,d]" using \<open>a \<noteq> b\<close> \<open>a \<noteq> c\<close> \<open>a \<noteq> d\<close> \<open>b \<noteq> c\<close> \<open>b \<noteq> d\<close> \<open>c \<noteq> d\<close> by simp
            then have "\<forall> x \<in> {a,b,c}. r c \<noteq> x" using \<open>r c \<noteq> a\<close> \<open>r c \<noteq> b\<close> \<open>r c \<noteq> c\<close> by auto 
            then have "r c = d" using simple_distinct_map' comp.hyps(1) dist by auto 
            have "r d \<noteq> b" using \<open>b \<noteq> d\<close> b comp.hyps(1) simple_rotation_bij_corollary by blast  
            have "r d \<noteq> c" using \<open>c \<noteq> d\<close> \<open>r c = d\<close> comp.hyps(1) notid simple_rotations_cycle by blast 
            have "r d \<noteq> d" using \<open>c \<noteq> d\<close> \<open>r c = d\<close> comp.hyps(1) simple_rotation_bij_corollary by auto 
            have dist:"distinct [b,c,d,a]" using \<open>a \<noteq> b\<close> \<open>a \<noteq> c\<close> \<open>a \<noteq> d\<close> \<open>b \<noteq> c\<close> \<open>b \<noteq> d\<close> \<open>c \<noteq> d\<close> by simp
            then have "\<forall> x \<in> {b,c,d}. r d \<noteq> x" using \<open>r d \<noteq> b\<close> \<open>r d \<noteq> c\<close> \<open>r d \<noteq> d\<close> by auto 
            then have "r d = a" using simple_distinct_map' comp.hyps(1) dist by auto         
            have "s d \<noteq> a" using \<open>a \<noteq> d\<close> a comp.hyps(2) rotation_bij_corollary by blast 
            have "s d \<noteq> c" using nofixrs \<open>r c = d\<close> \<open>c \<noteq> d\<close> comp_apply by metis
            have "s d \<noteq> d" using \<open>b \<noteq> d\<close> \<open>s b = d\<close> comp.hyps(2) rotation_bij_corollary by auto 
            have dist:"distinct [a,c,d,b]" using \<open>a \<noteq> b\<close> \<open>a \<noteq> c\<close> \<open>a \<noteq> d\<close> \<open>b \<noteq> c\<close> \<open>b \<noteq> d\<close> \<open>c \<noteq> d\<close> by simp
            then have "\<forall> x \<in> {a,c,d}. s d \<noteq> x" using \<open>s d \<noteq> a\<close> \<open>s d \<noteq> c\<close> \<open>s d \<noteq> d\<close> by auto 
            then have "s d = b" using distinct_map' comp.hyps(2) dist by auto 
            have "s c \<noteq> a" using \<open>a \<noteq> c\<close> a comp.hyps(2) rotation_bij_corollary by blast 
            have "s c \<noteq> b" using \<open>c \<noteq> d\<close> \<open>s d = b\<close> comp.hyps(2) rotation_bij_corollary by blast 
            have "s c \<noteq> d" using \<open>b \<noteq> c\<close> \<open>s b = d\<close> comp.hyps(2) rotation_bij_corollary by blast  
            have dist:"distinct [a,b,d,c]" using \<open>a \<noteq> b\<close> \<open>a \<noteq> c\<close> \<open>a \<noteq> d\<close> \<open>b \<noteq> c\<close> \<open>b \<noteq> d\<close> \<open>c \<noteq> d\<close> by simp
            then have "\<forall> x \<in> {a,b,d}. s c \<noteq> x" using \<open>s c \<noteq> a\<close> \<open>s c \<noteq> b\<close> \<open>s c \<noteq> d\<close> by auto 
            then have "s c = c" using distinct_map' comp.hyps(2) dist by auto 
            then have False using fix_unique \<open>s d \<noteq> d\<close> \<open>a \<noteq> c\<close> a by fastforce 
            then show ?thesis by simp
          qed
        qed
      qed
    qed
  qed
next
  show "(r \<circ> s) v = v \<longrightarrow> (r \<circ> s) w = w \<longrightarrow> v \<noteq> w \<longrightarrow> r \<circ> s = id"
  proof(rule impI)+
    assume rsv:"(r \<circ> s) v = v" and rsw:"(r \<circ> s) w = w" and "v \<noteq> w"
    show "r \<circ> s = id"
    proof(cases "s = id")
      assume sid:"s = id"
      then have "s v = v" and "s w = w" by auto
      then have "r = id" using simple_rotations_fix_unique rsv rsw \<open>v \<noteq> w\<close> r  by auto
      with sid show ?thesis by simp
    next
      assume snotid:"s \<noteq> id"
      then show ?thesis
      proof(cases "r = id")
        assume rid:"r = id"
        then have "s v = v" and "s w = w" using rsv rsw by auto
        then have "s = id" using \<open>v \<noteq> w\<close> fix_unique by blast 
        with rid show ?thesis by simp
      next
        assume rnotid:"r \<noteq> id"
        from simple_rotations_fix_unique[OF comp.hyps(1) rnotid] have 
          r_fix_forall:"\<forall>v w. r v = v \<and> r w = w \<longrightarrow> v = w" by blast
        from comp.IH snotid have
          s_fix_forall:"\<forall>v w. s v = v \<and> s w = w \<longrightarrow> v = w" by blast
        have fixes_two: "\<exists>a b. (r \<circ> s) a = a \<and> (r \<circ> s) b = b \<and> a \<noteq> b" using \<open>v \<noteq> w\<close> rsv rsw by blast 
        then show ?thesis
        proof (cases "\<forall> x. s x \<noteq> x")
          assume sfix':"\<forall> x. s x \<noteq> x"  
          from simple_rotations_fix obtain a where a:"r a = a" using r by blast
          from sfix' have "s a \<noteq> a" by blast
          then have "(r \<circ> s) a \<noteq> a" using a simple_rotation_bij_corollary r by fastforce
          with fixes_two obtain b where "(r \<circ> s) b = b" and "b \<noteq> a" by blast
          with fixes_two obtain c where "(r \<circ> s) c = c" and "c \<noteq> a" and "c \<noteq> b" 
            using \<open>(r \<circ> s) a \<noteq> a\<close> by blast
        
          have "s b \<noteq> a" using a \<open>(r \<circ> s) b = b\<close> sfix' by force
          have "s c \<noteq> a" using a \<open>(r \<circ> s) c = c\<close> sfix' by force
        
          then obtain d where "s d = a" and "d \<noteq> a" and "d \<noteq> b" and "d \<noteq> c"
            using \<open>s a \<noteq> a\<close> \<open>s b \<noteq> a\<close> \<open>s c \<noteq> a\<close> complex_rotations_bij s bij_pointE by metis
          have "(r \<circ> s) d = a" using a \<open>s d = a\<close> by simp
        
          have "r b \<noteq> a" using a r simple_rotation_bij_corollary \<open>b \<noteq> a\<close> by auto 
          have "r c \<noteq> a" using a r simple_rotation_bij_corollary \<open>c \<noteq> a\<close> by auto
          have "r d \<noteq> a" using a r simple_rotation_bij_corollary \<open>d \<noteq> a\<close> by auto  
          have "r b \<noteq> b" using a r simple_rotations_fix_unique rnotid \<open>b \<noteq> a\<close> by blast
          have "r c \<noteq> c" using a r simple_rotations_fix_unique rnotid \<open>c \<noteq> a\<close> by blast
          have "r d \<noteq> d" using a r simple_rotations_fix_unique rnotid \<open>d \<noteq> a\<close> by blast
        
          then have False using sfix'
          proof (cases "r b = c")
            assume "r b = c"
            then have "r c \<noteq> c" using r simple_rotation_bij_corollary \<open>c \<noteq> b\<close> by auto
            then have "r c \<noteq> b" using r rnotid simple_rotations_cycle \<open>r b = c\<close> by auto
            have dist:"distinct [a,b,c,d]" using \<open>c \<noteq> a\<close> \<open>d \<noteq> a\<close> \<open>d \<noteq> c\<close> \<open>d \<noteq> b\<close> \<open>c \<noteq> b\<close> \<open>b \<noteq> a\<close> by simp
            then have "\<forall> v \<in> {a,b,c}. r c \<noteq> v" using \<open>r c \<noteq> c\<close> \<open>r c \<noteq> a\<close> \<open>r c \<noteq> b\<close> by auto 
            then have "r c = d" using simple_distinct_map' r dist by auto
        
            have "r d \<noteq> c" using r simple_rotation_bij_corollary \<open>d \<noteq> b\<close> \<open>r b = c\<close> by auto
            have "r d \<noteq> d" using r a \<open>d \<noteq> a\<close> \<open>r d \<noteq> d\<close> by simp 
            have dist':"distinct [a,c,d,b]" using \<open>c \<noteq> a\<close> \<open>d \<noteq> a\<close> \<open>d \<noteq> c\<close> \<open>d \<noteq> b\<close> \<open>c \<noteq> b\<close> \<open>b \<noteq> a\<close> by simp
            then have "\<forall> v \<in> {a,c,d}. r d \<noteq> v" using \<open>r d \<noteq> c\<close> \<open>r d \<noteq> a\<close> \<open>r d \<noteq> d\<close> by auto 
            then have "r d = b" using simple_distinct_map' r dist' by auto
        
            then have "s b = d" using \<open>(r \<circ> s) b = b\<close> r simple_rotation_bij_corollary by auto 
            have "s c = b" using \<open>(r \<circ> s) c = c\<close> \<open>r b = c\<close> r simple_rotation_bij_corollary by auto 
            
            then have "s b \<noteq> c" using \<open>s b = d\<close> \<open>d \<noteq> c\<close> by simp
            then show False using s sfix' \<open>s c = b\<close> comp(3) by blast
          next
            assume "r b \<noteq> c"
            have dist':"distinct [a,b,c,d]" using \<open>c \<noteq> a\<close> \<open>d \<noteq> a\<close> \<open>d \<noteq> c\<close> \<open>d \<noteq> b\<close> \<open>c \<noteq> b\<close> \<open>b \<noteq> a\<close> by simp
            then have "\<forall> v \<in> {a,b,c}. r b \<noteq> v" using \<open>r b \<noteq> a\<close> \<open>r b \<noteq> b\<close> \<open>r b \<noteq> c\<close> by auto 
            then have "r b = d" using simple_distinct_map' r dist' by auto
            
            then have "r c \<noteq> d" using r simple_rotation_bij_corollary \<open>c \<noteq> b\<close> by auto
            have dist'':"distinct [a,c,d,b]" using \<open>c \<noteq> a\<close> \<open>d \<noteq> a\<close> \<open>d \<noteq> c\<close> \<open>d \<noteq> b\<close> \<open>c \<noteq> b\<close> \<open>b \<noteq> a\<close> by simp
            then have "\<forall> v \<in> {a,c,d}. r c \<noteq> v" using \<open>r c \<noteq> a\<close> \<open>r c \<noteq> c\<close> \<open>r c \<noteq> d\<close> by auto 
            then have "r c = b" using simple_distinct_map' r dist'' by auto
        
            then have "r d \<noteq> b" using r simple_rotation_bij_corollary \<open>d \<noteq> c\<close> by auto
            have dist''':"distinct [a,b,d,c]" using \<open>c \<noteq> a\<close> \<open>d \<noteq> a\<close> \<open>d \<noteq> c\<close> \<open>d \<noteq> b\<close> \<open>c \<noteq> b\<close> \<open>b \<noteq> a\<close> by simp
            then have "\<forall> v \<in> {a,b,d}. r d \<noteq> v" using \<open>r d \<noteq> a\<close> \<open>r d \<noteq> b\<close> \<open>r d \<noteq> d\<close> by auto 
            then have "r d = c" using simple_distinct_map' r dist''' by auto
        
            then have "s b = c" using \<open>r c = b\<close> \<open>(r \<circ> s) b = b\<close> r simple_rotation_bij_corollary by auto 
            have "s c = d" using \<open>(r \<circ> s) c = c\<close> \<open>r d = c\<close> r simple_rotation_bij_corollary by auto 
            
            then have "s c \<noteq> b" using \<open>d \<noteq> b\<close> by simp
            then have False using comp(3) s sfix' \<open>s b = c\<close> by blast
            then show ?thesis by simp
          qed
          then show ?thesis by simp
        next
          assume "\<not> (\<forall> x. s x \<noteq> x)" 
          then have "\<exists> x. s x = x" by simp
          then obtain a where a:"s a = a" by blast
          from simple_rotations_fix obtain b where b:"r b = b" using r by blast
          then show ?thesis
          proof (cases "a = b")
            assume "a \<noteq> b"
            with a b have "r a \<noteq> a" using r rnotid simple_rotations_fix_unique by blast 
            then have "(r \<circ> s) a \<noteq> a" using a by simp
            have "s b \<noteq> b" using a \<open>a \<noteq> b\<close> s_fix_forall by blast 
            then have "(r \<circ> s) b \<noteq> b" using b simple_rotations_inj r 
                complex_rotations.simp rotation_bij_corollary by fastforce  
            with fixes_two obtain c where "(r \<circ> s) c = c" and "c \<noteq> a" and "c \<noteq> b" using \<open>(r \<circ> s) a \<noteq> a\<close> by blast
            from fixes_two obtain d where "(r \<circ> s) d = d" and "d \<noteq> a" and "d \<noteq> b" and "d \<noteq> c" 
              using \<open>(r \<circ> s) a \<noteq> a\<close> \<open>(r \<circ> s) b \<noteq> b\<close> by blast
        
            have "s c \<noteq> a" using a \<open>c \<noteq> a\<close> rotation_bij_corollary s by force
            have "s d \<noteq> a" using a \<open>d \<noteq> a\<close> rotation_bij_corollary s by force
            
            have "r a \<noteq> c" using \<open>s c \<noteq> a\<close> \<open>(r \<circ> s) c = c\<close> \<open>c \<noteq> a\<close> r simple_rotation_bij_corollary by auto
            have "r a \<noteq> d" using \<open>s d \<noteq> a\<close> \<open>(r \<circ> s) d = d\<close> \<open>d \<noteq> a\<close> r simple_rotation_bij_corollary by auto
            have "r a \<noteq> b" using b simple_rotation_bij_corollary \<open>a \<noteq> b\<close> r by auto    
        
            have dist:"distinct [b,c,d,a]" using \<open>c \<noteq> a\<close> \<open>d \<noteq> a\<close> \<open>c \<noteq> b\<close> \<open>a \<noteq> b\<close> \<open>d \<noteq> c\<close> \<open>d \<noteq> b\<close> by simp
            then have "\<forall> v \<in> {b,c,d}. r a \<noteq> v" using \<open>r a \<noteq> b\<close> \<open>r a \<noteq> c\<close> \<open>r a \<noteq> d\<close> by auto 
            then have "r a = a" using simple_distinct_map' r dist by simp
            then have False using \<open>r a \<noteq> a\<close> by simp
            then show ?thesis by simp
          next
            assume "a = b"
            with a b have "(r \<circ> s) a = a" by simp
            from fixes_two obtain c where rsc:"(r \<circ> s) c = c" and "c \<noteq> a" by blast
            then have "r c \<noteq> c" using b \<open>a = b\<close>r rnotid simple_rotations_fix_unique by blast 
            then have "s c \<noteq> c" using rsc by auto
            then obtain d where "s c = d" and "d \<noteq> c" by blast
            then have "d \<noteq> a" using a s rotation_bij_corollary by blast
            have "s d \<noteq> d" using a using \<open>d \<noteq> a\<close> s_fix_forall by blast 
            have "r d = c" using rsc \<open>s c = d\<close> by simp
            then have "r c \<noteq> d" using \<open>d \<noteq> c\<close> simple_rotations_cycle r rnotid by auto
            then obtain e where "r c = e" and "e \<noteq> d" by blast
            then have "e \<noteq> a" using b \<open>a = b\<close> simple_rotation_bij_corollary \<open>c \<noteq> a\<close> r by auto 
            then have "e \<noteq> c" using b \<open>a = b\<close> \<open>r c = e\<close> \<open>r c \<noteq> c\<close> by blast  
            then have "r e \<noteq> c" using \<open>r c = e\<close> simple_rotations_cycle r rnotid by auto
            have "r e \<noteq> a" using b \<open>a = b\<close> \<open>e \<noteq> a\<close> simple_rotation_bij_corollary r by auto
            then have "r e \<noteq> e" using \<open>e \<noteq> c\<close> \<open>r c = e\<close> r simple_rotation_bij_corollary by blast 
            have dist:"distinct [a,c,d,e]" using \<open>c \<noteq> a\<close> \<open>d \<noteq> a\<close> \<open>d \<noteq> c\<close> \<open>e \<noteq> a\<close> \<open>e \<noteq> c\<close> \<open>e \<noteq> d\<close> by simp
            then have "\<forall> v \<in> {a,c,d}. r v \<noteq> d" using \<open>r b = b\<close> \<open>a = b\<close> \<open>r d = c\<close> \<open>r c = e\<close> by auto 
            then have "r e = d" using simple_distinct_map r dist by auto
            
            have dist':"distinct [a,c,e,d]" using dist by auto
            have "s e \<noteq> e" using  \<open>e \<noteq> a\<close> a s_fix_forall by blast 
            then have "\<forall> v \<in> {a,c,e}. s v \<noteq> e" using \<open>s a = a\<close> \<open>s c = d\<close> dist by auto
            then have "s d = e" using distinct_map s dist' by auto           
            then have "\<forall> v \<in> {a,c,d}. s v \<noteq> c" using \<open>s a = a \<close> \<open>s c = d\<close> dist by auto
            then have "s e = c" using distinct_map s dist by auto          
            then have "(r \<circ> s) d = d" using \<open>s d = e\<close> \<open>r e = d\<close> by auto
            then have "(r \<circ> s) e = e" using \<open>s e = c\<close> \<open>r c = e\<close> by auto
            then show "(r \<circ> s) = id" using \<open>(r \<circ> s) d = d\<close>  \<open>(r \<circ> s) a = a\<close> \<open>(r \<circ> s) c = c\<close> dist id_decomp by auto
            qed    
          qed
        qed
      qed
    qed     
  qed
qed
  
text \<open>
  This lemma is a simple corollary of the previous result. It is the main result necessary to 
  count stabilisers.
\<close>  

corollary complex_rotations_fix: "r \<in> complex_rotations \<Longrightarrow> r a = a \<Longrightarrow> r b = b \<Longrightarrow> a \<noteq> b \<Longrightarrow> r = id"
  using complex_rotations_invariants by blast

section "Inversions"
text \<open>
  In this section we show that inverses exist for each rotation, which we will need to show that
  the rotations we defined indeed form a group.
\<close>

lemma simple_rotations_rotate_id:
  assumes r:"r \<in> simple_rotations"
  shows "r \<circ> r \<circ> r = id"  
  using r unfolding simple_rotations_def
  by safe
     (rule ext; rename_tac a; case_tac a;
      simp add: simple_rotations
     )+

lemma simple_rotations_inverses:
  assumes r:"r \<in> simple_rotations"
  shows "\<exists>y\<in>complex_rotations. y \<circ> r = id"
proof
  let ?y = "r \<circ> r"
  from r show y:"?y \<in> complex_rotations" using complex_rotations.intros by simp
  from simple_rotations_rotate_id show "?y \<circ> r = id" using r by auto 
qed  

lemma complex_rotations_inverses:
  "r \<in> complex_rotations \<Longrightarrow> \<exists>y\<in>complex_rotations. y \<circ> r = id"
proof (induction r rule: complex_rotations.induct)
  case (simp r) then show ?case using simple_rotations_inverses by blast
next
  case (comp r s)
  obtain r' where r'_comp:"r'\<in>complex_rotations" and r'_inv:"r' \<circ> r = id" 
    using simple_rotations_inverses comp.hyps  by auto
  obtain y where y_comp:"y\<in>complex_rotations" and y_inv:"y \<circ> s = id" using comp.IH by blast
  from complex_rotations_comp have yr':"y \<circ> r' \<in> complex_rotations" using r'_comp y_comp by simp
  have "r' \<circ> (r \<circ> s) = r' \<circ> r \<circ> s" using comp_assoc by metis
  then have "r' \<circ> (r \<circ> s) = s" using r'_inv by simp
  then have "y \<circ> r' \<circ> (r \<circ> s) = id" using y_inv comp_assoc by metis
  then show ?case using yr' by metis
qed

section "The Tetrahedral Group"

text \<open>
We can now define the group of rotational symmetries of a tetrahedron. Since we modeled rotations
as functions, the group operation is functional composition and the identity element of the group is
the identity function
\<close>

definition tetrahedral_group :: "Rotation monoid" where
  "tetrahedral_group = \<lparr>carrier = complex_rotations, mult = (\<circ>), one = id\<rparr>"

text \<open>
We now prove that this indeed forms a group. Most of the subgoals are trivial, the last goal uses
our results from the previous section about inverses.
\<close>

lemma is_tetrahedral_group: "group tetrahedral_group"
proof(rule groupI)
  show "\<one>\<^bsub>tetrahedral_group\<^esub> \<in> carrier tetrahedral_group"
    by (simp add: complex_rotations.intros(1) simple_rotations_def tetrahedral_group_def)
next
  fix x
  assume "x \<in> carrier tetrahedral_group"
  show "\<one>\<^bsub>tetrahedral_group\<^esub> \<otimes>\<^bsub>tetrahedral_group\<^esub> x = x"
    unfolding id_comp tetrahedral_group_def monoid.select_convs(1) monoid.select_convs(2) ..
next
  fix x y z
  assume "x \<in> carrier tetrahedral_group" and
    "y \<in> carrier tetrahedral_group" and
    "z \<in> carrier tetrahedral_group"
  then show "x \<otimes>\<^bsub>tetrahedral_group\<^esub> y \<otimes>\<^bsub>tetrahedral_group\<^esub> z =
             x \<otimes>\<^bsub>tetrahedral_group\<^esub> (y \<otimes>\<^bsub>tetrahedral_group\<^esub> z)"
    unfolding tetrahedral_group_def monoid.select_convs(1) by auto 
next
  fix x y
  assume "x \<in> carrier tetrahedral_group" and
    "y \<in> carrier tetrahedral_group"
  then show "x \<otimes>\<^bsub>tetrahedral_group\<^esub> y \<in> carrier tetrahedral_group"
    by (simp add: complex_rotations.intros(2) tetrahedral_group_def complex_rotations_comp)
next
  fix x
  assume "x \<in> carrier tetrahedral_group"
  then show "\<exists>y\<in>carrier tetrahedral_group.
            y \<otimes>\<^bsub>tetrahedral_group\<^esub> x = \<one>\<^bsub>tetrahedral_group\<^esub>"
    using complex_rotations_inverses by (simp add: tetrahedral_group_def)
qed

text \<open>
Having proved that our definition forms a group we can now instantiate our orbit-stabiliser locale.
The group action is the application of a rotation.
\<close>

fun apply_rotation :: "Rotation \<Rightarrow> Vertex \<Rightarrow> Vertex" where "apply_rotation r v = r v"

interpretation tetrahedral: orbit_stabiliser "tetrahedral_group" "apply_rotation :: Rotation \<Rightarrow> Vertex \<Rightarrow> Vertex"
proof intro_locales
  show "Group.monoid tetrahedral_group" using is_tetrahedral_group by (simp add: group.is_monoid)
  show "group_axioms tetrahedral_group" using is_tetrahedral_group by (simp add: group_def)
  show "orbit_stabiliser_axioms tetrahedral_group apply_rotation"
  proof
    fix x
    show "apply_rotation \<one>\<^bsub>tetrahedral_group\<^esub> x = x" by (simp add: tetrahedral_group_def)
  next
    fix g h x
    show "g \<in> carrier tetrahedral_group \<and> h \<in> carrier tetrahedral_group
           \<longrightarrow> apply_rotation g (apply_rotation h x) = apply_rotation (g \<otimes>\<^bsub>tetrahedral_group\<^esub> h) x"
      by (simp add: tetrahedral_group_def)
  qed
qed

section "Counting Orbits"
text \<open>
We now prove that there is an orbit for each vertex. That is, the group action is transitive.
\<close>
lemma orbit_is_transitive: "tetrahedral.orbit A = vertices"
proof
  show "tetrahedral.orbit A \<subseteq> vertices" unfolding vertices_def using Vertex.exhaust by blast 
  have "id \<in> complex_rotations" using complex_rotations.intros simple_rotations_def by auto
  then have "id \<in> carrier tetrahedral_group" 
    unfolding tetrahedral_group_def partial_object.select_convs(1).
  moreover have "apply_rotation id A = A" by simp
  ultimately have A:"A \<in> (tetrahedral.orbit A)"
    using tetrahedral.orbit_def mem_Collect_eq by fastforce

  have "rotate_C \<in> simple_rotations"
    using simple_rotations_def insert_subset subset_insertI by blast
  then have "rotate_C \<in> complex_rotations" using complex_rotations.intros(1) by simp
  then have "rotate_C \<in> carrier tetrahedral_group"
    unfolding tetrahedral_group_def partial_object.select_convs(1).
  moreover have "apply_rotation rotate_C A = B" by (simp add: rotate_C_def)
  ultimately have B:"B \<in> (tetrahedral.orbit A)"
    using tetrahedral.orbit_def mem_Collect_eq by fastforce

  have "rotate_D \<in> simple_rotations"
    using simple_rotations_def insert_subset subset_insertI by blast
  then have "rotate_D \<in> complex_rotations" using complex_rotations.intros(1) by simp
  then have "rotate_D \<in> carrier tetrahedral_group"
    unfolding tetrahedral_group_def partial_object.select_convs(1).
  moreover have "apply_rotation rotate_D A = C" by (simp add: rotate_D_def)
  ultimately have C:"C \<in> (tetrahedral.orbit A)"
    using tetrahedral.orbit_def mem_Collect_eq by fastforce

  have "rotate_B \<in> simple_rotations"
    using simple_rotations_def insert_subset subset_insertI by blast
  then have "rotate_B \<in> complex_rotations" using complex_rotations.intros(1) by simp
  then have "rotate_B \<in> carrier tetrahedral_group"
    unfolding tetrahedral_group_def partial_object.select_convs(1).
  moreover have "apply_rotation rotate_B A = D" by (simp add: rotate_B_def)
  ultimately have D:"D \<in> (tetrahedral.orbit A)"
    using tetrahedral.orbit_def mem_Collect_eq by fastforce

  from A B C D show "vertices \<subseteq> tetrahedral.orbit A" by (simp add: vertices_def subsetI)
qed

text \<open>
It follows from the previous lemma, that the cardinality of the set of orbits for a particular vertex is 4.
\<close>
lemma card_orbit: "card (tetrahedral.orbit A) = 4"
proof -
  from card_empty card_insert_if have "card vertices = 4" unfolding vertices_def by auto
  with orbit_is_transitive show "card (tetrahedral.orbit A) = 4" by simp
qed

section "Counting Stabilisers"

text \<open>
Each vertex has three elements in its stabiliser - the identity, a rotation around its axis by 120 degrees,
and a rotation around its axis by 240 degrees. We will prove this next.
\<close>
definition stabiliser_A :: "Rotation set" where
  "stabiliser_A = {id, rotate_A, rotate_A \<circ> rotate_A}"

text \<open>
This lemma shows that our conjectured stabiliser is correct.
\<close>
lemma is_stabiliser: "tetrahedral.stabiliser A = stabiliser_A"
proof
  show "stabiliser_A \<subseteq> tetrahedral.stabiliser A"
  proof -
    have "id \<in> complex_rotations" using complex_rotations.intros simple_rotations_def by auto
    then have "id \<in> carrier tetrahedral_group"
      unfolding tetrahedral_group_def partial_object.select_convs(1) by simp
    moreover have "apply_rotation id A = A" by simp
    ultimately have id:"id \<in> (tetrahedral.stabiliser A)"
      using tetrahedral.stabiliser_def mem_Collect_eq by fastforce

    have "rotate_A \<in> simple_rotations"
      using simple_rotations_def insert_subset subset_insertI by blast
    then have "rotate_A \<in> complex_rotations" using complex_rotations.intros(1) by simp
    then have "rotate_A \<in> carrier tetrahedral_group"
      unfolding tetrahedral_group_def partial_object.select_convs(1) by simp
    moreover have "apply_rotation rotate_A A = A" by (simp add: rotate_A_def)
    ultimately have A:"rotate_A \<in> (tetrahedral.stabiliser A)"
      using tetrahedral.stabiliser_def mem_Collect_eq by fastforce

    have "rotate_A \<in> simple_rotations"
      using simple_rotations_def insert_subset subset_insertI by blast
    then have "rotate_A \<circ> rotate_A \<in> complex_rotations" using complex_rotations.intros by simp
    then have "rotate_A \<circ> rotate_A \<in> carrier tetrahedral_group"
      unfolding tetrahedral_group_def partial_object.select_convs(1) by simp
    moreover have "apply_rotation (rotate_A \<circ> rotate_A) A = A" by (simp add: rotate_A_def)
    ultimately have AA:"(rotate_A \<circ> rotate_A) \<in> (tetrahedral.stabiliser A)"
      using tetrahedral.stabiliser_def mem_Collect_eq by fastforce

    from id A AA show "stabiliser_A \<subseteq> tetrahedral.stabiliser A"
      by (simp add: stabiliser_A_def subsetI)
  qed
  show "tetrahedral.stabiliser A \<subseteq> stabiliser_A"
  proof
    fix x
    assume a:"x \<in> tetrahedral.stabiliser A"
    with tetrahedral.stabiliser_def have "apply_rotation x A = A" by simp
    with apply_rotation.simps have xA:"x A = A" by simp
    from a have "x \<in> carrier tetrahedral_group"
      using subgroup.mem_carrier[of "tetrahedral.stabiliser A"] tetrahedral.stabiliser_subgroup by auto
    then have xC:"x \<in> complex_rotations"
      unfolding tetrahedral_group_def partial_object.select_convs(1) by simp
    have "x B \<noteq> A" using xA xC rotation_bij_corollary by fastforce
    then have "x \<in> complex_rotations \<Longrightarrow> x A = A \<Longrightarrow> x \<in> stabiliser_A"
    proof (cases "x B", simp)
      assume "x B = B"
      then have "x = id" using complex_rotations_fix xC xA by simp
      then show ?thesis using stabiliser_A_def by auto
    next
      assume "x B = C"
      then have "x \<noteq> id" by auto
      then have "x D \<noteq> D" using complex_rotations_fix xC xA by blast
      have "x D \<noteq> C" using xC \<open>x B = C\<close> rotation_bij_corollary by fastforce 
      have "x D \<noteq> A" using xC xA rotation_bij_corollary by fastforce 
      then have "x D = B" using \<open>x D \<noteq> C\<close>  \<open>x D \<noteq> D\<close> Vertex.exhaust by blast
      
      have "x C \<noteq> A" using xC xA rotation_bij_corollary by fastforce 
      have "x C \<noteq> B" using xC \<open>x D = B\<close> rotation_bij_corollary by fastforce 
      have "x C \<noteq> C" using complex_rotations_fix xC xA \<open>x \<noteq> id\<close> by blast
      then have "x C = D" using \<open>x C \<noteq> A\<close> \<open>x C \<noteq> B\<close> Vertex.exhaust by blast

      have "\<forall> v. x v = rotate_A v" 
        using xA \<open>x B = C\<close> \<open>x D = B\<close> \<open>x C = D\<close> Vertex.exhaust rotate_A_def Vertex.simps by metis
      then have "x = rotate_A" by auto
      then show ?thesis using stabiliser_A_def by auto
    next
      assume "x B = D"
      then have "x \<noteq> id" by auto
      then have "x C \<noteq> C" using complex_rotations_fix xC xA by blast
      have "x C \<noteq> D" using xC \<open>x B = D\<close> rotation_bij_corollary by fastforce 
      have "x C \<noteq> A" using xC xA rotation_bij_corollary by fastforce 
      then have "x C = B" using \<open>x C \<noteq> D\<close>  \<open>x C \<noteq> C\<close> Vertex.exhaust by blast
      
      have "x D \<noteq> A" using xC xA rotation_bij_corollary by fastforce 
      have "x D \<noteq> B" using xC \<open>x C = B\<close> rotation_bij_corollary by fastforce 
      have "x D \<noteq> D" using complex_rotations_fix xC xA \<open>x \<noteq> id\<close> by blast
      then have "x D = C" using \<open>x D \<noteq> A\<close> \<open>x D \<noteq> B\<close> Vertex.exhaust by blast

      have "\<forall> v. x v = (rotate_A \<circ> rotate_A) v" 
        using xA \<open>x B = D\<close> \<open>x C = B\<close> \<open>x D = C\<close> Vertex.exhaust rotate_A_def Vertex.simps comp_apply by metis
      then have "x = rotate_A \<circ> rotate_A" by auto
      then show ?thesis using stabiliser_A_def by auto
    qed
    then show "x \<in> stabiliser_A" using xA xC by simp
  qed
qed

text \<open>
Using the previous result, we can now show that the cardinality of the stabiliser is 3.
\<close>
lemma card_stabiliser_help: "card stabiliser_A = 3"
proof -
  have idA:"id \<noteq> rotate_A"
  proof -
    have "id B = B" by simp
    moreover have "rotate_A B = C" by (simp add: rotate_A_def)
    ultimately show "id \<noteq> rotate_A" by force
  qed
  have idAA:"id \<noteq> rotate_A \<circ> rotate_A"
  proof -
    have "id B = B" by simp
    moreover have "(rotate_A \<circ> rotate_A) B = D" by (simp add: rotate_A_def)
    ultimately show "id \<noteq> rotate_A \<circ> rotate_A" by force
  qed
  have AAA:"rotate_A \<noteq> rotate_A \<circ> rotate_A"
  proof -
    have "rotate_A B = C" by (simp add: rotate_A_def)
    moreover have "(rotate_A \<circ> rotate_A) B = D" by (simp add: rotate_A_def)
    ultimately show "rotate_A \<noteq> rotate_A \<circ> rotate_A" by force
  qed
  from idA idAA AAA card_empty card_insert_if show
    "(card stabiliser_A) = 3" unfolding stabiliser_A_def by auto
qed

lemma card_stabiliser: "card (tetrahedral.stabiliser A) = 3"
  using is_stabiliser card_stabiliser_help by simp

section "Proving Finiteness"

text \<open>
In order to apply the orbit-stabiliser theorem, we need to prove that the set of rotations is
finite. We first prove that the set of vertices is finite.
\<close>
lemma vertex_set: "(UNIV::Vertex set) = {A, B, C, D}"
  by(auto, metis Vertex.exhaust)

lemma vertex_finite: "finite (UNIV :: Vertex set)"
  by (simp add: vertex_set)

text \<open>
Next we need instantiate Vertex as an element of the type class of finite sets in
HOL/Finite\_Set.thy. This will allow us to use the lemma that functions between finite sets
are finite themselves.
\<close>

instantiation Vertex :: finite
begin
instance proof
  show "finite (UNIV :: Vertex set)" by (simp add: vertex_set)
qed

text \<open>
Now we can show that the set of rotations is finite.
\<close>
lemma finite_carrier: "finite (carrier tetrahedral_group)"
proof -
  (* This follows from the instantiation above *)
  have "finite (UNIV :: (Vertex \<Rightarrow> Vertex) set)" by simp
  moreover have "complex_rotations \<subseteq> (UNIV :: (Vertex \<Rightarrow> Vertex) set)" by simp
  ultimately show "finite (carrier tetrahedral_group)" using finite_subset top_greatest by blast
qed

section "Order of the Group"

text \<open>
We can now finally apply the orbit-stabiliser theorem.
Since we have orbits of cardinality 4 and stabilisers of cardinality 3, the order of the tetrahedral group,
and with it the number of rotational symmetries of the tetrahedron, is 12.
\<close>
theorem "order tetrahedral_group = 12"
proof -
  have "card (tetrahedral.orbit A) * card (tetrahedral.stabiliser A) = 12"
    using card_stabiliser card_orbit by simp
  with tetrahedral.orbit_stabiliser[OF finite_carrier]
  show "order tetrahedral_group = 12" by simp
qed

end
  
end
