subsection \<open>DHH Extension\<close>

text \<open>We define a variant of the DDH assumption and show it is as hard as the original DDH assumption.\<close>

theory DH_Ext imports
  Game_Based_Crypto.Diffie_Hellman
  Cyclic_Group_Ext
begin

context ddh begin

definition DDH0 :: "'grp adversary \<Rightarrow> bool spmf"
  where "DDH0 \<A> = do {
    s \<leftarrow> sample_uniform (order \<G>);
    r \<leftarrow> sample_uniform (order \<G>);
    let h = \<^bold>g [^] s;
    \<A> h (\<^bold>g [^] r) (h [^] r)}"

definition DDH1 :: "'grp adversary \<Rightarrow> bool spmf"
  where "DDH1 \<A> = do {
    s \<leftarrow> sample_uniform (order \<G>);
    r \<leftarrow> sample_uniform (order \<G>);
    let h = \<^bold>g [^] s;
    \<A> h (\<^bold>g [^] r) ((h [^] r) \<otimes> \<^bold>g)}"

definition DDH_advantage :: "'grp adversary \<Rightarrow> real"
  where "DDH_advantage \<A> = \<bar>spmf (DDH0 \<A>) True - spmf (DDH1 \<A>) True\<bar>"

definition DDH_\<A>' :: "'grp adversary \<Rightarrow> 'grp \<Rightarrow> 'grp \<Rightarrow> 'grp \<Rightarrow> bool spmf"
  where "DDH_\<A>' D_ddh a b c = D_ddh a b (c \<otimes> \<^bold>g)"

end 

locale ddh_ext = ddh + cyclic_group \<G>
begin

lemma DDH0_eq_ddh_0: "ddh.DDH0 \<G> \<A> = ddh.ddh_0 \<G> \<A>"
  by(simp add: ddh.DDH0_def Let_def monoid.nat_pow_pow ddh.ddh_0_def) 

lemma DDH_bound1: "\<bar>spmf (ddh.DDH0 \<G> \<A>) True - spmf (ddh.DDH1 \<G> \<A>) True\<bar> 
                        \<le> \<bar>spmf (ddh.ddh_0 \<G> \<A>) True - spmf (ddh.ddh_1 \<G> \<A>) True\<bar> 
                              + \<bar>spmf (ddh.ddh_1 \<G> \<A>) True - spmf (ddh.DDH1 \<G> \<A>) True\<bar>"
  by (simp add: abs_diff_triangle_ineq2 DDH0_eq_ddh_0)

lemma DDH_bound2: 
  shows "\<bar>spmf (ddh.DDH0 \<G> \<A>) True - spmf (ddh.DDH1 \<G> \<A>) True\<bar> 
               \<le> ddh.advantage \<G> \<A> + \<bar>spmf (ddh.ddh_1 \<G> \<A>) True - spmf (ddh.DDH1 \<G> \<A>) True\<bar>"
  using advantage_def DDH_bound1 by simp

lemma rewrite: 
  shows "(sample_uniform (order \<G>) \<bind> (\<lambda>x. sample_uniform (order \<G>) 
            \<bind> (\<lambda>y. sample_uniform (order \<G>) \<bind> (\<lambda>z. \<A> (\<^bold>g [^] x) (\<^bold>g [^] y) (\<^bold>g [^] z \<otimes> \<^bold>g))))) 
              = (sample_uniform (order \<G>) \<bind> (\<lambda>x. sample_uniform (order \<G>) 
                \<bind> (\<lambda>y. sample_uniform (order \<G>) \<bind> (\<lambda>z. \<A> (\<^bold>g [^] x) (\<^bold>g [^] y) (\<^bold>g [^] z)))))"
(is "?lhs = ?rhs")
proof-
  have "?lhs = do {
   x \<leftarrow> sample_uniform (order \<G>);
   y \<leftarrow> sample_uniform (order \<G>);
   c \<leftarrow> map_spmf (\<lambda> z. \<^bold>g [^] z \<otimes> \<^bold>g) (sample_uniform (order \<G>));
   \<A> (\<^bold>g [^] x) (\<^bold>g [^] y) c}" 
    by(simp add: o_def bind_map_spmf Let_def)
  also have "... = do {
   x \<leftarrow> sample_uniform (order \<G>);
   y \<leftarrow> sample_uniform (order \<G>);
   c \<leftarrow> map_spmf (\<lambda>x. \<^bold>g [^] x) (sample_uniform (order \<G>));
   \<A> (\<^bold>g [^] x) (\<^bold>g [^] y) c}" 
    by(simp add: sample_uniform_one_time_pad)
  ultimately show ?thesis 
    by(simp add: Let_def bind_map_spmf o_def)
qed

lemma DDH_\<A>'_bound: "ddh.advantage \<G> (ddh.DDH_\<A>' \<G> \<A>) = \<bar>spmf (ddh.ddh_1 \<G> \<A>) True - spmf (ddh.DDH1 \<G> \<A>) True\<bar>"
  unfolding ddh.advantage_def ddh.ddh_1_def ddh.DDH1_def Let_def ddh.DDH_\<A>'_def ddh.ddh_0_def 
  by (simp add: rewrite abs_minus_commute nat_pow_pow)

lemma DDH_advantage_bound: "ddh.DDH_advantage \<G> \<A> \<le> ddh.advantage \<G> \<A> + ddh.advantage \<G> (ddh.DDH_\<A>' \<G> \<A>)"
  using DDH_bound2 DDH_\<A>'_bound DDH_advantage_def by simp

end 

end