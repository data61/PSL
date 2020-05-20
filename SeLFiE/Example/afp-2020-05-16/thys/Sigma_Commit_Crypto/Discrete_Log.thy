theory Discrete_Log imports 
  CryptHOL.CryptHOL
  Cyclic_Group_Ext
begin 

locale dis_log = 
  fixes \<G> :: "'grp cyclic_group" (structure)
  assumes order_gt_0 [simp]: "order \<G> > 0"
begin

type_synonym 'grp' dislog_adv = "'grp' \<Rightarrow> nat spmf"

type_synonym 'grp' dislog_adv' = "'grp' \<Rightarrow> (nat \<times> nat) spmf"

type_synonym 'grp' dislog_adv2 = "'grp' \<times> 'grp' \<Rightarrow> nat spmf"

definition dis_log :: "'grp dislog_adv \<Rightarrow> bool spmf"
where "dis_log \<A> = TRY do {
  x \<leftarrow> sample_uniform (order \<G>);
  let h = \<^bold>g [^] x; 
  x'\<leftarrow> \<A> h;
  return_spmf ([x = x'] (mod order \<G>))} ELSE return_spmf False"

definition advantage :: "'grp dislog_adv \<Rightarrow> real"
where "advantage \<A> \<equiv> spmf (dis_log \<A>) True" 

lemma lossless_dis_log: "\<lbrakk>0 < order \<G>; \<forall> h. lossless_spmf (\<A> h)\<rbrakk> \<Longrightarrow> lossless_spmf (dis_log \<A>)"
by(auto simp add:  dis_log_def)

end 

locale dis_log_alt = 
  fixes \<G> :: "'grp cyclic_group" (structure)
    and x :: nat
  assumes order_gt_0 [simp]: "order \<G> > 0"
begin

sublocale dis_log: dis_log \<G>
  unfolding dis_log_def by simp

definition "g' = \<^bold>g [^] x"

definition dis_log2 :: "'grp dis_log.dislog_adv' \<Rightarrow> bool spmf"
where "dis_log2 \<A> = TRY do {
    w \<leftarrow> sample_uniform (order \<G>);
    let h = \<^bold>g [^] w;
    (w1',w2') \<leftarrow> \<A> h;
    return_spmf ([w = (w1' + x * w2')]  (mod (order \<G>)))} ELSE return_spmf False"

definition advantage2 :: "'grp dis_log.dislog_adv' \<Rightarrow> real"
where "advantage2 \<A> \<equiv> spmf (dis_log2 \<A>) True" 

definition adversary2 :: "('grp \<Rightarrow> (nat \<times> nat) spmf) \<Rightarrow> 'grp \<Rightarrow> nat spmf"
  where "adversary2 \<A> h = do {
    (w1,w2) \<leftarrow> \<A> h;
    return_spmf (w1 + x * w2)}"

definition dis_log3 :: "'grp dis_log.dislog_adv2 \<Rightarrow> bool spmf"
where "dis_log3 \<A> = TRY do {
    w \<leftarrow> sample_uniform (order \<G>);
    let (h,w) = ((\<^bold>g [^] w, g' [^] w), w);
    w' \<leftarrow> \<A> h;
    return_spmf ([w = w'] (mod (order \<G>)))} ELSE return_spmf False"

definition advantage3 :: "'grp dis_log.dislog_adv2 \<Rightarrow> real"
  where "advantage3 \<A> \<equiv> spmf (dis_log3 \<A>) True" 

definition adversary3:: "'grp dis_log.dislog_adv2 \<Rightarrow> 'grp \<Rightarrow> nat spmf"
  where "adversary3 \<A> g = do {
    \<A> (g, g [^] x)}"

end 

locale dis_log_alt_reductions = dis_log_alt + cyclic_group \<G> 
begin

lemma dis_log_adv3:
  shows "advantage3 \<A> = dis_log.advantage (adversary3 \<A>)"
  unfolding dis_log_alt.advantage3_def
  by(simp add: advantage3_def dis_log.advantage_def adversary3_def dis_log.dis_log_def dis_log3_def Let_def g'_def power_swap)

lemma dis_log_adv2:
  shows  "advantage2 \<A> = dis_log.advantage (adversary2 \<A>)"
  unfolding dis_log_alt.advantage2_def
  by(simp add: advantage2_def dis_log2_def dis_log.advantage_def dis_log.dis_log_def adversary2_def split_def)

end 

end
