section \<open>Formalization of Bit Vectors\<close>

theory BitVector imports Main begin

type_synonym bit_vector = "bool list"

fun bv_leqs :: "bit_vector \<Rightarrow> bit_vector \<Rightarrow> bool" ("_ \<preceq>\<^sub>b _" 99)
  where bv_Nils:"[] \<preceq>\<^sub>b [] = True"
  | bv_Cons:"(x#xs) \<preceq>\<^sub>b (y#ys) = ((x \<longrightarrow> y) \<and> xs \<preceq>\<^sub>b ys)"
  | bv_rest:"xs \<preceq>\<^sub>b ys = False"


subsection \<open>Some basic properties\<close>

lemma bv_length: "xs \<preceq>\<^sub>b ys \<Longrightarrow> length xs = length ys"
by(induct rule:bv_leqs.induct)auto


lemma [dest!]: "xs \<preceq>\<^sub>b [] \<Longrightarrow> xs = []"
by(induct xs) auto


lemma bv_leqs_AppendI:
  "\<lbrakk>xs \<preceq>\<^sub>b ys; xs' \<preceq>\<^sub>b ys'\<rbrakk> \<Longrightarrow> (xs@xs') \<preceq>\<^sub>b (ys@ys')"
by(induct xs ys rule:bv_leqs.induct,auto)


lemma bv_leqs_AppendD:
  "\<lbrakk>(xs@xs') \<preceq>\<^sub>b (ys@ys'); length xs = length ys\<rbrakk>
  \<Longrightarrow> xs \<preceq>\<^sub>b ys \<and> xs' \<preceq>\<^sub>b ys'"
by(induct xs ys rule:bv_leqs.induct,auto)


lemma bv_leqs_eq:
  "xs \<preceq>\<^sub>b ys = ((\<forall>i < length xs. xs ! i \<longrightarrow> ys ! i) \<and> length xs = length ys)"
proof(induct xs ys rule:bv_leqs.induct)
  case (2 x xs y ys)
  note eq = \<open>xs \<preceq>\<^sub>b ys = 
    ((\<forall>i < length xs. xs ! i \<longrightarrow> ys ! i) \<and> length xs = length ys)\<close>
  show ?case
  proof
    assume leqs:"x#xs \<preceq>\<^sub>b y#ys"
    with eq have "x \<longrightarrow> y" and "\<forall>i < length xs. xs ! i \<longrightarrow> ys ! i"
      and "length xs = length ys" by simp_all
    from \<open>x \<longrightarrow> y\<close> have "(x#xs) ! 0 \<longrightarrow> (y#ys) ! 0" by simp
    { fix i assume "i > 0" and "i < length (x#xs)"
      then obtain j where "i = Suc j" and "j < length xs" by(cases i) auto
      with \<open>\<forall>i < length xs. xs ! i \<longrightarrow> ys ! i\<close> 
      have "(x#xs) ! i \<longrightarrow> (y#ys) ! i" by auto }
    hence "\<forall>i < length (x#xs). i > 0 \<longrightarrow> (x#xs) ! i \<longrightarrow> (y#ys) ! i" by simp
    with \<open>(x#xs) ! 0 \<longrightarrow> (y#ys) ! 0\<close> \<open>length xs = length ys\<close>
    show "(\<forall>i < length (x#xs). (x#xs) ! i \<longrightarrow> (y#ys) ! i) \<and> 
      length (x#xs) = length (y#ys)"
      by clarsimp(case_tac "i>0",auto)
  next
    assume "(\<forall>i < length (x#xs). (x#xs) ! i \<longrightarrow> (y#ys) ! i) \<and> 
      length (x#xs) = length (y#ys)"
    hence "\<forall>i < length (x#xs). (x#xs) ! i \<longrightarrow> (y#ys) ! i" 
      and "length (x#xs) = length (y#ys)" by simp_all
    from \<open>\<forall>i < length (x#xs). (x#xs) ! i \<longrightarrow> (y#ys) ! i\<close>
    have "\<forall>i < length xs. xs ! i \<longrightarrow> ys ! i"
      by clarsimp(erule_tac x="Suc i" in allE,auto)
    with eq \<open>length (x#xs) = length (y#ys)\<close> have "xs \<preceq>\<^sub>b ys" by simp
    from \<open>\<forall>i < length (x#xs). (x#xs) ! i \<longrightarrow> (y#ys) ! i\<close>
    have "x \<longrightarrow> y" by(erule_tac x="0" in allE) simp
    with \<open>xs \<preceq>\<^sub>b ys\<close> show "x#xs \<preceq>\<^sub>b y#ys" by simp
  qed
qed simp_all


subsection \<open>$\preceq_b$ is an order on bit vectors with minimal and 
  maximal element\<close>

lemma minimal_element:
  "replicate (length xs) False \<preceq>\<^sub>b xs"
by(induct xs) auto

lemma maximal_element:
  "xs \<preceq>\<^sub>b replicate (length xs) True"
by(induct xs) auto

lemma bv_leqs_refl:"xs \<preceq>\<^sub>b xs"
  by(induct xs) auto


lemma bv_leqs_trans:"\<lbrakk>xs \<preceq>\<^sub>b ys; ys \<preceq>\<^sub>b zs\<rbrakk> \<Longrightarrow> xs \<preceq>\<^sub>b zs"
proof(induct xs ys arbitrary:zs rule:bv_leqs.induct)
  case (2 x xs y ys)
  note IH = \<open>\<And>zs. \<lbrakk>xs \<preceq>\<^sub>b ys; ys \<preceq>\<^sub>b zs\<rbrakk> \<Longrightarrow> xs \<preceq>\<^sub>b zs\<close>
  from \<open>(x#xs) \<preceq>\<^sub>b (y#ys)\<close> have "xs \<preceq>\<^sub>b ys" and "x \<longrightarrow> y" by simp_all
  from \<open>(y#ys) \<preceq>\<^sub>b zs\<close> obtain z zs' where "zs = z#zs'" by(cases zs) auto
  with \<open>(y#ys) \<preceq>\<^sub>b zs\<close> have "ys \<preceq>\<^sub>b zs'" and "y \<longrightarrow> z" by simp_all
  from IH[OF \<open>xs \<preceq>\<^sub>b ys\<close> \<open>ys \<preceq>\<^sub>b zs'\<close>] have "xs \<preceq>\<^sub>b zs'" .
  with \<open>x \<longrightarrow> y\<close> \<open>y \<longrightarrow> z\<close> \<open>zs = z#zs'\<close> show ?case by simp
qed simp_all


lemma bv_leqs_antisym:"\<lbrakk>xs \<preceq>\<^sub>b ys; ys \<preceq>\<^sub>b xs\<rbrakk> \<Longrightarrow> xs = ys"
  by(induct xs ys rule:bv_leqs.induct)auto


definition bv_less :: "bit_vector \<Rightarrow> bit_vector \<Rightarrow> bool" ("_ \<prec>\<^sub>b _" 99)
  where "xs \<prec>\<^sub>b ys \<equiv> xs \<preceq>\<^sub>b ys \<and> xs \<noteq> ys"


interpretation order "bv_leqs" "bv_less"
by(unfold_locales,
   auto intro:bv_leqs_refl bv_leqs_trans bv_leqs_antisym simp:bv_less_def)


end
