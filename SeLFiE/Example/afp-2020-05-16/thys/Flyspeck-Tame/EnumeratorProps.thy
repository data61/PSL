(*  Author:  Gertrud Bauer, Tobias Nipkow  *)

section\<open>Properties of Patch Enumeration\<close>

theory EnumeratorProps
imports Enumerator GraphProps
begin

lemma length_hideDupsRec[simp]: "\<And>x. length(hideDupsRec x xs) = length xs"
by(induct xs) auto

lemma length_hideDups[simp]: "length(hideDups xs) = length xs"
by(cases xs) simp_all

lemma length_indexToVertexList[simp]:
 "length(indexToVertexList x y xs) = length xs"
by(simp add:indexToVertexList_def)


(***************************** List not decreasing ***************************)
definition increasing :: "('a::linorder) list \<Rightarrow> bool" where
 "increasing ls \<equiv> \<forall> x y as bs. ls = as @ x # y # bs \<longrightarrow> x \<le> y"

lemma increasing1: "\<And> as x. increasing ls \<Longrightarrow> ls = as @ x # cs @ y # bs \<Longrightarrow> x \<le> y"
proof (induct cs)
  case Nil then show ?case
    by (auto simp: increasing_def)
next
  case (Cons c cs) then show ?case
    apply (subgoal_tac "c \<le> y")
    apply (force simp: increasing_def)
    apply (rule_tac Cons) by simp_all
qed

lemma increasing2: "increasing (as@bs) \<Longrightarrow> x \<in> set as \<Longrightarrow> y \<in> set bs \<Longrightarrow> x \<le> y"
proof-
  assume n:"increasing (as@bs)" and x:"x \<in> set as" and y: "y \<in> set bs"
  from x obtain as' as'' where as: "as = as' @ x # as''" by (auto simp: in_set_conv_decomp)
  from y obtain bs' bs'' where bs: "bs = bs' @ y # bs''" by (auto simp: in_set_conv_decomp)
  from n as bs show ?thesis
  apply (auto intro!: increasing1)
  apply (subgoal_tac "as' @ x # as'' @ bs' @ y # bs'' = as' @ x # (as'' @ bs') @ y # bs''")
  by (assumption) auto
qed

lemma increasing3: "\<forall> as bs. (ls = as @ bs \<longrightarrow> (\<forall> x \<in> set as. \<forall> y \<in> set bs. x \<le> y)) \<Longrightarrow> increasing (ls)"
apply (simp add: increasing_def) apply safe
proof -
  fix as bs x y
  assume p: "\<forall>asa bsa. as @ x # y # bs = asa @ bsa \<longrightarrow> (\<forall>x\<in>set asa. \<forall>y\<in>set bsa. x \<le> y)"
  then have p': "\<And> asa bsa. as @ x # y # bs = asa @ bsa \<Longrightarrow> (\<forall>x\<in>set asa. \<forall>y\<in>set bsa. x \<le> y)" by auto
  then have "(\<forall>x\<in>set (as @ [x]). \<forall>y\<in>set (y # bs). x \<le> y)" by (rule_tac p') auto
  then show "x \<le> y" by (auto simp: increasing_def)
qed

lemma increasing4: "increasing (as@bs) \<Longrightarrow> increasing as"
apply (simp add: increasing_def) apply safe by auto

lemma increasing5: "increasing (as@bs) \<Longrightarrow> increasing bs"
proof -
  assume nd: "increasing (as@bs)"
  then have r: "\<And> x y asa bsa. (\<exists>asa bsa. as @ bs = asa @ x # y # bsa) \<Longrightarrow> x \<le> y" by (auto simp: increasing_def)
  show ?thesis apply (clarsimp simp add: increasing_def)
    apply (rule_tac r)
    apply (rule_tac x="as @ _" in exI)
    apply auto
    done
qed


(*********************************** EnumeratorProps *************************************)

(********** enumBase ***********)

lemma enumBase_length: "ls \<in> set (enumBase nmax) \<Longrightarrow> length ls = 1"
by (auto simp: enumBase_def)

lemma enumBase_bound: "\<forall>y \<in> set (enumBase nmax). \<forall>z \<in> set y. z \<le> nmax"
by (auto simp: enumBase_def)

lemmas enumBase_simps = enumBase_length enumBase_bound


(********** enumAppend ************)

lemma enumAppend_bound: "ls \<in> set ((enumAppend nmax) lss) \<Longrightarrow>
 \<forall> y \<in> set lss. \<forall> z \<in> set y. z \<le> nmax \<Longrightarrow> x \<in> set ls \<Longrightarrow> x \<le>  nmax"
by (auto simp add: enumAppend_def split: if_split_asm)


lemma enumAppend_bound_rec: "ls \<in> set (((enumAppend nmax) ^^ n) lss) \<Longrightarrow>
  \<forall> y \<in> set lss. \<forall> z \<in> set y. z \<le> nmax \<Longrightarrow> x \<in> set ls \<Longrightarrow> x \<le>  nmax"
proof -
  assume ls: "ls \<in> set ((enumAppend nmax ^^ n) lss)" and lss: "\<forall>y\<in>set lss. \<forall>z\<in>set y. z \<le> nmax" and x: "x \<in> set ls"
  have ind:"\<And> lss. \<forall>y\<in>set lss. \<forall>z\<in>set y. z \<le> nmax \<Longrightarrow> \<forall> y \<in> set (((enumAppend nmax) ^^ n) lss). \<forall> z \<in> set y. z \<le> nmax"
  proof (induct n)
    case 0 then show ?case by auto
  next
    case (Suc n) show ?case apply (intro ballI) apply (rule enumAppend_bound) by (auto intro!: Suc)
  qed
  with lss have "\<forall> y \<in> set (((enumAppend nmax) ^^ n) lss). \<forall> z \<in> set y. z \<le> nmax" apply (rule_tac ind) .
  with ls x show ?thesis by auto
qed

lemma enumAppend_increase_rec:
  "\<And> m as bs. ls \<in> set (((enumAppend nmax) ^^ m) (enumBase nmax)) \<Longrightarrow>
  as @ bs = ls \<Longrightarrow>  \<forall> x \<in> set as. \<forall> y \<in> set bs. x \<le> y"
apply (induct ls rule: rev_induct) apply force apply auto apply (case_tac "m") apply simp  apply (drule_tac enumBase_length)
apply (case_tac as) apply simp_all
proof -
  fix x xs m as bs xa xb n
  assume ih: "\<And>m as bs.
           \<lbrakk>xs \<in> set ((enumAppend nmax ^^ m) (enumBase nmax)); as @ bs = xs\<rbrakk>
           \<Longrightarrow> \<forall>x\<in>set as. \<forall>xa\<in>set bs. x \<le> xa"
    and xs:"xs @ [x] \<in> set (enumAppend nmax ((enumAppend nmax ^^ n) (enumBase nmax)))"
    and asbs: "as @ bs = xs @ [x]" and xa:"xa \<in> set as" and xb: "xb \<in> set bs" and m: "m = Suc n"
  from ih have ih2: "\<And> as bs x y. \<lbrakk>xs \<in> set ((enumAppend nmax ^^ n) (enumBase nmax)); as @ bs = xs; x \<in> set as; y \<in> set bs\<rbrakk>
           \<Longrightarrow> x \<le> y" by auto

  from xb have "bs \<noteq> []"  by auto
  then obtain bs' b where bs': "bs = bs' @ [b]" apply (cases rule: rev_exhaust) by auto
  with asbs have beq:"b = x" by auto
  from bs' asbs have xs': "as @ bs' = xs" by auto
  with xs have "xa \<le> x"
  proof (cases "xs" rule: rev_exhaust)
    case Nil with xa xs' show ?thesis by auto
  next
    case (snoc ys y)
    have "xa \<le> y"
    proof (cases "xa = y")
      case True then show ?thesis by auto
    next
      case False
      from xa xs' have "xa \<in> set xs" by auto
      with False snoc have "xa \<in> set ys" by auto
      with xs snoc  show ?thesis
        apply (rule_tac ih2)
        by (auto simp: enumAppend_def)
    qed
    with xs snoc show "xa \<le> x" by (auto simp: enumAppend_def split:if_split_asm)
  qed
  then show "xa \<le> xb" apply (cases "xb = b") apply (simp add: beq)
  proof (rule_tac ih2)
    from xs
    show "xs \<in> set ((enumAppend nmax ^^ n) (enumBase nmax))"
    by (auto simp: enumAppend_def)
  next
    from xs' show "as @ bs' = xs" by auto
  next
    from xa show "xa \<in> set as" by auto
  next
    assume "xb \<noteq> b"
    with xb bs' show "xb \<in> set bs'" by auto
  qed
qed

lemma enumAppend_length1: "\<And>ls. ls \<in> set ((enumAppend nmax ^^ n) lss) \<Longrightarrow>
 (\<forall>l \<in> set lss. |l| = k) \<Longrightarrow> |ls| = k + n"
apply (induct n)
apply simp
by (auto simp add:enumAppend_def split: if_split_asm)

lemma enumAppend_length2: "\<And>ls. ls \<in> set ((enumAppend nmax ^^ n) lss) \<Longrightarrow>
 (\<And>l. l \<in> set lss \<Longrightarrow> |l| = k) \<Longrightarrow> K = k + n \<Longrightarrow> |ls| = K"
 by (auto simp add: enumAppend_length1)


(*********** enum *********)

lemma enum_enumerator:
 "enum i j = enumerator i j"
by(simp add: enum_def enumTab_def tabulate2_def tabulate_def)


(*********** enumerator *********)

lemma enumerator_hd: "ls \<in> set (enumerator m n) \<Longrightarrow> hd ls = 0"
by (auto simp: enumerator_def split: if_split_asm)

lemma enumerator_last: "ls \<in> set (enumerator m n) \<Longrightarrow> last ls = (n - 1)"
by (auto simp: enumerator_def split: if_split_asm)

lemma enumerator_length: "ls \<in> set (enumerator m n) \<Longrightarrow> 2 \<le> length ls"
by (auto simp: enumerator_def split: if_split_asm)

lemmas set_enumerator_simps = enumerator_hd enumerator_last enumerator_length

lemma enumerator_not_empty[dest]: "ls \<in> set (enumerator m n) \<Longrightarrow> ls \<noteq>  []"
apply (subgoal_tac "2 \<le> length ls") apply force  by (rule enumerator_length)

lemma enumerator_length2: "ls \<in> set (enumerator m n) \<Longrightarrow> 2 < m \<Longrightarrow> length ls = m"
proof -
  assume ls:"ls \<in> set (enumerator m n)" and m: "2 < m"
  define k where "k = m - 3"
  with m have k: "m = k + 3" by arith
  with ls have "ls \<in> set (enumerator (k+3) n)" by auto
  then have "length ls = k + 3"
    apply (auto simp: enumerator_def enumBase_def)
    apply (erule enumAppend_length2) by auto
  with k show ?thesis by simp
qed

lemma enumerator_bound: "ls \<in> set (enumerator m nmax) \<Longrightarrow>
 0 < nmax \<Longrightarrow> x \<in> set ls \<Longrightarrow> x < nmax"
apply (auto simp: enumerator_def split: if_split_asm)
apply (subgoal_tac "x \<le> nmax - 2") apply arith
apply (rule_tac enumAppend_bound_rec) by(auto simp:enumBase_simps)

lemma enumerator_bound2: "ls \<in> set (enumerator m nmax) \<Longrightarrow> 1 < nmax \<Longrightarrow> x \<in> set (butlast ls) \<Longrightarrow> x < nmax - Suc 0"
apply (auto simp: enumerator_def split: if_split_asm)
apply (subgoal_tac "x \<le>  (nmax - 2)") apply arith
apply (rule_tac enumAppend_bound_rec) by(auto simp:enumBase_simps)

lemma enumerator_bound3: "ls \<in> set (enumerator m nmax) \<Longrightarrow> 1 < nmax \<Longrightarrow> last (butlast ls) < nmax - Suc 0"
apply (case_tac "ls" rule: rev_exhaust) apply force
apply (rule_tac enumerator_bound2) apply assumption
apply auto
apply (case_tac "ys" rule: rev_exhaust) apply simp
apply (subgoal_tac "2 \<le> length (ys @ [y])") apply simp
apply (rule_tac enumerator_length) by auto


lemma enumerator_increase: "\<And> as bs. ls \<in> set (enumerator m nmax) \<Longrightarrow>  as @ bs = ls \<Longrightarrow> \<forall> x \<in> set as. \<forall> y \<in> set bs. x \<le> y"
apply (auto simp: enumerator_def del: Nat.diff_is_0_eq' split: if_split_asm intro: enumAppend_increase_rec)
apply (case_tac as) apply simp apply simp
apply (case_tac bs rule: rev_exhaust)  apply simp apply simp apply auto
apply (drule_tac enumAppend_bound_rec) apply (auto simp:enumBase_simps)
by (auto dest!: enumAppend_increase_rec)

lemma enumerator_increasing: "ls \<in> set (enumerator m nmax) \<Longrightarrow> increasing ls"
apply (rule increasing3)
by (auto dest: enumerator_increase)

definition incrIndexList :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
 "incrIndexList ls m nmax \<equiv>
  1 < m \<and> 1 < nmax \<and>
  hd ls = 0 \<and> last ls = (nmax - 1) \<and> length ls = m
 \<and> last (butlast ls) < last ls \<and> increasing ls"

lemma incrIndexList_1lem[simp]: "incrIndexList ls m nmax \<Longrightarrow> Suc 0 < m"
by (unfold incrIndexList_def) simp

lemma incrIndexList_1len[simp]: "incrIndexList ls m nmax \<Longrightarrow> Suc 0 < nmax"
by (unfold incrIndexList_def) simp

lemma incrIndexList_help2[simp]: "incrIndexList ls m nmax \<Longrightarrow> hd ls = 0"
by (unfold incrIndexList_def) simp

lemma incrIndexList_help21[simp]: "incrIndexList (l # ls) m nmax \<Longrightarrow> l = 0"
by (auto dest: incrIndexList_help2)

lemma incrIndexList_help3[simp]: "incrIndexList ls m nmax \<Longrightarrow> last ls = (nmax - (Suc 0))"
by (unfold incrIndexList_def)  simp

lemma incrIndexList_help4[simp]: "incrIndexList ls m nmax \<Longrightarrow> length ls = m "
by (unfold incrIndexList_def)  simp

lemma incrIndexList_help5[intro]: "incrIndexList ls m nmax \<Longrightarrow>  last (butlast ls) < nmax - Suc 0"
by (unfold incrIndexList_def) auto

lemma incrIndexList_help6[simp]: "incrIndexList ls m nmax \<Longrightarrow> increasing ls"
by (unfold incrIndexList_def) simp

lemma incrIndexList_help7[simp]: "incrIndexList ls m nmax \<Longrightarrow> ls \<noteq> []"
apply (subgoal_tac "length ls \<noteq>  0") apply force
apply simp
apply (subgoal_tac "1 < m")  apply arith apply force done

lemma incrIndexList_help71[simp]: "\<not> incrIndexList [] m nmax"
by (auto dest: incrIndexList_help7)

lemma incrIndexList_help8[simp]: "incrIndexList ls m nmax \<Longrightarrow> butlast ls \<noteq> []"
proof (rule ccontr)
  assume props: "incrIndexList ls m nmax" and butl: "\<not> butlast ls \<noteq> []"
  then have "ls \<noteq> []" by auto
  then have ls': "ls = (butlast ls) @ [last ls]" by auto
  define l where "l = last ls"
  with butl ls' have "ls = [l]" by auto
  then have "length ls = 1" by auto
  with props have "m = 1" by auto
  with props show "False" by (auto dest: incrIndexList_1lem)
qed

lemma incrIndexList_help81[simp]: "\<not> incrIndexList [l] m nmax"
by (auto dest: incrIndexList_help8)

lemma incrIndexList_help9[intro]: "(incrIndexList ls m nmax)  \<Longrightarrow>
  x \<in> set (butlast ls) \<Longrightarrow> x \<le> nmax - 2"
proof -
  assume props: "(incrIndexList ls m nmax)"  and x: "x \<in> set (butlast ls)"
  then have "last (butlast ls) < last ls" by auto
  with props have "last (butlast ls) < nmax - 1" by auto
  then have leq: "last (butlast ls) \<le>  nmax - 2" by arith
  from props  have "ls \<noteq> []" by auto
  then have ls1: "ls = butlast ls @ [last ls]" by auto
  define ls' where "ls' = butlast (butlast ls)"
  define last2 where "last2 = last (butlast ls)"
  define last1 where "last1 = last ls"
  from props  have "butlast ls \<noteq> []" by auto
  with ls'_def last2_def have bls: "butlast ls = ls' @ [last2]" by auto
  with last1_def ls1 props have ls3: "ls = ls' @ [last2] @ [last1]" by auto
  from props  have "increasing ls" by auto
  with ls3 have increasing: "increasing (ls' @ ([last2] @ [last1]))" by auto
  then have "x \<in> set ls' \<Longrightarrow> x \<le> last2" by (auto intro: increasing2)
  then have "x \<in> set (ls' @ [last2]) \<Longrightarrow> x \<le> last2" by auto
  with bls x have "x \<le> last2" by auto
  with leq last2_def show ?thesis by auto
qed


lemma incrIndexList_help10[intro]: "(incrIndexList ls m nmax)  \<Longrightarrow>
  x \<in> set ls \<Longrightarrow> x < nmax" apply (cases ls rule: rev_exhaust) apply auto
  apply (frule incrIndexList_help3) apply (auto dest: incrIndexList_1len)
  apply (frule incrIndexList_help9) apply auto apply (drule incrIndexList_1len)
  by arith

lemma enumerator_correctness: "2 < m \<Longrightarrow> 1 < nmax \<Longrightarrow>
  ls \<in> set (enumerator m nmax) \<Longrightarrow>
  incrIndexList ls m nmax"
proof -
  assume m: "2 < m" and nmax: "1 < nmax" and enum: "ls \<in> set (enumerator m nmax)"
  then have "(hd ls = 0 \<and> last ls = (nmax - 1) \<and> length ls = m \<and> last (butlast ls) < last ls \<and>  increasing ls)"
    by (auto intro: enumerator_increasing enumerator_hd enumerator_last enumerator_length2 enumerator_bound3 simp: set_enumerator_simps)
  with m nmax show ?thesis by (unfold incrIndexList_def) auto
qed

lemma enumerator_completeness_help: "\<And> ls. increasing ls \<Longrightarrow> ls \<noteq> [] \<Longrightarrow> length ls = Suc ks \<Longrightarrow> list_all (\<lambda>x. x < Suc nmax) ls \<Longrightarrow> ls \<in> set ((enumAppend nmax ^^ ks) (enumBase nmax))"
proof (induct ks)
  case 0
  assume "increasing ls" "ls \<noteq> []" "length ls = Suc 0" "list_all (\<lambda>x. x < Suc nmax) ls"
  then have "\<exists> x. ls = [x]"
    apply (case_tac "ls::nat list") by auto
  then obtain x where ls1: "ls = [x]" by auto
  with 0 have "x < Suc nmax" by auto
  with ls1 show ?case apply (simp add: enumBase_def) by auto
next
  case (Suc n)
  define ls' where "ls' = butlast ls"
  define l where "l = last ls"
  define ll where "ll = last ls'"
  define bl where "bl = butlast ls'"
  define ls'list where "ls'list = (enumAppend nmax ^^ n) (enumBase nmax)"
  then have short: "(enumAppend nmax ^^ n) (enumBase nmax) = ls'list" by simp
  from Suc have "ls \<noteq> []" by auto
  then have "ls = butlast ls @ [last ls]" by auto
  with ls'_def l_def have ls1: "ls = ls' @ [l]" by auto
  with Suc have "length ls' = Suc n" by auto
  then have ls'ne: "ls' \<noteq> []" by auto
  with ll_def bl_def have ls'1: "ls' = bl @ [ll]" by auto
  then have ll_in_ls': "ll \<in> set ls'" by simp
  from Suc ls1 have "list_all (\<lambda>x. x < Suc nmax) ls'" by auto
  with ll_in_ls' have "ll < Suc nmax" by (induct ls') auto
  with ll_def have llsmall: "last ls' \<le> nmax"  by auto

  from ls1 have l_in_ls: "l \<in> set ls" by auto
  from Suc have "list_all (\<lambda>x. x < Suc nmax) ls" by auto
  with l_in_ls have "l < Suc nmax" by (induct ls) auto
  then have lo: "l \<le> nmax" by auto

  from Suc ls1 ls'1 have "increasing ((bl @ [ll]) @ [l])" by auto
  then have "ll \<le>  l" by (rule increasing2) auto
  with ll_def have lu: "last ls' \<le> l" by simp

  from Suc ls1 have vors: "ls' \<in> set ((enumAppend nmax ^^ n) (enumBase nmax))"
    by (rule_tac Suc) (auto intro: increasing4)
  with short have "ls' \<in> set ls'list"  by  auto
  with short llsmall ls1 lo lu show ?case  apply simp  apply (simp add: enumAppend_def)
    apply (intro bexI) by auto
qed

lemma enumerator_completeness: "2 < m \<Longrightarrow> incrIndexList ls m nmax \<Longrightarrow>
  ls \<in> set (enumerator m nmax)"
proof -
  assume m: "2 < m" and props: "incrIndexList ls m nmax"
  then have props': "(hd ls = 0 \<and> last ls = (nmax - 1)
   \<and> length ls = m \<and> last (butlast ls) < last ls \<and>  increasing ls)"
   by (unfold incrIndexList_def) auto
  show ?thesis
  proof -
    have props'': "hd ls = 0 \<and> last ls = (nmax - 1) \<and> length ls = m \<and>
       increasing ls"
      by (auto simp: props')
    show "ls \<in> set (enumerator m nmax)"
    proof -
      from m props'' have l_ls: "2 < length ls"  by auto
      then have "\<exists> x y ks. ls = x # ks @ [y]"
        apply (case_tac "ls::(nat list)") apply auto
        apply (case_tac "list" rule: rev_exhaust) by auto
      then obtain x y ks where "ls = x # ks @ [y]" by auto
      with props'' have ls': "ls = 0 # ks @ [nmax - 1]" by auto
      with l_ls have l_ms: "0 < length ks" by auto
      then have ms_ne: "ks \<noteq> []" by auto
      from ls' have lks: "length ks = length ls - 2" by auto
      from props'' have nd: "increasing ls" by auto
      from props'' have "\<And> z. z \<in> set ks \<Longrightarrow> 0 \<le> z" by auto
      from props'' ls' have "increasing ((0 # ks) @ [nmax - 1])" by auto
      then have z: "\<And> z. z \<in> set ks \<Longrightarrow> z \<le> (nmax - 1)"
        by (drule_tac increasing2) auto
      from props  ls' have z': "\<And> z. z \<in> set ks \<Longrightarrow> z \<le> (nmax - 2)" by auto

      have "ks \<in> set ((enumAppend (nmax - 2)
         ^^ (length ks - Suc 0)) (enumBase (nmax - 2)))"
      proof (cases "ks = []")   
        case True with ms_ne show ?thesis by simp
      next
        case False
        from props'' have "increasing ls" by auto
        with ls' have "increasing (0 # ks)" by (auto intro: increasing4)
        then have "increasing ([0] @ ks)" by auto
        then have ndks: "increasing ks" by (rule_tac increasing5)
        have listall: "list_all (\<lambda>x. x < Suc (nmax - 2)) ks"
          apply (simp add: list_all_iff)
          by (auto dest: z')
        with False ndks show ?thesis
          apply (rule_tac enumerator_completeness_help) by auto
      qed
      with lks props' have
        "ks \<in> set ((enumAppend (nmax - 2) ^^ (m - 3)) (enumBase (nmax - 2)))" by auto
      with m ls' show ?thesis by (simp add: enumerator_def)
    qed
  qed
qed

lemma enumerator_equiv[simp]:
 "2 < n \<Longrightarrow> 1 < m \<Longrightarrow> is \<in> set(enumerator n m) = incrIndexList is n m"
by (auto intro: enumerator_correctness enumerator_completeness)


end
