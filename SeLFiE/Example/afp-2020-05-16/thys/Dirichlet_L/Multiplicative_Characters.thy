(*
    File:      Multiplicative_Characters.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Multiplicative Characters of Finite Abelian Groups\<close>
theory Multiplicative_Characters
imports
  Complex_Main
  Group_Adjoin
begin

subsection \<open>Definition of characters\<close>

text \<open>
  A (multiplicative) character is a completely multiplicative function from a group to the
  complex numbers. For simplicity, we restrict this to finite abelian groups here, which is
  the most interesting case.

  Characters form a group where the identity is the \emph{principal} character that maps all
  elements to $1$, multiplication is point-wise multiplication of the characters, and the inverse
  is the point-wise complex conjugate.

  This group is often called the \emph{Pontryagin dual} group and is isomorphic to the original
  group (in a non-natural way) while the double-dual group \<^emph>\<open>is\<close> naturally isomorphic to the
  original group.

  To get extensionality of the characters, we also require characters to map anything that is
  not in the group to $0$.
\<close>

definition principal_char :: "('a, 'b) monoid_scheme \<Rightarrow> 'a \<Rightarrow> complex" where
  "principal_char G a = (if a \<in> carrier G then 1 else 0)"

definition inv_character where
  "inv_character \<chi> = (\<lambda>a. cnj (\<chi> a))"

lemma inv_character_principal [simp]: "inv_character (principal_char G) = principal_char G"
  by (simp add: inv_character_def principal_char_def fun_eq_iff)

lemma inv_character_inv_character [simp]: "inv_character (inv_character \<chi>) = \<chi>"
  by (simp add: inv_character_def)

lemma eval_inv_character: "inv_character \<chi> j = cnj (\<chi> j)"
  by (simp add: inv_character_def)


bundle character_syntax
begin
notation principal_char ("\<chi>\<^sub>0\<index>")
end

locale character = finite_comm_group +
  fixes \<chi> :: "'a \<Rightarrow> complex"
  assumes char_one_nz: "\<chi> \<one> \<noteq> 0"
  assumes char_eq_0:   "a \<notin> carrier G \<Longrightarrow> \<chi> a = 0"
  assumes char_mult [simp]: "a \<in> carrier G \<Longrightarrow> b \<in> carrier G \<Longrightarrow> \<chi> (a \<otimes> b) = \<chi> a * \<chi> b"
begin


subsection \<open>Basic properties\<close>

lemma char_one [simp]: "\<chi> \<one> = 1"
proof-
  from char_mult[of \<one> \<one>] have "\<chi> \<one> * (\<chi> \<one> - 1) = 0"
    by (auto simp del: char_mult)
  with char_one_nz show ?thesis by simp
qed

lemma char_power [simp]: "a \<in> carrier G \<Longrightarrow> \<chi> (a [^] k) = \<chi> a ^ k"
  by (induction k) auto

lemma char_root:
  assumes "a \<in> carrier G"
  shows   "\<chi> a ^ ord a = 1"
proof -
  from assms have "\<chi> a ^ ord a = \<chi> (a [^] ord a)"
    by (subst char_power) auto
  also from fin and assms have "a [^] ord a = \<one>" by (intro pow_ord_eq_1) auto
  finally show ?thesis by simp
qed

lemma char_root':
  assumes "a \<in> carrier G"
  shows   "\<chi> a ^ order G = 1"
proof -
  from assms have "\<chi> a ^ order G = \<chi> (a [^] order G)" by simp
  also from fin and assms have "a [^] order G = \<one>" by (intro pow_order_eq_1) auto
  finally show ?thesis by simp
qed

lemma norm_char: "norm (\<chi> a) = (if a \<in> carrier G then 1 else 0)"
proof (cases "a \<in> carrier G")
  case True
  have "norm (\<chi> a) ^ order G = norm (\<chi> a ^ order G)" by (simp add: norm_power)
  also from True have "\<chi> a ^ order G = 1" by (rule char_root')
  finally have "norm (\<chi> a) ^ order G = 1 ^ order G" by simp
  hence "norm (\<chi> a) = 1" by (subst (asm) power_eq_iff_eq_base) auto
  with True show ?thesis by auto
next
  case False
  thus ?thesis by (auto simp: char_eq_0)
qed

lemma char_eq_0_iff: "\<chi> a = 0 \<longleftrightarrow> a \<notin> carrier G"
proof -
  have "\<chi> a = 0 \<longleftrightarrow> norm (\<chi> a) = 0" by simp
  also have "\<dots> \<longleftrightarrow> a \<notin> carrier G" by (subst norm_char) auto
  finally show ?thesis .
qed

lemma inv_character: "character G (inv_character \<chi>)"
  by standard (auto simp: inv_character_def char_eq_0)

lemma mult_inv_character: "\<chi> k * inv_character \<chi> k = principal_char G k"
proof -
  have "\<chi> k * inv_character \<chi> k = of_real (norm (\<chi> k) ^ 2)"
    by (subst complex_norm_square) (simp add: inv_character_def)
  also have "\<dots> = principal_char G k"
    by (simp add: principal_char_def norm_char)
  finally show ?thesis .
qed

lemma
  assumes "a \<in> carrier G"
  shows    char_inv: "\<chi> (inv a) = cnj (\<chi> a)" and char_inv': "\<chi> (inv a) = inverse (\<chi> a)"
proof -
  from assms have "inv a \<otimes> a = \<one>" by simp
  also have "\<chi> \<dots> = 1" by simp
  also from assms have "\<chi> (inv a \<otimes> a) = \<chi> (inv a) * \<chi> a"
    by (intro char_mult) auto
  finally have *: "\<chi> (inv a) * \<chi> a = 1" .
  thus "\<chi> (inv a) = inverse (\<chi> a)" by (auto simp: divide_simps)
  also from mult_inv_character[of a] and assms have "inverse (\<chi> a) = cnj (\<chi> a)"
    by (auto simp add: inv_character_def principal_char_def divide_simps mult.commute)
  finally show "\<chi> (inv a) = cnj (\<chi> a)" .
qed

end

lemma (in finite_comm_group) character_principal [simp, intro]: "character G (principal_char G)"
  by standard (auto simp: principal_char_def)

lemmas [simp,intro] = finite_comm_group.character_principal

lemma character_ext:
  assumes "character G \<chi>" "character G \<chi>'" "\<And>x. x \<in> carrier G \<Longrightarrow> \<chi> x = \<chi>' x"
  shows   "\<chi> = \<chi>'"
proof
  fix x :: 'a
  show "\<chi> x = \<chi>' x"
    using assms by (cases "x \<in> carrier G") (auto simp: character.char_eq_0)
qed

lemma character_mult [intro]: 
  assumes "character G \<chi>" "character G \<chi>'"
  shows   "character G (\<lambda>x. \<chi> x * \<chi>' x)"
proof -
  interpret \<chi>: character G \<chi> by fact
  interpret \<chi>': character G \<chi>' by fact
  show ?thesis by standard (auto simp: \<chi>.char_eq_0)
qed
 

lemma character_inv_character_iff [simp]: "character G (inv_character \<chi>) \<longleftrightarrow> character G \<chi>"
proof
  assume "character G (inv_character \<chi>)"
  from character.inv_character [OF this] show "character G \<chi>" by simp
qed (auto simp: character.inv_character)


definition characters :: "('a, 'b) monoid_scheme \<Rightarrow> ('a \<Rightarrow> complex) set"  where
  "characters G = {\<chi>. character G \<chi>}"


subsection \<open>The Character group\<close>

text \<open>
  The characters of a finite abelian group $G$ form another group $\widehat{G}$, which is called
  its Pontryagin dual group. This generalises to the more general setting of locally compact
  abelian groups, but we restrict ourselves to the finite setting because it is much easier.
\<close>
definition Characters :: "('a, 'b) monoid_scheme \<Rightarrow> ('a \<Rightarrow> complex) monoid"
  where "Characters G = \<lparr> carrier = characters G, mult = (\<lambda>\<chi>\<^sub>1 \<chi>\<^sub>2 k. \<chi>\<^sub>1 k * \<chi>\<^sub>2 k),
                          one = principal_char G \<rparr>"

lemma carrier_Characters: "carrier (Characters G) = characters G"
  by (simp add: Characters_def)

lemma one_Characters: "one (Characters G) = principal_char G"
  by (simp add: Characters_def)

lemma mult_Characters: "mult (Characters G) \<chi>\<^sub>1 \<chi>\<^sub>2 = (\<lambda>a. \<chi>\<^sub>1 a * \<chi>\<^sub>2 a)"
  by (simp add: Characters_def)

context finite_comm_group
begin

sublocale principal: character G "principal_char G" ..

lemma finite_characters [intro]: "finite (characters G)"
proof (rule finite_subset)
  show "characters G \<subseteq> (\<lambda>f x. if x \<in> carrier G then f x else 0) ` 
                          Pi\<^sub>E (carrier G) (\<lambda>_. {z. z ^ order G = 1})" (is "_ \<subseteq> ?h ` ?Chars")
  proof (intro subsetI, goal_cases)
    case (1 \<chi>)
    then interpret \<chi>: character G \<chi> by (simp add: characters_def)
    have "?h (restrict \<chi> (carrier G)) \<in> ?h ` ?Chars"
      by (intro imageI) (auto simp: \<chi>.char_root')
    also have "?h (restrict \<chi> (carrier G)) = \<chi>" by (simp add: fun_eq_iff \<chi>.char_eq_0)
    finally show ?case .
  qed
  show "finite (?h ` ?Chars)"
    by (intro finite_imageI finite_PiE finite_roots_unity) (auto simp: Suc_le_eq)
qed

lemma finite_comm_group_Characters [intro]: "finite_comm_group (Characters G)"
proof
  fix \<chi> \<chi>' assume *: "\<chi> \<in> carrier (Characters G)" "\<chi>' \<in> carrier (Characters G)"
  from * interpret \<chi>: character G \<chi> by (simp_all add: characters_def carrier_Characters)
  from * interpret \<chi>': character G \<chi>' by (simp_all add: characters_def  carrier_Characters)
  have "character G (\<lambda>k. \<chi> k * \<chi>' k)"
    by standard (insert *, simp_all add: \<chi>.char_eq_0 one_Characters 
                                         mult_Characters characters_def  carrier_Characters)
  thus "\<chi> \<otimes>\<^bsub>Characters G\<^esub> \<chi>' \<in> carrier (Characters G)"
    by (simp add: characters_def one_Characters mult_Characters  carrier_Characters)
next
  have "character G (principal_char G)" ..
  thus "\<one>\<^bsub>Characters G\<^esub> \<in> carrier (Characters G)"
    by (simp add: characters_def one_Characters mult_Characters  carrier_Characters)
next
  fix \<chi> assume *: "\<chi> \<in> carrier (Characters G)"
  from * interpret \<chi>: character G \<chi> by (simp_all add: characters_def carrier_Characters)
  show "\<one>\<^bsub>Characters G\<^esub> \<otimes>\<^bsub>Characters G\<^esub> \<chi> = \<chi>" and "\<chi> \<otimes>\<^bsub>Characters G\<^esub> \<one>\<^bsub>Characters G\<^esub> = \<chi>"
    by (simp_all add: principal_char_def fun_eq_iff \<chi>.char_eq_0 one_Characters mult_Characters)
next
  have "\<chi> \<in> Units (Characters G)" if "\<chi> \<in> carrier (Characters G)" for \<chi>
  proof -
    from that interpret \<chi>: character G \<chi> by (simp add: characters_def carrier_Characters)
    have "\<chi> \<otimes>\<^bsub>Characters G\<^esub> inv_character \<chi> = \<one>\<^bsub>Characters G\<^esub>" and 
         "inv_character \<chi> \<otimes>\<^bsub>Characters G\<^esub> \<chi> = \<one>\<^bsub>Characters G\<^esub>"
      by (simp_all add: \<chi>.mult_inv_character mult_ac one_Characters mult_Characters)
    moreover from that have "inv_character \<chi> \<in> carrier (Characters G)"
      by (simp add: characters_def carrier_Characters)
    ultimately show ?thesis using that unfolding Units_def by blast
  qed
  thus "carrier (Characters G) \<subseteq> Units (Characters G)" ..
qed (auto simp: principal_char_def one_Characters mult_Characters carrier_Characters)

end

lemma (in character) character_in_order_1:
  assumes "order G = 1"
  shows   "\<chi> = principal_char G"
proof -
  from assms have "card (carrier G - {\<one>}) = 0"
    by (subst card_Diff_subset) (auto simp: order_def)
  hence "carrier G - {\<one>} = {}"
    by (subst (asm) card_0_eq) auto
  hence "carrier G = {\<one>}" by auto
  thus ?thesis
    by (intro ext) (simp_all add: principal_char_def char_eq_0)
qed

lemma (in finite_comm_group) characters_in_order_1:
  assumes "order G = 1"
  shows   "characters G = {principal_char G}"
  using character.character_in_order_1 [OF _ assms] by (auto simp: characters_def)

lemma (in character) inv_Characters: "inv\<^bsub>Characters G\<^esub> \<chi> = inv_character \<chi>"
proof -
  interpret Characters: finite_comm_group "Characters G" ..
  have "character G \<chi>" ..
  thus ?thesis
    by (intro Characters.inv_equality) 
       (auto simp: characters_def mult_inv_character mult_ac 
                   carrier_Characters one_Characters mult_Characters)
qed

lemma (in finite_comm_group) inv_Characters': 
  "\<chi> \<in> characters G \<Longrightarrow> inv\<^bsub>Characters G\<^esub> \<chi> = inv_character \<chi>"
  by (intro character.inv_Characters) (auto simp: characters_def)

lemmas (in finite_comm_group) Characters_simps = 
  carrier_Characters mult_Characters one_Characters inv_Characters'

lemma inv_Characters': "\<chi> \<in> characters G \<Longrightarrow> inv\<^bsub>Characters G\<^esub> \<chi> = inv_character \<chi>"
  using character.inv_Characters[of G \<chi>] by (simp add: characters_def)



subsection \<open>Relationship of characters and adjoining\<close>

text \<open>
  We now study the set of characters of two subgroups $H$ and $H_x$, where $x\in G\setminus H$
  and $H_x$ is the smallest supergroup of $H$ that contains \<open>x\<close>.

  Let $n$ denote the indicator of \<open>x\<close> in \<open>H\<close> (i.\,e.\ the smallest positive number such
  that $x^n\in H$) We show that any character on $H_x$ corresponds to a pair of
  a character \<open>\<chi>\<close> on \<open>H\<close> and an $n$-th root of $\chi(x^n)$ (or, equivalently, an $n$-th
  root of unity).
\<close>

context finite_comm_group_adjoin
begin

lemma lower_character:
  assumes "character (G\<lparr>carrier := adjoin G H a\<rparr>) \<chi>" 
    (is "character ?G'' _")
  shows   "character (G\<lparr>carrier := H\<rparr>) (\<lambda>x. if x \<in> H then \<chi> x else 0)" (is "character ?G' ?\<chi>")
proof -
  have "subgroup H G" ..
  then interpret G'': finite_comm_group ?G'' 
    by (intro subgroup_imp_finite_comm_group adjoin_subgroup) auto
  from \<open>subgroup H G\<close> interpret G': finite_comm_group ?G'
    by (intro subgroup_imp_finite_comm_group adjoin_subgroup) auto
  from assms interpret character ?G'' \<chi>
    by (simp add: characters_def)
  show ?thesis
  proof
    fix x y assume "x \<in> carrier ?G'" "y \<in> carrier ?G'"
    thus "?\<chi> (x \<otimes>\<^bsub>?G'\<^esub> y) = ?\<chi> x * ?\<chi> y"
      using char_mult[of x y] mem_adjoin[OF \<open>subgroup H G\<close>] by auto
  qed (insert char_one, auto simp del: char_one)
qed

definition lift_character :: "('a \<Rightarrow> complex) \<times> complex \<Rightarrow> ('a \<Rightarrow> complex)" where
  "lift_character = 
     (\<lambda>(\<chi>,z) x. if x \<in> adjoin G H a then \<chi> (fst (unadjoin x)) * z ^ snd (unadjoin x) else 0)"

lemma lift_character:
  defines "h \<equiv> subgroup_indicator G H a"
  assumes "character (G\<lparr>carrier := H\<rparr>) \<chi>" (is "character ?G' _") and "z ^ h = \<chi> (a [^] h)"
  shows   "character (G\<lparr>carrier := adjoin G H a\<rparr>) (lift_character (\<chi>, z))" (is "character ?G'' _")
proof -
  interpret H': subgroup "adjoin G H a" G by (intro adjoin_subgroup is_subgroup) auto
  have "subgroup H G" ..
  then interpret G'': finite_comm_group ?G''
    by (intro subgroup_imp_finite_comm_group adjoin_subgroup) auto
  from \<open>subgroup H G\<close> interpret G': finite_comm_group ?G'
    by (intro subgroup_imp_finite_comm_group adjoin_subgroup) auto
  from assms interpret character ?G' \<chi> by (simp add: characters_def)
  show ?thesis
  proof (standard, goal_cases)
    case 1
    from char_one show ?case
      by (auto simp: lift_character_def simp del: char_one)
  next
    case (2 x)
    thus ?case by (auto simp: lift_character_def)
  next
    case (3 x y)
    from 3(1) obtain x' k where x: "x' \<in> H" "x = x' \<otimes> a [^] k" and k: "k < h"
      by (auto simp: adjoin_def h_def)
    from 3(2) obtain y' l where y: "y' \<in> H" "y = y' \<otimes> a [^] l" and l: "l < h"
      by (auto simp: adjoin_def h_def)
    have [simp]: "unadjoin x = (x', k)" using x k by (intro unadjoin_unique') (auto simp: h_def)
    have [simp]: "unadjoin y = (y', l)" using y l by (intro unadjoin_unique') (auto simp: h_def)
    have char_mult': "\<chi> (x \<otimes> y) = \<chi> x * \<chi> y" if "x \<in> H" "y \<in> H" for x y
      using char_mult[of x y] that by simp
    have char_power': "\<chi> (x [^] n) = \<chi> x ^ n" if "x \<in> H" for x n
      using that char_one by (induction n) (simp_all add: char_mult' del: char_one)

    define r where "r = (k + l) mod h"
    have r: "r < subgroup_indicator G H a" unfolding h_def r_def
      by (intro mod_less_divisor subgroup_indicator_pos is_subgroup) auto
    define zz where "zz = (a [^] h) [^] ((k + l) div h)"
    have [simp]: "zz \<in> H" unfolding zz_def h_def 
      by (rule nat_pow_closed) (auto intro: pow_subgroup_indicator is_subgroup)
    have "a [^] k \<otimes> a [^] l = zz \<otimes> a [^] r"
      by (simp add: nat_pow_mult zz_def nat_pow_pow r_def)
    with x y r have "unadjoin (x \<otimes> y) = (x' \<otimes> y' \<otimes> zz, r)"
      by (intro unadjoin_unique' m_closed) (auto simp: m_ac)
    hence "lift_character (\<chi>, z) (x \<otimes>\<^bsub>?G''\<^esub> y) = \<chi> (x' \<otimes> y' \<otimes> zz) * z ^ r"
      using 3 by (simp add: lift_character_def)
    also have "\<dots> = \<chi> x' * \<chi> y' * (\<chi> zz * z ^ r)"
      using x(1) y(1) by (simp add: char_mult' char_power')
    also have "\<chi> zz * z ^ r = z ^ (h * ((k + l) div h) + r)"
      unfolding h_def zz_def using \<open>subgroup H G\<close> assms(3)[symmetric] 
      by (subst char_power') (auto simp: pow_subgroup_indicator h_def power_mult power_add)
    also have "h * ((k + l) div h) + r = k + l" by (simp add: r_def)
    also have "\<chi> x' * \<chi> y' * z ^ (k + l) = lift_character (\<chi>,z) x * lift_character (\<chi>,z) y"
      using 3 by (simp add: lift_character_def power_add)
    finally show ?case .
  qed
qed

lemma lower_character_lift_character:
  assumes "\<chi> \<in> characters (G\<lparr>carrier := H\<rparr>)"
  shows   "(\<lambda>x. if x \<in> H then lift_character (\<chi>, z) x else 0) = \<chi>" (is ?th1)
          "lift_character (\<chi>, z) a = z" (is ?th2)
proof -
  from assms interpret \<chi>: character "G\<lparr>carrier := H\<rparr>" \<chi> by (simp add: characters_def)
  have char_mult: "\<chi> (x \<otimes> y) = \<chi> x * \<chi> y" if "x \<in> H" "y \<in> H" for x y
    using \<chi>.char_mult[of x y] that by simp
  have char_power: "\<chi> (x [^] n) = \<chi> x ^ n" if "x \<in> H" for x n
    using \<chi>.char_one that by (induction n) (simp_all add: char_mult)
  show ?th1 using \<chi>.char_eq_0 mem_adjoin[OF is_subgroup _ a_in_carrier]
    by (auto simp: lift_character_def)
  show ?th2 using \<chi>.char_one is_subgroup
    by (auto simp: lift_character_def adjoined_in_adjoin)
qed

lemma lift_character_lower_character:
  assumes "\<chi> \<in> characters (G\<lparr>carrier := adjoin G H a\<rparr>)"
  shows   "lift_character (\<lambda>x. if x \<in> H then \<chi> x else 0, \<chi> a) = \<chi>"
proof -
  let ?G' = "G\<lparr>carrier := adjoin G H a\<rparr>"
  from assms interpret \<chi>: character ?G' \<chi> by (simp add: characters_def)
  show ?thesis
  proof (rule ext, goal_cases)
    case (1 x)
    show ?case
    proof (cases "x \<in> adjoin G H a")
      case True
      note * = unadjoin_correct[OF this]
      interpret H': subgroup "adjoin G H a" G
        by (intro adjoin_subgroup is_subgroup a_in_carrier)
      have "x = fst (unadjoin x) \<otimes>\<^bsub>?G'\<^esub> a [^]\<^bsub>?G'\<^esub> snd (unadjoin x)" 
        using *(3) by (simp add: nat_pow_def)
      also have "\<chi> \<dots> = \<chi> (fst (unadjoin x)) * \<chi> (a [^]\<^bsub>?G'\<^esub> snd (unadjoin x))"
        using * is_subgroup by (intro \<chi>.char_mult) 
                               (auto simp: nat_pow_modify_carrier mem_adjoin adjoined_in_adjoin)
      also have "\<chi> (a [^]\<^bsub>?G'\<^esub> snd (unadjoin x)) = \<chi> a ^ snd (unadjoin x)"
        using is_subgroup by (intro \<chi>.char_power) (auto simp: adjoined_in_adjoin)
      finally show ?thesis using True * by (auto simp: lift_character_def)
    qed (auto simp: lift_character_def \<chi>.char_eq_0)
  qed
qed

lemma lift_character_unchanged [simp]:
  assumes "x \<in> H"
  shows   "lift_character \<chi>z x = fst \<chi>z x"
  using assms mem_adjoin[of H x a] is_subgroup
  by (cases \<chi>z) (auto simp: lift_character_def)

lemma lift_character_adjoined [simp]:
 "character (G\<lparr>carrier := H\<rparr>) (fst \<chi>z) \<Longrightarrow> lift_character \<chi>z a = snd \<chi>z"
  using is_subgroup character.char_one[of "G\<lparr>carrier := H\<rparr>"]
  by (cases \<chi>z) (auto simp: lift_character_def adjoined_in_adjoin character.char_one)

lemma bij_betw_characters_adjoin:
  defines "h \<equiv> subgroup_indicator G H a"
  shows "bij_betw lift_character
                  (SIGMA \<chi>:characters (G\<lparr>carrier := H\<rparr>). {z. z ^ h = \<chi> (a [^] h)})
                  (characters (G\<lparr>carrier := adjoin G H a\<rparr>))"
proof (rule bij_betwI[where ?g = "\<lambda>\<chi>. (\<lambda>x. if x \<in> H then \<chi> x else 0, \<chi> a)"], goal_cases)
  case 1
  show ?case by (auto simp: characters_def h_def intro!: lift_character)
next
  case 2
  show ?case unfolding characters_def
  proof (safe, goal_cases)
    case (1 \<chi>)
    thus ?case unfolding h_def by (rule lower_character)
  next
    case (2 \<chi>)
    interpret \<chi>: character "G\<lparr>carrier := adjoin G H a\<rparr>" \<chi> by fact
    have [simp]: "\<chi> (a [^] n) = \<chi> a ^ n" for n using \<chi>.char_power[of a n] is_subgroup 
      by (auto simp: adjoined_in_adjoin nat_pow_def simp del: \<chi>.char_power)
    from is_subgroup a_in_carrier pow_subgroup_indicator show ?case
      by (auto simp: h_def intro!: subgroup_indicator_pos \<chi>.char_eq_0)
  qed
next
  case (3 w)
  thus ?case using lower_character_lift_character[of "fst w" "snd w"]
    by (auto cong: if_cong)
next
  case (4 \<chi>)
  thus ?case by (rule lift_character_lower_character)
qed

end


subsection \<open>Non-trivial facts about characters\<close>

context finite_comm_group
begin

text \<open>
  The following theorem is a very central one. It shows that any character on a subgroup \<open>H\<close> can
  be extended to a character on the full group in exactly $[G : H]$ ways.

  The proof is by induction; we start with \<open>H\<close> and then successively adjoin elements until we
  have reached \<open>G\<close>. As we showed before, when we lift a character from \<open>H\<close> to $H_x$, we have
  \<open>n\<close> choices to do so, where \<open>n\<close> is the indicator of \<open>x\<close> in \<open>H\<close>. Since $|H_x| = n |H|$, the
  induction step is valid.
\<close>
theorem card_character_extensions:
  assumes "subgroup H G" "character (G\<lparr>carrier := H\<rparr>) \<chi>"
  shows   "card {\<chi>'\<in>characters G. \<forall>x\<in>H. \<chi>' x = \<chi> x} * card H = order G"
  using assms
proof (induction rule: subgroup_adjoin_induct)
  case (base )
  have "{\<chi>' \<in> characters (G\<lparr>carrier := H\<rparr>). \<forall>x\<in>H. \<chi>' x = \<chi> x} = {\<chi>}"
    using base by (auto simp: fun_eq_iff characters_def intro: character_ext)
  thus ?case using base by (simp add: order_def)
next
  case (adjoin H' a )
  interpret H': subgroup H' G by fact
  interpret H': finite_comm_group "G\<lparr>carrier := H'\<rparr>"
    by (rule subgroup_imp_finite_comm_group) fact
  interpret H': finite_comm_group_adjoin G H' a
    using adjoin.hyps by unfold_locales auto

  define h where "h = subgroup_indicator G H' a"
  from adjoin have [simp]: "h > 0" unfolding h_def by (intro subgroup_indicator_pos) auto
  define c where "c = a [^] h"
  from adjoin have [simp]: "c \<in> H'"
    by (auto simp: c_def h_def pow_subgroup_indicator)

  define C where "C = (\<lambda>H'. {\<chi>'. \<chi>' \<in> characters (G\<lparr>carrier := H'\<rparr>) \<and> (\<forall>x\<in>H. \<chi>' x = \<chi> x)})"
  define I where "I = (\<lambda>\<chi>. {z::complex. z ^ h = \<chi> c})"
  have [simp]: "finite (C H')"
    by (rule finite_subset[OF _ H'.finite_characters]) (auto simp: C_def)

  (* TODO: extract lemma *)
  have "bij_betw H'.lift_character (SIGMA \<chi>:C H'. I \<chi>) (C (adjoin G H' a))"
  proof (rule bij_betwI)
    show "H'.lift_character \<in> Sigma (C H') I \<rightarrow> C (adjoin G H' a)"
    proof safe
      fix \<chi> z assume *: "\<chi> \<in> C H'" "z \<in> I \<chi>"
      have "\<forall>x\<in>H. H'.lift_character (\<chi>, z) x = \<chi> x"
        using * adjoin.hyps by auto
      with * show "H'.lift_character (\<chi>, z) \<in> C (adjoin G H' a)"
        using H'.lift_character[of \<chi> z]
        by (auto simp: C_def I_def h_def c_def characters_def)
    qed
  next
    show "(\<lambda>\<chi>. (\<lambda>x. if x \<in> H' then \<chi> x else 0, \<chi> a)) \<in> C (adjoin G H' a) \<rightarrow> Sigma (C H') I"
    proof safe
      fix \<chi> assume \<chi>: "\<chi> \<in> C (adjoin G H' a)"
      thus "(\<lambda>xa. if xa \<in> H' then \<chi> xa else 0) \<in> C H'"
        using H'.lower_character[of \<chi>] adjoin.prems adjoin.hyps
        by (auto simp: C_def characters_def character.char_eq_0)
      have "\<chi> (a [^]\<^bsub>G\<lparr>carrier := adjoin G H' a\<rparr>\<^esub> subgroup_indicator (G\<lparr>carrier := adjoin G H' a\<rparr>) H' a) =
              \<chi> a ^ subgroup_indicator (G\<lparr>carrier := adjoin G H' a\<rparr>) H' a"
        using \<chi> adjoin.prems adjoin.hyps
        by (intro character.char_power) (auto simp: C_def characters_def adjoined_in_adjoin)
      hence "\<chi> (a [^] h) = \<chi> a ^ subgroup_indicator G H' a"
        by (simp add: nat_pow_consistent [symmetric] h_def)
      with \<chi> show "\<chi> a \<in> I (\<lambda>xa. if xa \<in> H' then \<chi> xa else 0)"
        using adjoin.hyps adjoin.prems
        by (auto simp: I_def C_def characters_def character.char_power character.char_eq_0
                       pow_subgroup_indicator h_def c_def)
    qed
  next
    fix \<chi>z assume *: "\<chi>z \<in> (SIGMA \<chi>:C H'. I \<chi>)"
    obtain \<chi> z where [simp]: "\<chi>z = (\<chi>, z)" by (cases \<chi>z)
    from * show "(\<lambda>xa. if xa \<in> H' then H'.lift_character \<chi>z xa else 0, H'.lift_character \<chi>z a) = \<chi>z"
      using H'.lower_character_lift_character[of \<chi> z] by (auto simp: C_def cong: if_cong)
  next
    fix \<chi> assume "\<chi> \<in> C (adjoin G H' a)"
    thus "H'.lift_character (\<lambda>x. if x \<in> H' then \<chi> x else 0, \<chi> a) = \<chi>"
      using H'.lift_character_lower_character[of \<chi>] by (auto simp: C_def)
  qed

  hence "card (SIGMA \<chi>:C H'. I \<chi>) = card (C (adjoin G H' a))"
    by (rule bij_betw_same_card)
  also have "card (SIGMA \<chi>:C H'. I \<chi>) = (\<Sum>a\<in>C H'. card (I a))"
    by (intro card_SigmaI) (auto simp: I_def)
  also have "\<dots> = (\<Sum>a\<in>C H'. h)"
  proof (intro sum.cong refl, goal_cases)
    case (1 \<chi>)
    then interpret character "G\<lparr>carrier := H'\<rparr>" \<chi> by (simp add: characters_def C_def)
    have "\<chi> c \<noteq> 0"
      by (subst char_eq_0_iff) (auto simp: c_def h_def intro!: pow_subgroup_indicator adjoin)
    thus ?case by (simp add: I_def card_nth_roots)
  qed
  also have "\<dots> = h * card (C H')" by simp
  finally have "card (C (adjoin G H' a)) * card H = h * (card (C H') * card H)"
    by simp
  also have "card (C H') * card H = card H'"
    unfolding C_def using adjoin.prems by (subst adjoin.IH) (auto simp: order_def)
  also have "h * card H' = card (adjoin G H' a)"
    using adjoin.hyps by (subst card_adjoin) (auto simp: h_def)
  also have "\<dots> = order (G\<lparr>carrier := adjoin G H' a\<rparr>)"
    by (simp add: order_def)
  finally show ?case by (simp add: C_def)
qed

text \<open>
  By taking \<open>H\<close> to be the trivial subgroup, we obtain that the number of characters
  on \<open>G\<close> is precisely the order of \<open>G\<close> itself, i.\,e.\ $|\widehat{G}|=|G|$.
\<close>
corollary card_characters: "card (characters G) = order G"
proof -
  define \<chi> where "\<chi> = principal_char (G\<lparr>carrier := {\<one>}\<rparr>)"
  interpret triv: subgroup "{\<one>}"
    by standard auto
  interpret triv: finite_comm_group "G\<lparr>carrier := {\<one>}\<rparr>"
    by (rule subgroup_imp_finite_comm_group) (rule triv.is_subgroup)
  
  have "card {\<chi>'\<in>characters G. \<forall>x\<in>{\<one>}. \<chi>' x = \<chi> x} * card {\<one>} = order G"
    unfolding \<chi>_def
    by (intro card_character_extensions triv.is_subgroup triv.character_principal)
  also have "{\<chi>'\<in>characters G. \<forall>x\<in>{\<one>}. \<chi>' x = \<chi> x} = characters G"
    by (auto simp: characters_def character.char_one principal_char_def \<chi>_def)
  finally show ?thesis by simp
qed

lemma order_Characters [simp]: "order (Characters G) = order G"
  by (simp add: order_def card_characters carrier_Characters)

text \<open>
  It also follows as a simple corollary that any character on \<open>H\<close> \<^emph>\<open>can\<close> be extended
  to a character on \<open>G\<close>.
\<close>
corollary character_extension_exists:
  assumes "subgroup H G" "character (G\<lparr>carrier := H\<rparr>) \<chi>"
  obtains \<chi>' where "character G \<chi>'" and "\<And>x. x \<in> H \<Longrightarrow> \<chi>' x = \<chi> x"
proof -
  have "card {\<chi>'\<in>characters G. \<forall>x\<in>H. \<chi>' x = \<chi> x} * card H = order G"
    by (intro card_character_extensions assms)
  hence "card {\<chi>'\<in>characters G. \<forall>x\<in>H. \<chi>' x = \<chi> x} \<noteq> 0"
    using order_gt_0 by (intro notI) auto
  hence "{\<chi>'\<in>characters G. \<forall>x\<in>H. \<chi>' x = \<chi> x} \<noteq> {}"
    by (intro notI) simp
  then obtain \<chi>' where "character G \<chi>'" and "\<And>x. x \<in> H \<Longrightarrow> \<chi>' x = \<chi> x"
    unfolding characters_def by blast
  thus ?thesis using that[of \<chi>'] by blast
qed

text \<open>
  Lastly, we can also show that for each $x\in H$ of order $n > 1$ and each \<open>n\<close>-th root of
  unity \<open>z\<close>, there exists a character \<open>\<chi>\<close> on \<open>G\<close> such that $\chi(x) = z$.
\<close>
corollary character_with_value_exists:
  assumes "x \<in> carrier G" and "x \<noteq> \<one>" and "z ^ ord x = 1"
  obtains \<chi> where "character G \<chi>" and "\<chi> x = z"
proof -
  define triv where "triv = G\<lparr>carrier := {\<one>}\<rparr>"
  interpret triv: subgroup "{\<one>}"
    by standard auto
  interpret triv: finite_comm_group "G\<lparr>carrier := {\<one>}\<rparr>"
    by (rule subgroup_imp_finite_comm_group) (rule triv.is_subgroup)
  interpret H: finite_comm_group_adjoin G "{\<one>}" x
    using assms by unfold_locales auto

  define h where "h = subgroup_indicator G {\<one>} x"
  have x_pow_h: "x [^] h = \<one>"
    using pow_subgroup_indicator[OF triv.is_subgroup assms(1)] by (simp add: h_def)
  have "h > 0"
    using subgroup_indicator_pos[OF triv.is_subgroup assms(1)] by (simp add: h_def)
  have [simp]: "ord x = h"
    using x_pow_h triv.is_subgroup assms \<open>h > 0\<close> unfolding h_def
    by (intro antisym subgroup_indicator_le_ord ord_min) auto

  define \<chi> where "\<chi> = principal_char triv"
  define \<chi>' where "\<chi>' = H.lift_character (\<chi>, z)"
  have "subgroup (adjoin G {\<one>} x) G"
    by (intro adjoin_subgroup triv.is_subgroup assms)
  moreover have \<chi>': "character (G\<lparr>carrier := adjoin G {\<one>} x\<rparr>) \<chi>'"
    using H.lift_character[of \<chi> z] triv.character_principal assms x_pow_h
    by (auto simp: \<chi>'_def \<chi>_def principal_char_def triv_def h_def)
  ultimately obtain \<chi>'' where \<chi>'': "character G \<chi>''" "\<And>y. y \<in> adjoin G {\<one>} x \<Longrightarrow> \<chi>'' y = \<chi>' y"
    by (erule character_extension_exists)
  moreover {
    have "\<chi>'' x = \<chi>' x"
      using \<chi>''(2)[of x] assms triv.is_subgroup by (auto simp: adjoined_in_adjoin)
    also have "\<chi>' x = z"
      unfolding \<chi>'_def by (subst H.lift_character_adjoined) (simp_all add: \<chi>_def triv_def)
    finally have "\<chi>'' x = z" .
  }
  ultimately show ?thesis using that[of \<chi>''] by blast
qed

text \<open>
  In particular, for any \<open>x\<close> that is not the identity element, there exists a character \<open>\<chi>\<close>
  such that $\chi(x)\neq 1$.
\<close>
corollary character_neq_1_exists:
  assumes "x \<in> carrier G" and "x \<noteq> \<one>"
  obtains \<chi> where "character G \<chi>" and "\<chi> x \<noteq> 1"
proof -
  define z where "z = cis (2 * pi / ord x)"
  have z_pow_h: "z ^ ord x = 1"
    by (auto simp: z_def DeMoivre)

  from assms have "ord x \<ge> 1" by (intro ord_ge_1) auto
  moreover have "ord x \<noteq> 1"
    using pow_ord_eq_1[of x] assms fin by (intro notI) simp_all
  ultimately have "ord x > 1" by linarith

  have [simp]: "z \<noteq> 1"
  proof
    assume "z = 1"
    have "bij_betw (\<lambda>k. cis (2 * pi * real k / real (ord x))) {..<ord x} {z. z ^ ord x = 1}"
      using \<open>ord x > 1\<close> by (intro bij_betw_roots_unity) auto
    hence inj: "inj_on (\<lambda>k. cis (2 * pi * real k / real (ord x))) {..<ord x}"
      by (auto simp: bij_betw_def)
    have "0 = (1 :: nat)"
      using \<open>z = 1\<close> and \<open>ord x > 1\<close> by (intro inj_onD[OF inj]) (auto simp: z_def)
    thus False by simp
  qed

  obtain \<chi> where "character G \<chi>" and "\<chi> x = z"
    using character_with_value_exists[OF assms z_pow_h] .
  thus ?thesis using that[of \<chi>] by simp
qed 

end


subsection \<open>The first orthogonality relation\<close>

text \<open>
  The entries of any non-principal character sum to 0.
\<close>
theorem (in character) sum_character:
  "(\<Sum>x\<in>carrier G. \<chi> x) = (if \<chi> = principal_char G then of_nat (order G) else 0)"
proof (cases "\<chi> = principal_char G")
  case True
  hence "(\<Sum>x\<in>carrier G. \<chi> x) = (\<Sum>x\<in>carrier G. 1)"
    by (intro sum.cong) (auto simp: principal_char_def)
  also have "\<dots> = order G" by (simp add: order_def)
  finally show ?thesis using True by simp
next
  case False
  define S where "S = (\<Sum>x\<in>carrier G. \<chi> x)"
  from False obtain y where y: "y \<in> carrier G" "\<chi> y \<noteq> 1"
    by (auto simp: principal_char_def fun_eq_iff char_eq_0_iff split: if_splits)
  from y have "S = (\<Sum>x\<in>carrier G. \<chi> (y \<otimes> x))" unfolding S_def
    by (intro sum.reindex_bij_betw [symmetric] bij_betw_mult_left)
  also have "\<dots> = (\<Sum>x\<in>carrier G. \<chi> y * \<chi> x)"
    by (intro sum.cong refl char_mult y)
  also have "\<dots> = \<chi> y * S" by (simp add: S_def sum_distrib_left)
  finally have "(\<chi> y - 1) * S = 0" by (simp add: algebra_simps)
  with y have "S = 0" by simp
  with False show ?thesis by (simp add: S_def)
qed

corollary (in finite_comm_group) character_orthogonality1:
  assumes "character G \<chi>" and "character G \<chi>'"
  shows   "(\<Sum>x\<in>carrier G. \<chi> x * cnj (\<chi>' x)) = (if \<chi> = \<chi>' then of_nat (order G) else 0)"
proof -
  define C where [simp]: "C = Characters G"
  interpret C: finite_comm_group C unfolding C_def
    by (rule finite_comm_group_Characters)
  let ?\<chi> = "\<lambda>x. \<chi> x * inv_character \<chi>' x"
  interpret character G "\<lambda>x. \<chi> x * inv_character \<chi>' x"
    by (intro character_mult character.inv_character assms)
  have "(\<Sum>x\<in>carrier G. \<chi> x * cnj (\<chi>' x)) = (\<Sum>x\<in>carrier G. ?\<chi> x)"
    by (intro sum.cong) (auto simp: inv_character_def)
  also have "\<dots> = (if ?\<chi> = principal_char G then of_nat (order G) else 0)"
    by (rule sum_character)
  also have "?\<chi> = principal_char G \<longleftrightarrow> \<chi> \<otimes>\<^bsub>C\<^esub> inv\<^bsub>C\<^esub> \<chi>' = \<one>\<^bsub>C\<^esub>"
    using assms by (simp add: Characters_simps characters_def)
  also have "\<dots> \<longleftrightarrow> \<chi> = \<chi>'"
  proof
    assume "\<chi> \<otimes>\<^bsub>C\<^esub> inv\<^bsub>C\<^esub> \<chi>' = \<one>\<^bsub>C\<^esub>"
    from C.inv_equality [OF this] and assms show "\<chi> = \<chi>'"
      by (auto simp: characters_def Characters_simps)
  next
    assume *: "\<chi> = \<chi>'"
    from assms show "\<chi> \<otimes>\<^bsub>C\<^esub> inv\<^bsub>C\<^esub> \<chi>' = \<one>\<^bsub>C\<^esub>" 
      by (subst *, intro C.r_inv) (auto simp: carrier_Characters characters_def)
  qed
  finally show ?thesis .
qed


subsection \<open>The isomorphism between a group and its double dual\<close>

text \<open>
  Lastly, we show that the double dual of a finite abelian group is naturally isomorphic
  to the original group via the obvious isomorphism $x\mapsto (\chi\mapsto \chi(x))$.
  It is easy to see that this is a homomorphism and that it is injective. The fact 
  $|\widehat{\widehat{G}}| = |\widehat{G}| = |G|$ then shows that it is also surjective.
\<close>
context finite_comm_group
begin

definition double_dual_iso :: "'a \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> complex" where
  "double_dual_iso x = (\<lambda>\<chi>. if character G \<chi> then \<chi> x else 0)"

lemma double_dual_iso_apply [simp]: "character G \<chi> \<Longrightarrow> double_dual_iso x \<chi> = \<chi> x"
  by (simp add: double_dual_iso_def)

lemma character_double_dual_iso [intro]:
  assumes x: "x \<in> carrier G"
  shows   "character (Characters G) (double_dual_iso x)"
proof -
  interpret G': finite_comm_group "Characters G"
    by (rule finite_comm_group_Characters)
  show "character (Characters G) (double_dual_iso x)"
    using x by unfold_locales (auto simp: double_dual_iso_def characters_def Characters_def
                                              principal_char_def character.char_eq_0)
qed

lemma double_dual_iso_mult [simp]:
  assumes "x \<in> carrier G" "y \<in> carrier G"
  shows   "double_dual_iso (x \<otimes> y) =
             double_dual_iso x \<otimes>\<^bsub>Characters (Characters G)\<^esub> double_dual_iso y"
  using assms by (auto simp: double_dual_iso_def Characters_def fun_eq_iff character.char_mult)

lemma double_dual_iso_one [simp]:
  "double_dual_iso \<one> = principal_char (Characters G)"
  by (auto simp: fun_eq_iff double_dual_iso_def principal_char_def
                 carrier_Characters characters_def character.char_one)

lemma inj_double_dual_iso: "inj_on double_dual_iso (carrier G)"
proof -
  interpret G': finite_comm_group "Characters G"
    by (rule finite_comm_group_Characters)
  interpret G'': finite_comm_group "Characters (Characters G)"
    by (rule G'.finite_comm_group_Characters)
  have hom: "double_dual_iso \<in> hom G (Characters (Characters G))"
    by (rule homI) (auto simp: carrier_Characters characters_def)
  have inj_aux: "x = \<one>"
    if x: "x \<in> carrier G" "double_dual_iso x = \<one>\<^bsub>Characters (Characters G)\<^esub>" for x
  proof (rule ccontr)
    assume "x \<noteq> \<one>"
    obtain \<chi> where \<chi>: "character G \<chi>" "\<chi> x \<noteq> 1"
      using character_neq_1_exists[OF x(1) \<open>x \<noteq> \<one>\<close>] .
    from x have "\<forall>\<chi>. (if \<chi> \<in> characters G then \<chi> x else 0) = (if \<chi> \<in> characters G then 1 else 0)"
      by (auto simp: double_dual_iso_def Characters_def fun_eq_iff
                     principal_char_def characters_def)
    hence eq1: "\<forall>\<chi>\<in>characters G. \<chi> x = 1" by metis
    with \<chi> show False unfolding characters_def by auto
  qed
  thus ?thesis
    using inj_aux hom is_group G''.is_group by (subst inj_on_one_iff') auto
qed

lemma double_dual_iso_eq_iff [simp]:
  "x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> double_dual_iso x = double_dual_iso y \<longleftrightarrow> x = y"
  by (auto dest: inj_onD[OF inj_double_dual_iso])

theorem double_dual_iso: "double_dual_iso \<in> iso G (Characters (Characters G))"
proof (rule isoI)
  interpret G': finite_comm_group "Characters G"
    by (rule finite_comm_group_Characters)
  interpret G'': finite_comm_group "Characters (Characters G)"
    by (rule G'.finite_comm_group_Characters)

  show hom: "double_dual_iso \<in> hom G (Characters (Characters G))"
    by (rule homI) (auto simp: carrier_Characters characters_def)

  show "bij_betw double_dual_iso (carrier G) (carrier (Characters (Characters G)))"
    unfolding bij_betw_def
  proof
    show "inj_on double_dual_iso (carrier G)" by (fact inj_double_dual_iso)
  next
    show "double_dual_iso ` carrier G = carrier (Characters (Characters G))"
    proof (rule card_subset_eq)
      show "finite (carrier (Characters (Characters G)))"
        by (fact G''.fin)
    next
      have "card (carrier (Characters (Characters G))) = card (carrier G)"
        by (simp add: carrier_Characters G'.card_characters card_characters order_def)
      also have "\<dots> = card (double_dual_iso ` carrier G)"
        by (intro card_image [symmetric] inj_double_dual_iso)
      finally show "card (double_dual_iso ` carrier G) =
                      card (carrier (Characters (Characters G)))" ..
    next
      show "double_dual_iso ` carrier G \<subseteq> carrier (Characters (Characters G))"
        using hom by (auto simp: hom_def)
    qed
  qed
qed

lemma double_dual_is_iso: "Characters (Characters G) \<cong> G"
  by (rule iso_sym) (use double_dual_iso in \<open>auto simp: is_iso_def\<close>)

text \<open>
  The second orthogonality relation follows from the first one via Pontryagin duality:
\<close>
theorem sum_characters:
  assumes x: "x \<in> carrier G"
  shows   "(\<Sum>\<chi>\<in>characters G. \<chi> x) = (if x = \<one> then of_nat (order G) else 0)"
proof -
  interpret G': finite_comm_group "Characters G"
    by (rule finite_comm_group_Characters)
  interpret x: character "Characters G" "double_dual_iso x"
    using x by auto
  from x.sum_character show ?thesis using double_dual_iso_eq_iff[of x \<one>] x
    by (auto simp: characters_def carrier_Characters simp del: double_dual_iso_eq_iff)
qed

corollary character_orthogonality2:
  assumes "x \<in> carrier G" "y \<in> carrier G"
  shows   "(\<Sum>\<chi>\<in>characters G. \<chi> x * cnj (\<chi> y)) = (if x = y then of_nat (order G) else 0)"
proof -
  from assms have "(\<Sum>\<chi>\<in>characters G. \<chi> x * cnj (\<chi> y)) = (\<Sum>\<chi>\<in>characters G. \<chi> (x \<otimes> inv y))"
    by (intro sum.cong) (simp_all add: character.char_inv character.char_mult characters_def)
  also from assms have "\<dots> = (if x \<otimes> inv y = \<one> then of_nat (order G) else 0)"
    by (intro sum_characters) auto
  also from assms have "x \<otimes> inv y = \<one> \<longleftrightarrow> x = y"
    using inv_equality[of x "inv y"] by auto
  finally show ?thesis .
qed

end

end
