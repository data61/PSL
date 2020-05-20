section\<open>Finite Strings\<close>
text\<open>Finite-String.thy implements a type of strings whose lengths are bounded by a constant defined
    at "proof-time", by taking a sub-type of the built-in string type. A finite length bound is
    important for applications in real analysis, specifically the Differential-Dynamic-Logic (dL) 
    entry, because finite-string identifiers are used as the index of a real vector, only forming a
    Euclidean space if identifiers are finite.

    We include finite strings in this AFP entry both to promote using it as the basis of future
    versions of the dL entry and simply in case the typeclass instances herein are useful. One could
    imagine using this type in file formats with fixed-length fields.\<close>
(*  Author:     Brandon Bohrer*)

theory "Finite_String"
  imports 
    Main 
    "HOL-Library.Code_Target_Int"
begin

text\<open>This theory uses induction on pairs of lists often: give names to the cases\<close>
lemmas list_induct2'[case_names BothNil LeftCons RightCons BothCons] = List.list_induct2'

text\<open>Set a hard-coded global maximum string length\<close>
definition max_str:"MAX_STR = 20"

text\<open>Finite strings are strings whose size is within the maximum\<close>
typedef fin_string = "{s::string. size s \<le> MAX_STR}"
  morphisms Rep_fin_string Abs_fin_string
  apply(auto)
  apply(rule exI[where x=Nil])
  by(auto simp add: max_str)

text\<open>Lift definition of string length\<close>
setup_lifting  Finite_String.fin_string.type_definition_fin_string 
lift_definition ilength::"fin_string \<Rightarrow> nat" is length done

text\<open>Product of types never decreases cardinality\<close>
lemma card_prod_finite:
  fixes C:: "char set" and S::"string set"
  assumes C:"card C \<ge> 1" and S:"card S \<ge> 0"
  shows "card C * card S \<ge> card S"
  using C S by auto

fun cons :: "('a * 'a list) \<Rightarrow> 'a list" 
  where "cons (x,y) = x # y"

text\<open>Finite strings are finite\<close>
instantiation fin_string :: finite begin
instance proof 
  have any:"\<forall>i::nat. card {s::string. length s \<le> i} > 0"
    apply(auto)
    subgoal for i
  proof (induct i)
    case 0
    then show ?case by auto
  next
    case (Suc k)
    assume IH:"card {s::string. length s \<le> k} > 0"
    let ?c = "(UNIV::char set)"
    let ?ih = "{s::string. length s \<le> k}"
    let ?prod = "(?c \<times> ?ih)"
    let ?b = "(cons ` ?prod)"
    let ?A = "{s::string. length s \<le> Suc k}"
    let ?B = "insert [] ?b"
    have IHfin:"finite ?ih" using IH card_ge_0_finite by blast
    have finChar:"finite ?c" using card_ge_0_finite finite_code by blast
    have finiteProd:"finite ?prod"
      using Groups_Big.card_cartesian_product IHfin finChar by auto
    have cardCons:"card ?b = card ?prod"
      apply(rule Finite_Set.card_image)
      by(auto simp add: inj_on_def) 
    have finiteCons:"finite ?b" using cardCons finiteProd card_ge_0_finite by blast
    have finiteB:"finite ?B" using finite_insert finiteCons by auto
    have lr:"\<And>x. x \<in> ?A \<Longrightarrow> x \<in> ?B" subgoal for x
      apply(auto) apply(cases x) apply auto 
      by (metis UNIV_I cons.simps image_eqI mem_Collect_eq mem_Sigma_iff) done
    have rl:"\<And>x. x \<in> ?B \<Longrightarrow> x \<in> ?A" subgoal for x
      by(auto) done
    have isCons:"?A = ?B"
      using lr rl by auto
  show ?case
      using finiteB isCons IH by (simp add: card_insert)
  qed
  done 
  note finMax = card_ge_0_finite[OF spec[OF any, of MAX_STR]]
  have fin:"finite {x | x y . x = Abs_fin_string y \<and> y \<in> {s. length s \<le> MAX_STR}}"
    using Abs_fin_string_cases finMax by auto
  have univEq:"UNIV = {x | x y . x = Abs_fin_string y \<and> y \<in> {s. length s \<le> MAX_STR}}"
    using Abs_fin_string_cases  
    by (metis (mono_tags, lifting) Collect_cong UNIV_I top_empty_eq top_set_def)
  then have "finite (UNIV :: fin_string set)" using univEq fin by auto
  then show "finite (UNIV::fin_string set)" by auto
qed
end

text\<open>Characters are linearly ordered by their code value\<close>
instantiation char :: linorder begin
definition less_eq_char where
less_eq_char[code]:"less_eq_char x  y \<equiv> int_of_char x \<le> int_of_char y"
definition less_char where
less_char[code]:"less_char x y \<equiv> int_of_char x < int_of_char y"
instance
  by(standard, auto simp add: less_char less_eq_char int_of_char_def)+
end

text\<open>Finite strings are linearly ordered, lexicographically\<close>
instantiation fin_string :: linorder begin
fun lleq_charlist :: "char list \<Rightarrow> char list \<Rightarrow> bool"
  where 
  "lleq_charlist Nil Nil = True"
| "lleq_charlist Nil _ = True"
| "lleq_charlist _ Nil = False"
| "lleq_charlist (x # xs)(y # ys) = 
   (if x = y then lleq_charlist xs ys else x < y)"

fun less_charlist :: "char list \<Rightarrow> char list \<Rightarrow> bool"
  where 
  "less_charlist Nil Nil = False"
| "less_charlist Nil _ = True"
| "less_charlist _ Nil = False"
| "less_charlist (x # xs)(y # ys) = 
   (if x = y then less_charlist xs ys else x < y)"

lift_definition less_eq_fin_string::"fin_string \<Rightarrow> fin_string \<Rightarrow> bool" is lleq_charlist done
lift_definition less_fin_string::"fin_string \<Rightarrow> fin_string \<Rightarrow> bool" is less_charlist done

lemma lleq_head:
  fixes L1 L2 x
  assumes a:
  "(\<And>z. lleq_charlist L2 z \<Longrightarrow> lleq_charlist L1 z)"
  "lleq_charlist L1 L2"
  "lleq_charlist (x # L2) w"
  shows "lleq_charlist (x # L1) w"
  using a by(induction arbitrary: x rule: List.list_induct2', auto)

lemma lleq_less:
  fixes x y
  shows "(less_charlist x y) = (lleq_charlist x y \<and> \<not> lleq_charlist y  x)"
  by(induction rule: List.list_induct2', auto)

lemma lleq_refl:
  fixes x
  shows "lleq_charlist x x"
  by(induction x, auto)

lemma lleq_trans:
  fixes x y z
  shows "lleq_charlist x y \<Longrightarrow> lleq_charlist y z \<Longrightarrow> lleq_charlist x z"
proof(induction arbitrary: z rule: list_induct2') 
  case BothNil
  then show ?case  by auto
next
  case (LeftCons x xs)
  then show ?case 
    apply(induction y)
    using lleq_charlist.elims(2) lleq_charlist.simps(2) by blast+
next
  case (RightCons y ys)
  then show ?case by auto
next
  case (BothCons x xs y ys z)
  then show ?case 
    using lleq_head[of xs ys x z] apply(cases "x = y", auto)
    apply(cases z, auto)
    subgoal for a list
    by(cases "x = a", auto)
    done
qed

lemma lleq_antisym:
  fixes x y
  shows "lleq_charlist x y \<Longrightarrow> lleq_charlist y x \<Longrightarrow> x = y"
proof(induction rule: list_induct2')
     case (LeftCons x xs)      then show ?case by(cases "xs=y",auto)
next case (RightCons y ys)     then show ?case by(cases "x=ys",auto)
next case (BothCons x xs y ys) then show ?case by(cases "x=y", auto)
qed (auto)

lemma lleq_dichotomy:
  fixes x y
  shows "lleq_charlist x y \<or> lleq_charlist y x"
  by(induction rule: List.list_induct2',auto)

instance
  apply(standard)
      unfolding less_eq_fin_string_def less_fin_string_def
      apply (auto simp add: lleq_less lleq_refl lleq_trans lleq_dichotomy)
  using lleq_antisym less_eq_fin_string_def less_fin_string_def Rep_fin_string_inject by blast
end

fun string_expose::"string \<Rightarrow> (unit + (char * string))"
  where "string_expose Nil = Inl ()"
  | "string_expose (c#cs) = Inr(c,cs)"

fun string_cons::"char \<Rightarrow> string \<Rightarrow> string"
  where "string_cons c s = (if length s \<ge> MAX_STR then s else c # s)" 

lift_definition fin_string_empty::fin_string is "''''" by(auto simp add: max_str)
lift_definition fin_string_cons::"char \<Rightarrow> fin_string \<Rightarrow> fin_string" is "string_cons" by auto
lift_definition fin_string_expose::"fin_string \<Rightarrow> (unit + (char*fin_string))" is string_expose 
  apply(auto simp add: dual_order.trans less_imp_le pred_sum.simps string_expose.elims)
  by (metis dual_order.trans impossible_Cons le_cases string_expose.elims)


text\<open>Helper functions for enum typeclass instance\<close>
fun fin_string_upto :: "nat \<Rightarrow> fin_string list"
  where 
  "fin_string_upto 0 = [fin_string_empty]"
| "fin_string_upto (Suc k) = 
 (let r = fin_string_upto k in
  let ab =  (enum_class.enum::char list) in
  fin_string_empty # concat (map (\<lambda> c. map (\<lambda>s. fin_string_cons c  s) r) ab))"

lemma mem_appL:"List.member L1 x \<Longrightarrow> List.member (L1 @ L2) x"
  apply(induction L1 arbitrary: L2)
  by(auto simp add: member_rec)

lemma mem_appR:"List.member L2 x \<Longrightarrow> List.member (L1 @ L2) x"
  apply(induction L1 arbitrary: L2)
  by(auto simp add: member_rec)

lemma mem_app_or:"List.member (L1 @ L2) x = List.member L1 x \<or> List.member L2 x"
  unfolding member_def by auto

lemma fin_string_nil:
  fixes n
  shows "List.member (fin_string_upto n) fin_string_empty"
  by(induction n, auto simp add: member_rec Let_def fin_string_empty_def)

text\<open>List of every string. Not practical for code generation but used to show strings are an enum\<close>
definition vals_def[code]:"vals \<equiv> fin_string_upto MAX_STR"

definition fin_string_enum :: "fin_string list" 
  where "fin_string_enum = vals"
definition fin_string_enum_all :: "(fin_string \<Rightarrow> bool) \<Rightarrow> bool"
  where "fin_string_enum_all = (\<lambda> f. list_all f vals)"
definition fin_string_enum_ex :: "(fin_string \<Rightarrow> bool) \<Rightarrow> bool"
  where "fin_string_enum_ex = (\<lambda> f. list_ex f vals)"

text\<open>Induct on the length of a bounded list, with access to index of element\<close>
lemma length_induct:
  fixes P
  assumes len:"length L \<le> MAX_STR"
  assumes BC:"P [] 0"
  assumes IS:"(\<And>k x xs.  P xs k \<Longrightarrow> P ((x # xs)) (Suc k))"
  shows "P L (length L)"
  proof -
    have "\<And>k.  length L = k \<Longrightarrow> k \<le> MAX_STR \<Longrightarrow> P L (length L)" 
    proof (induction L)
      case Nil then show ?case using BC by auto
    next
      case (Cons a L)
      then have it:"P (L) (length L)" using less_imp_le by fastforce
      then show ?case  using IS[OF it, of a] by (auto)
    qed
  then show ?thesis using BC IS len by auto
  qed

text\<open>Induct on length of fin-string\<close>
lemma ilength_induct:
  fixes P
  assumes BC:"P fin_string_empty 0"
  assumes IS:"(\<And>k x xs.  P xs k \<Longrightarrow> P (Abs_fin_string (x # Rep_fin_string xs)) (Suc k))"
  shows  "P L (ilength L)"
  apply(cases L)
  apply(unfold ilength_def)
  apply(auto simp add: Abs_fin_string_inverse)
  subgoal for y
  proof -
    assume a1:"L = Abs_fin_string y"
    assume a2:" length y \<le> MAX_STR "
    have main:"\<And>k. L = Abs_fin_string y \<Longrightarrow> length y = k \<Longrightarrow> k \<le> MAX_STR 
        \<Longrightarrow> P (Abs_fin_string y) (length y)" 
      subgoal for k
        apply(induction y arbitrary: k L)
        subgoal for k using BC unfolding fin_string_empty_def by auto
        subgoal for a y k L
        proof -
          assume IH:"(\<And>k L. L = Abs_fin_string y \<Longrightarrow> length y = k \<Longrightarrow> k \<le> MAX_STR 
            \<Longrightarrow> P (Abs_fin_string y) (length y))"
          assume L:"L = Abs_fin_string (a # y)"
          assume l:"length (a # y) = k"
          assume str:"k \<le> MAX_STR"
          have yLen:"length y < MAX_STR" using l str by auto
          have it:"P (Abs_fin_string y) (length y)" 
            using IH[of "Abs_fin_string y" "k-1", OF refl] using L l str by auto
          show  "P (Abs_fin_string (a # y)) (length (a # y))"
            using IS[OF it, of a] apply (auto simp add: fin_string_cons_def Abs_fin_string_inverse)
            apply(cases "MAX_STR \<le> length (Rep_fin_string (Abs_fin_string y))")
            using yLen by(auto simp add: l yLen Abs_fin_string_inverse)
        qed
        done
      done
    show ?thesis
      apply(rule main)
      using BC IS a1 a2 by auto
  qed
  done

lemma enum_chars:"set (enum_class.enum::char list)= UNIV"
  using Enum.enum_class.enum_UNIV by auto

lemma member_concat:"List.member (concat LL) x = (\<exists>L. List.member LL L \<and> List.member L x)"
  by(auto simp add: member_def)

text\<open>fin-string-upto k enumerates all strings up to length $min(k,MAX\_STR)$\<close>
lemma fin_string_length:
  fixes L::string
  assumes len:"length L \<le> k"
  assumes Len:"length L \<le> MAX_STR"
  shows "List.member (fin_string_upto k) (Abs_fin_string L)"
proof - 
  have BC:"\<forall>j\<ge>0. 0 \<le> MAX_STR \<longrightarrow> length [] = 0 \<longrightarrow> 
    List.member (fin_string_upto j) (Abs_fin_string [])" 
    apply(auto) 
    subgoal for j 
      apply(cases j) 
      by (auto simp add: fin_string_empty_def member_rec) 
    done
  have IS:"(\<And>k x xs.
      \<forall>j\<ge>k. k\<le>MAX_STR \<longrightarrow> length xs=k \<longrightarrow> List.member (fin_string_upto j) (Abs_fin_string xs)\<Longrightarrow>
      \<forall>j\<ge>Suc k. Suc k \<le> MAX_STR \<longrightarrow> length (x # xs) = Suc k 
        \<longrightarrow> List.member (fin_string_upto j) (Abs_fin_string (x # xs)))"
    subgoal for k x xs
    proof -
      assume "\<forall>j\<ge>k. k \<le> MAX_STR \<longrightarrow> length xs = k 
        \<longrightarrow> List.member (fin_string_upto j) (Abs_fin_string xs)"
      then have IH:"\<And>j. j\<ge> k \<Longrightarrow> k \<le> MAX_STR \<Longrightarrow> length xs = k 
        \<Longrightarrow> List.member (fin_string_upto j) (Abs_fin_string xs)" 
        by auto
      show ?thesis
        apply(auto)
        subgoal for j
        proof -
          assume kj:"Suc (length xs) \<le> j"
          assume sucMax:"Suc (length xs) \<le> MAX_STR"
          assume ilen:" k = length xs"
          obtain jj where jj[simp]:"j = Suc jj" using kj Suc_le_D by auto
          then have kMax:"k < MAX_STR" using jj kj Suc_le_D ilen
            by (simp add: less_eq_Suc_le sucMax)
           have res:"List.member (fin_string_upto (jj)) (Abs_fin_string xs)"
            using IH[of "jj"] kj jj ilen  Suc_leD sucMax by blast
          have neq:"Abs_fin_string [] \<noteq> Abs_fin_string (x # xs)"
            using Abs_fin_string_inverse fin_string_empty.abs_eq fin_string_empty.rep_eq 
              len length_Cons list.distinct(1) mem_Collect_eq
            by (metis ilen sucMax)
          have univ:" set enum_class.enum  = (UNIV::char set)" using enum_chars by auto
          have "List.member (fin_string_upto j) (Abs_fin_string (x # xs))"
            apply(auto simp add: member_rec(2) fin_string_empty_def)
            using len sucMax 
            apply(auto simp add: member_rec fin_string_empty_def fin_string_cons_def
                Abs_fin_string_inverse Rep_fin_string_inverse neq)
          proof -
            let ?witLL = "(\<lambda> x. map (map_fun Rep_fin_string Abs_fin_string (string_cons x)) 
                            (fin_string_upto jj))"
            have f1: "Abs_fin_string xs \<in> set (fin_string_upto jj)"
                by (metis member_def res)
            have f2:"Abs_fin_string (x # xs) = Abs_fin_string 
                      (if MAX_STR \<le> length (Rep_fin_string (Abs_fin_string xs)) 
                       then Rep_fin_string (Abs_fin_string xs)
                       else x # Rep_fin_string (Abs_fin_string xs))"
                using Abs_fin_string_inverse ilen kMax by auto
            have ex:"\<exists> LL. (List.member (map ?witLL enum_class.enum) LL) 
                          \<and> List.member LL (Abs_fin_string (x # xs))"
              apply(rule exI[where x="?witLL x"])
              apply(auto simp add: member_def univ)
              using f1 f2 by blast
            show "List.member (concat (map ?witLL enum_class.enum))
                    (Abs_fin_string (x # xs))"
              using member_concat ex by fastforce
          qed
          then show "List.member (fin_string_upto j) (Abs_fin_string (x # xs))"  by auto
        qed
        done
    qed
    done
  have impl:"length L \<le> k \<Longrightarrow> List.member (fin_string_upto k) (Abs_fin_string L)"
    using len Len 
    length_induct[where P = "(\<lambda> L k. \<forall> j \<ge> k. k \<le> MAX_STR \<longrightarrow> length L = k 
        \<longrightarrow> List.member (fin_string_upto j) (Abs_fin_string L))"
      , OF Len BC IS]
      by auto
    show ?thesis
    using impl len by auto
qed


lemma fin_string_upto_length:
  shows "List.member (fin_string_upto n) L \<Longrightarrow> ilength L \<le> n"
  apply(induction n arbitrary: L)
   apply(auto simp add: fin_string_empty_def Let_def ilength_def fin_string_cons_def 
     Rep_fin_string_inverse Abs_fin_string_inverse member_rec)
proof -
  fix n L
  let ?witLL = "(\<lambda>x. map(map_fun Rep_fin_string Abs_fin_string(string_cons x))(fin_string_upto n))"
  assume len:"(\<And>L. List.member (fin_string_upto n) L \<Longrightarrow> length (Rep_fin_string L) \<le> n)"
  assume mem:"List.member (concat (map ?witLL enum_class.enum)) L"
  have L:"List.member (fin_string_upto n) L \<Longrightarrow> length (Rep_fin_string L) \<le> Suc n" 
    using len[of L] by auto
  assume a:"List.member (concat (map ?witLL enum_class.enum)) L"
  obtain LL where conc:"List.member (map ?witLL enum_class.enum) LL"
    and concmem:"List.member LL L"
    using member_concat a by metis
  obtain c cs where c:"L = fin_string_cons c cs" and cs:"List.member (fin_string_upto n) cs"
    using a conc unfolding member_def apply(auto)
    subgoal for c d cs
      apply(cases "MAX_STR \<le> length (Rep_fin_string cs)")
      apply(auto simp add: Rep_fin_string_inverse)
      by (metis (full_types) Rep_fin_string_inverse fin_string_cons.rep_eq string_cons.simps)+ 
    done
  then have "ilength (fin_string_cons c cs) \<le> (Suc n)"
    using len[of cs] unfolding ilength_def fin_string_cons_def 
    apply (auto simp add: Rep_fin_string_inverse)
    using c fin_string_cons.rep_eq by force
  then show "length (Rep_fin_string L) \<le> Suc n"
    using c ilength.rep_eq by auto
qed

text\<open>fin-string-upto produces no duplicate identifiers\<close>
lemma distinct_upto:
  shows "i \<le> MAX_STR \<Longrightarrow> distinct (fin_string_upto i)"
proof (induction i)
  case 0
  then show ?case by(auto)
next
  case (Suc j) then
  have jLen:"Suc j \<le> MAX_STR"
    and IH:"distinct (fin_string_upto j)" by auto
  have distinct_char:"distinct (enum_class.enum:: char list)" 
    by (auto simp add: distinct_map enum_char_unfold)
  have diseq:"\<And> x y. y \<in> set (fin_string_upto j) \<Longrightarrow>  fin_string_empty \<noteq> fin_string_cons x y" 
    using Rep_fin_string_inverse jLen apply(auto simp add: fin_string_empty_def fin_string_cons_def)
    using fin_string_empty.rep_eq le_zero_eq list.size not_less_eq_eq zero_le Abs_fin_string_inject
    by (metis,auto)
  show ?case 
    apply(auto simp add: Let_def)
    subgoal for x xa using diseq by auto
    apply(rule distinct_concat)
    subgoal 
      apply(auto simp add: distinct_map)
       apply(rule distinct_char)
      apply(rule subset_inj_on[where B=UNIV])
       apply(rule injI)
       apply(auto simp add: fin_string_cons_def)
    proof -
      fix x y
      let ?l = "(\<lambda>xa x. Abs_fin_string 
        (if MAX_STR \<le> length (Rep_fin_string xa) 
         then Rep_fin_string xa 
         else x # Rep_fin_string xa))"
      assume a1:"\<forall>xa\<in>set (fin_string_upto j). ?l xa x = ?l xa y"
      then have a2:"\<And>xa. (List.member (fin_string_upto j) xa) \<Longrightarrow> ?l xa x = ?l xa y"
        using  member_def by force
      then have "Abs_fin_string [x] = Abs_fin_string [y] \<or> (MAX_STR::nat) = 0"
        using a2 fin_string_empty.rep_eq fin_string_nil by force
      then show "x = y"
        by (metis Abs_fin_string_inverse jLen le_zero_eq length_Cons list.inject list.size(3) 
            mem_Collect_eq nat.distinct(1) not_less_eq_eq)
    qed
    subgoal for ys
      apply(auto simp add: fin_string_cons_def)
    proof -
      fix c :: char
      assume c:"c \<in> set enum_class.enum"
      assume ys:"ys=map(map_fun Rep_fin_string Abs_fin_string (string_cons c)) (fin_string_upto j)"
      show"distinct(map(map_fun Rep_fin_string Abs_fin_string (string_cons c)) (fin_string_upto j))"
        unfolding distinct_map apply(rule conjI)
         apply(rule IH)
        apply(rule inj_onI)
        apply(auto)
        subgoal for x y
          using jLen fin_string_upto_length[of j x] fin_string_upto_length[of j y]
          unfolding List.member_def ilength_def apply auto
          by (metis (mono_tags, hide_lams) Rep_fin_string_inverse fin_string_cons.rep_eq le_trans
              list.inject not_less_eq_eq string_cons.simps)
          done
      qed
      apply(auto simp add: fin_string_cons_def)
      subgoal for c ca xa xb xc
        apply(cases "MAX_STR \<le> length (Rep_fin_string xa)")
         apply (metis fin_string_upto_length jLen ilength.rep_eq le_trans member_def not_less_eq_eq)
        apply(cases "MAX_STR \<le> length (Rep_fin_string xb)")
         apply(metis fin_string_upto_length jLen ilength.rep_eq le_trans member_def not_less_eq_eq)
        apply(cases "MAX_STR \<le> length (Rep_fin_string xc)") 
         by(auto,metis Rep_fin_string_inverse fin_string_cons.rep_eq list.inject string_cons.simps)
      done
  qed

text\<open>Finite strings are an enumeration type\<close>
instantiation fin_string :: enum begin
definition enum_fin_string 
  where enum_fin_string_def[code]:"enum_fin_string \<equiv> fin_string_enum"
definition enum_all_fin_string
  where enum_all_fin_string[code]:"enum_all_fin_string \<equiv> fin_string_enum_all"
definition enum_ex_fin_string
  where enum_ex_fin_string[code]:"enum_ex_fin_string \<equiv> fin_string_enum_ex"
lemma enum_ALL:"(UNIV::fin_string set) = set enum_class.enum"
  apply(auto simp add:enum_fin_string_def fin_string_enum_def vals_def)
  by(metis fin_string_length List.member_def mem_Collect_eq Abs_fin_string_cases)

lemma vals_ALL:"set (vals::fin_string list) = UNIV"
  using enum_ALL vals_def Rep_fin_string fin_string_length ilength.rep_eq member_def 
  by(metis (mono_tags) Rep_fin_string_inverse UNIV_eq_I mem_Collect_eq)

lemma setA:
  assumes set:"\<And>y. y \<in> set L \<Longrightarrow> P y"
  shows "list_all P L"
  using set  by (simp add: list.pred_set)

lemma setE:
  assumes set:" y \<in> set L"
  assumes P:"P y"
  shows "list_ex P L"
  using set P  list_ex_iff by auto

instance 
  apply(standard)
  apply(rule enum_ALL)
  by (auto simp add: fin_string_enum_all_def list_all_iff vals_ALL setA setE enum_all_fin_string
      enum_ALL fin_string_enum_def vals_def enum_fin_string_def distinct_upto list_ex_iff 
      enum_ex_fin_string fin_string_enum_ex_def)
end

instantiation fin_string :: equal begin
definition equal_fin_string :: "fin_string \<Rightarrow> fin_string \<Rightarrow> bool"
  where [code]:"equal_fin_string X Y = (X \<le> Y \<and> Y \<le> X)"
instance
  apply(standard)
  by(auto simp add: equal_fin_string_def)
end
end