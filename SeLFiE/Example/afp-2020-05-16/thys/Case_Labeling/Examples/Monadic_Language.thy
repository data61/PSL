subsection \<open>A labeling VCG for a monadic language\<close>

theory Monadic_Language
imports
  Complex_Main
  "../Case_Labeling"
  "HOL-Eisbach.Eisbach"
begin

ML_file \<open>../util.ML\<close>

ML \<open>
  fun vcg_tac nt_rules nt_comb ctxt =
    let
      val rules = Named_Theorems.get ctxt nt_rules
      val comb = Named_Theorems.get ctxt nt_comb
    in REPEAT_ALL_NEW_FWD ( resolve_tac ctxt rules ORELSE' (resolve_tac ctxt comb THEN' resolve_tac ctxt rules)) end
\<close>


text \<open>This language is inspired by the languages used in AutoCorres @{cite greenaway_bridging_2012}\<close>

consts bind :: "'a option \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b option" (infixr "|>>" 4)
consts return :: "'a \<Rightarrow> 'a option"
consts while :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> ('a \<Rightarrow> 'a option)"
consts valid :: "bool \<Rightarrow> 'a option \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"

named_theorems vcg
named_theorems vcg_comb

method_setup vcg = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD (FIRSTGOAL (vcg_tac @{named_theorems "vcg"} @{named_theorems "vcg_comb"} ctxt)))
\<close>


axiomatization where
   return[vcg]: "valid (Q x) (return x) Q" and
   bind[vcg]: "\<lbrakk>\<And>x. valid (R x) (c2 x) Q; valid P c1 R\<rbrakk> \<Longrightarrow> valid P (bind c1 c2) Q" and
   while[vcg]: "\<And>c. \<lbrakk>\<And>x. valid (I x \<and> b x) (c x) I; \<And>x. I x \<and> \<not>b x \<Longrightarrow> Q x\<rbrakk> \<Longrightarrow> valid (I x) (while b I c x) Q" and
   cond[vcg]: "\<And>b c1 c2. valid P1 c1 Q \<Longrightarrow> valid P2 c2 Q \<Longrightarrow> valid (if b then P1 else P2) (if b then c1 else c2) Q" and
   case_prod[vcg]: "\<And>P. \<lbrakk>\<And>x y. v = (x,y) \<Longrightarrow> valid (P x y) (B x y) Q\<rbrakk>
    \<Longrightarrow> valid (case v of (x,y) \<Rightarrow> P x y) (case v of (x,y) \<Rightarrow> B x y) Q" and
   conseq[vcg_comb]: "\<lbrakk>valid P' c Q; P \<Longrightarrow> P'\<rbrakk> \<Longrightarrow> valid P c Q"


text \<open>Labeled rules\<close>

named_theorems vcg_l
named_theorems vcg_l_comb
named_theorems vcg_elim

method_setup vcg_l = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD (FIRSTGOAL (vcg_tac @{named_theorems "vcg_l"} @{named_theorems "vcg_l_comb"} ctxt)))
\<close>

method vcg_l' = (vcg_l; (elim vcg_elim)?)

context begin
  interpretation Labeling_Syntax .

  lemma L_return[vcg_l]: "CTXT inp ct (Suc inp) (valid (P x) (return x) P)"
    unfolding LABEL_simps by (rule return)

  lemma L_bind[vcg_l]:
    assumes "\<And>x. CTXT (Suc outp') ((''bind'',outp', [VAR x]) # ct) outp (valid (R x) (c2 x) Q)"
    assumes "CTXT inp ct outp' (valid P c1 R)"
    shows "CTXT inp ct outp (valid P (bind c1 c2) Q)"
    using assms unfolding LABEL_simps by (rule bind)

  lemma L_while[vcg_l]:
    fixes inp ct defines "ct' \<equiv> \<lambda>x. (''while'', inp, [VAR x])  # ct"
    assumes "\<And>x. CTXT (Suc inp) (ct' x) outp'
      (valid (BIND ''inv_pre'' inp (I x) \<and> BIND ''lcond'' inp (b x)) (c x) (\<lambda>x. BIND ''inv_post'' inp (I x)))"
    assumes "\<And>x. B\<langle>''inv_pre'',inp: I x\<rangle> \<and> B\<langle>''lcond'',inp: \<not>b x\<rangle> \<Longrightarrow> VC (''post'',outp' , []) (ct' x) (P x)"
    shows "CTXT inp ct (Suc outp') (valid (I x) (while b I c x) P)"
    using assms(2-) unfolding LABEL_simps by (rule while)

  lemma L_cond[vcg_l]:
    fixes inp ct defines "ct' \<equiv> (''if'',inp,[]) # ct"
    assumes "C\<langle>Suc inp, (''then'',inp,[]) # ct',outp: valid P1 c1 Q\<rangle>"
    assumes "C\<langle>Suc outp, (''else'',outp,[]) # ct',outp': valid P2 c2 Q\<rangle>"
    shows "C\<langle>inp,ct,outp': valid (if B\<langle>''cond'',inp: b\<rangle> then B\<langle>''then'',inp: P1\<rangle> else B\<langle>''else'',inp: P2\<rangle>) (if b then c1 else c2) Q\<rangle>"
    using assms(2-) unfolding LABEL_simps by (rule cond)

  lemma L_case_prod[vcg_l]:
    assumes "\<And>x y. v = (x,y) \<Longrightarrow> CTXT inp ct outp (valid (P x y) (B x y) Q)"
    shows "CTXT inp ct outp (valid (case v of (x,y) \<Rightarrow> P x y) (case v of (x,y) \<Rightarrow> B x y) Q)"
    using assms unfolding LABEL_simps by (rule case_prod)

  lemma L_conseq[vcg_l_comb]:
    assumes "CTXT (Suc inp) ct outp (valid P' c Q)"
    assumes "P \<Longrightarrow> VC (''conseq'',inp,[]) ct P'"
    shows "CTXT inp ct outp (valid P c Q)"
    using assms unfolding LABEL_simps by (rule conseq)

  lemma L_assm_conjE[vcg_elim]:
    assumes "BIND name inp (P \<and> Q)" obtains "BIND name inp P" "BIND name inp Q"
    using assms unfolding LABEL_simps by auto

  declare conjE[vcg_elim]

end



lemma dvd_div:
  fixes a b c :: int
  assumes "a dvd b" "c dvd b" "coprime a c"
  shows "a dvd (b div c)"
  using assms coprime_dvd_mult_left_iff by fastforce

lemma divides: "
valid
  (0 < (a :: int))
  (
    return a
    |>> (\<lambda>n.
      while
        (\<lambda>n. even n)
        (\<lambda>n. 0 < n \<and> n dvd a \<and> (\<forall>m. odd m \<and> m dvd a \<longrightarrow> m dvd n))
        (\<lambda>n. return (n div 2))
        n
    )
  )
  (\<lambda>r. odd r \<and> r dvd a \<and> (\<forall>m. odd m \<and> m dvd a \<longrightarrow> m \<le> r))
"
  apply vcg
    apply (auto simp add: zdvd_imp_le dvd_div div_positive_int elim!:
      evenE intro: dvd_mult_right)
  done

lemma L_divides: "
valid
  (0 < (a :: int))
  (
    return a
    |>> (\<lambda>n.
      while
        (\<lambda>n. even n)
        (\<lambda>n. 0 < n \<and> n dvd a \<and> (\<forall>m. odd m \<and> m dvd a \<longrightarrow> m dvd n))
        (\<lambda>n. return (n div 2))
        n
    )
  )
  (\<lambda>r. odd r \<and> r dvd a \<and> (\<forall>m. odd m \<and> m dvd a \<longrightarrow> m \<le> r))
"
  apply (rule Initial_Label)
  apply vcg_l'
proof casify
print_nested_cases
  case bind
  { case (while n)
    { case post then show ?case by (auto simp: zdvd_imp_le)
    next
      case conseq
      from \<open>0 < n\<close> \<open>even n\<close> have "0 < n div 2"
        by (simp add: pos_imp_zdiv_pos_iff zdvd_imp_le)
      moreover
      from \<open>n dvd a\<close> \<open>even n\<close> have "n div 2 dvd a"
        by (metis dvd_div_mult_self dvd_mult_left)
      moreover
      { fix m assume "odd m" "m dvd a"
        then have "m dvd n" using conseq.inv_pre(3) by simp
        moreover note \<open>even n\<close>
        moreover from \<open>odd m\<close> have "coprime m 2"
         by (metis dvd_eq_mod_eq_0 invertible_coprime mult_cancel_left2 not_mod_2_eq_1_eq_0)
        ultimately
        have "m dvd n div 2" by (rule dvd_div)
      }
      ultimately show ?case by auto
    }
  next
    case conseq then show ?case by auto
  }
qed



lemma add: "
valid
  True
  (
    while
      \<comment> \<open>COND:\<close> (\<lambda>(r,j). j < (b :: nat))
      \<comment> \<open>INV:\<close> (\<lambda>(r,j). j \<le> b \<and> r = a + j)
      \<comment> \<open>BODY:\<close> (\<lambda>(r,j). return (r + 1, j + 1))
      \<comment> \<open>START:\<close> (a,0)
    |>> (\<lambda>(r,_). return r)
  )
  (\<lambda>r. r = a + b)
"
  by vcg auto


lemma mult: "
valid
  True
  (
    while
      \<comment> \<open>COND:\<close> (\<lambda>(r,i). i < (a :: nat))
      \<comment> \<open>INV:\<close> (\<lambda>(r,i). i \<le> a \<and> r = i * b)
      \<comment> \<open>BODY:\<close> (\<lambda>(r,i).
        while
          \<comment> \<open>COND:\<close> (\<lambda>(r,j). j < b)
          \<comment> \<open>INV:\<close> (\<lambda>(r,j). i < a \<and> j \<le> b \<and> r = i * b + j)
          \<comment> \<open>BODY:\<close> (\<lambda>(r,j). return (r + 1, j + 1))
          \<comment> \<open>START:\<close> (r,0)
        |>> (\<lambda>(r,_). return (r, i + 1))
      )
      \<comment> \<open>START:\<close> (0,0)
    |>> (\<lambda>(r,_). return r)
  )
  (\<lambda>r. r = a * b)
"
  by vcg auto


section \<open>Labeled\<close>

lemma L_mult: "
valid
  True
  (
    while
      \<comment> \<open>COND:\<close> (\<lambda>(r,i). i < (a :: nat))
      \<comment> \<open>INV:\<close> (\<lambda>(r,i). i \<le> a \<and> r = i * b)
      \<comment> \<open>BODY:\<close> (\<lambda>(r,i).
        while
          \<comment> \<open>COND:\<close> (\<lambda>(r,j). j < b)
          \<comment> \<open>INV:\<close> (\<lambda>(r,j). i < a \<and> j \<le> b \<and> r = i * b + j)
          \<comment> \<open>BODY:\<close> (\<lambda>(r,j). return (r + 1, j + 1))
          \<comment> \<open>START:\<close> (r,0)
        |>> (\<lambda>(r,_). return (r, i + 1))
      )
      \<comment> \<open>START:\<close> (0,0)
    |>> (\<lambda>(r,_). return r)
  )
  (\<lambda>r. r = a * b)
"
  apply (rule Initial_Label)
  apply vcg_l'
proof casify
  case while
  { case while
    { case post then show ?case by auto
    next
      case conseq then show ?case by auto
    }
  next
    case post then show ?case by auto
  next
    case conseq then show ?case by auto
  }
next
  case conseq then show ?case by auto
qed

lemma L_paths: "
valid
  (path \<noteq> [])
  ( while
      \<comment> \<open>COND:\<close> (\<lambda>(p,r). p \<noteq> [])
      \<comment> \<open>INV:\<close> (\<lambda>(p,r). distinct r \<and> hd (r @ p) = hd path \<and> last (r @ p) = last path)
      \<comment> \<open>BODY:\<close> (\<lambda>(p,r).
        return (hd p)
        |>> (\<lambda>x.
          if (r \<noteq> [] \<and> x = hd r)
          then return []
          else (if x \<in> set r
            then return (takeWhile (\<lambda>y. y \<noteq> x) r)
            else return (r))
        |>> (\<lambda>r'. return (tl p, r' @ [x])
        )
        )
        )
      \<comment> \<open>START:\<close> (path, [])
    |>> (\<lambda>(_,r). return r)
  )
  (\<lambda>r. distinct r \<and> hd r = hd path \<and> last r = last path)
"
  apply (rule Initial_Label)
  apply vcg_l'
proof casify
  case conseq then show ?case by auto
next
  case (while p r)
  { case conseq
    from conseq have "r = [] \<Longrightarrow> ?case" by (cases p) auto
    moreover
    from conseq have "r \<noteq> [] \<Longrightarrow> hd p = hd r \<Longrightarrow> ?case" by (cases p) auto
    moreover
    { assume A: "r \<noteq> []" "hd p \<noteq> hd r"
      have "hd (takeWhile (\<lambda>y. y \<noteq> hd p) r @ hd p # tl p) = hd r"
        using A by (cases r) auto
      moreover
      have "last (takeWhile (\<lambda>y. y \<noteq> hd p) r @ hd p # tl p) = last (r @ p)"
        using A \<open>p \<noteq> []\<close> by auto
      moreover
      have "distinct (takeWhile (\<lambda>y. y \<noteq> hd p) r @ [hd p])"
        using conseq by (auto dest: set_takeWhileD)
      ultimately
      have ?case using A conseq by auto
    }
    ultimately show ?case by blast
  next
    case post then show ?case by auto
  }
qed

end
