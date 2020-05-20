(*
    Author:     Tobias Nipkow, 2008
*)

section "The Gibbard-Satterthwaite Theorem"

theory GS imports Arrow_Order
begin

text\<open>The Gibbard-Satterthwaite theorem as a corollary to Arrow's
theorem. The proof follows Nisan~\cite{NisanRTV07}.\<close>

definition "manipulable f == \<exists>P\<in>Prof. \<exists>i. \<exists>L\<in>Lin. (f P, f(P(i:=L))) : P i"

definition "dict f i == \<forall>P\<in>Prof.\<forall>a. a \<noteq> f P \<longrightarrow> (a,f P) : P i"

definition
 Top :: "alt set \<Rightarrow> pref \<Rightarrow> pref" where
"Top S L \<equiv> {(a,b). (a,b) \<in> L \<and> (a \<in> S \<and> b \<in> S \<or> a \<notin> S \<and> b \<notin> S)} \<union>
             {(a,b). a \<notin> S \<and> b \<in> S}"

lemma Top_in_Lin: "L:Lin \<Longrightarrow> Top S L : Lin"
apply(simp add:Top_def slo_defs Sigma_def)
unfolding trans_def
apply blast
done

lemma Top_in_Prof: "P:Prof \<Longrightarrow> Top S o P : Prof"
by(simp add:Prof_def Pi_def Top_in_Lin)

lemma not_manipulable: "\<not> manipulable f \<longleftrightarrow>
 (\<forall>P\<in>Prof.\<forall>i.\<forall>L\<in>Lin. f P \<noteq> f(P(i:=L)) \<longrightarrow>
   (f(P(i := L)), f P) : P i \<and> (f P, f(P(i := L))) : L)" (is "?A = ?B")
proof
  assume ?A
  show ?B
  proof(clarsimp)
    fix P i L assume 0: "P \<in> Prof" "L \<in> Lin" "f P \<noteq> f (P(i := L))"
    moreover hence 1: "P i: Lin" "P(i:=L): Prof" by(simp add:Prof_def Pi_def)+
    ultimately have "(f (P(i := L)), f P) \<in> P i" (is ?L)
      using \<open>?A\<close> unfolding manipulable_def by (metis notin_Lin_iff)
    moreover have "(f P, f (P(i := L))) \<in> L" (is ?R)
      using 0 1 fun_upd_upd[of P] fun_upd_triv[of P] fun_upd_same[of P]
      using \<open>?A\<close> unfolding manipulable_def by (metis notin_Lin_iff)
    ultimately show "?L \<and> ?R" ..
  qed
next
  assume ?B
  show ?A
  proof(clarsimp simp:manipulable_def)
    fix P i L assume "P \<in> Prof" "L \<in> Lin" "(f P, f (P(i := L))) \<in> P i"
    moreover hence "P i: Lin" by(simp add:Prof_def Pi_def)
    ultimately show False
      using \<open>?B\<close> by(metis Lin_irrefl)
  qed
qed

definition "swf(f) \<equiv> \<lambda>P. {(a,b). a\<noteq>b \<and> f(Top {a,b} o P) = b}"

locale GS =
fixes f
assumes not_manip: "\<not> manipulable f"
and onto: "f ` Prof = UNIV"
begin

lemma nonmanip:
  "P:Prof \<Longrightarrow> L:Lin \<Longrightarrow> f(P(i := L)) \<noteq> f P \<Longrightarrow>
  (f(P(i := L)), f P) : P i \<and> (f P, f(P(i := L))) : L"
using not_manip by(metis not_manipulable)

lemma mono:
assumes "P\<in>Prof" "P'\<in>Prof" "\<forall>i a. (a, f P) : P i \<longrightarrow> (a, f P) : P' i"
shows "f P' = f P"
proof-
  obtain h :: "indi \<Rightarrow> nat" where
    injh: "inj h" and surjh: "h ` I = {0..<N}"
    by(metis ex_bij_betw_finite_nat[OF finite_indi] bij_betw_def)
  let ?M = "%n i. if h i < n then P' i else P i"
  have N: "!!i. h i < N" using surjh by auto
  have MProf: "!!n. ?M n : Prof" and P'Lin: "!!i. P' i : Lin"
    using \<open>P:Prof\<close> \<open>P':Prof\<close> by(simp add:Prof_def Pi_def)+
  { fix n have "n<=N \<Longrightarrow> f(?M n) = f P"
    proof(induct n)
      case 0 show ?case by simp
    next
      case (Suc n)
      let ?up = "(?M n)(inv h n := P' (inv h n))"
      have 1: "?M(Suc n) = ?up" using surjh Suc(2)
        by(simp (no_asm_simp) add:fun_eq_iff f_inv_into_f)
          (metis injh inv_f_f less_antisym)
      show ?case
      proof(rule ccontr)
        assume "\<not> ?case"
        with \<open>?M(Suc n) = ?up\<close> Suc have 0: "f ?up \<noteq> f(?M n)" by simp
        from nonmanip[OF MProf P'Lin 0] assms(3) show False
          using N surjh Suc Lin_irrefl[OF P'Lin]
          by(fastforce simp: f_inv_into_f)
      qed
    qed
  }
  from this[of N] N show "f P' = f P" by simp
qed

lemma una_Top: assumes "P:Prof" "S \<noteq> {}" shows "f(Top S o P) : S"
proof -
  obtain h :: "indi \<Rightarrow> nat" where
    injh: "inj h" and surjh: "h ` I = {0..<N}"
    by(metis ex_bij_betw_finite_nat[OF finite_indi] bij_betw_def)
  from assms obtain a where "a:S" by blast
  from onto obtain Pa where "Pa:Prof" "f Pa = a"
    by(metis inv_into_into UNIV_I f_inv_into_f)
  let ?M = "%n i. if h i < n then Top S (P i) else Pa i"
  have N: "!!i. h i < N" using surjh by auto
  have MProf: "!!n. ?M n : Prof" using \<open>P:Prof\<close> \<open>Pa:Prof\<close>
    by(simp add:Prof_def Pi_def Top_in_Lin mktop_Lin)
  { fix n have "n<=N \<Longrightarrow> f(?M n) : S"
    proof(induct n)
      case 0 thus ?case using \<open>f Pa = a\<close> \<open>a:S\<close> by simp
    next
      case (Suc n)
      show ?case
      proof cases
        assume "f(?M n) = f(?M(Suc n))"
        thus ?case using Suc by simp
      next
        let ?up = "(?M n)(inv h n := Top S (P(inv h n)))"
        assume "f(?M n) \<noteq> f(?M(Suc n))"
        also have eq: "?M(Suc n) = ?up" using surjh Suc
          by(simp (no_asm_simp) add:fun_eq_iff f_inv_into_f)
            (metis injh inv_f_eq less_antisym)
        finally have n: "f(?M n) \<noteq> f(?up)" .
        with nonmanip[OF MProf Top_in_Lin n[symmetric]] Suc eq \<open>P:Prof\<close>
        show ?case by (simp add:Top_def Prof_def Pi_def)
      qed
    qed
  }
  from this[of N] N show ?thesis by(simp add:comp_def)
qed

lemma SWF_swf: "swf f : SWF"
proof (rule Pi_I)
  fix P assume "P: Prof"
  show "swf f P : Lin"
  proof(unfold Lin_def strict_linear_order_on_def, auto)
    show "total(swf f P)"
    proof(simp add: total_on_def, intro allI impI)
      fix a b :: alt assume "a\<noteq>b"
      thus "(a,b) \<in> swf f P \<or> (b,a) \<in> swf f P"
        unfolding swf_def using una_Top[of P "{a,b}"] \<open>P:Prof\<close>
        by simp(metis insert_commute)
    qed
    show "irrefl(swf f P)" by(simp add: irrefl_def swf_def)
    show "trans(swf f P)"
    proof (clarsimp simp:trans_def swf_def insert_commute)
      fix a b c assume "a\<noteq>b" "b\<noteq>c" "f(Top{a,b} \<circ> P) = b" "f(Top{b,c} \<circ> P) = c"
      hence "a\<noteq>c" by(auto simp: insert_commute)
      note 3 = Top_in_Prof[OF \<open>P:Prof\<close>, of "{a,b,c}"]
      { assume "f (Top {a, b, c} \<circ> P) = a"
        hence "f(Top{a,b} \<circ> P) = a"
          using mono[OF 3 Top_in_Prof[OF \<open>P:Prof\<close>], of "{a,b}"]
          by(auto simp:Top_def)
        with \<open>f(Top{a,b} \<circ> P) = b\<close> \<open>a\<noteq>b\<close> have False by simp
      } moreover
      { assume "f (Top {a, b, c} \<circ> P) = b"
        hence "f(Top{b,c} \<circ> P) = b"
          using mono[OF 3 Top_in_Prof[OF \<open>P:Prof\<close>], of "{b,c}"]
          by(auto simp:Top_def)
        with \<open>f(Top{b,c} \<circ> P) = c\<close> \<open>b\<noteq>c\<close> have False by simp
      }
      ultimately have "f (Top {a, b, c} \<circ> P) = c"
        using una_Top[OF \<open>P:Prof\<close>, of "{a,b,c}", simplified] by blast
      hence "f(Top{a,c} \<circ> P) = c" (is ?R)
        using mono[OF 3 Top_in_Prof[OF \<open>P:Prof\<close>], of "{a,c}"]
        by (auto simp:Top_def)
      thus "a\<noteq>c \<and> ?R" using \<open>a\<noteq>c\<close> by blast
    qed
  qed
qed

lemma Top_top: "L:Lin \<Longrightarrow> (!!a. a\<noteq>b \<Longrightarrow> (a,b) : L) \<Longrightarrow> Top {b} L = L"
apply(auto simp:Top_def slo_defs)
apply (metis trans_def)
apply (metis trans_def)
done

lemma una_swf: "unanimity(swf f)"
proof(clarsimp simp:swf_def unanimity_def)
  fix P a b
  assume "P:Prof" and abP: "\<forall>i. (a, b) \<in> P i"
  hence "a \<noteq> b" by(fastforce simp:Prof_def Pi_def slo_defs)
  let ?abP = "Top {a,b} \<circ> P"
  have "?abP : Prof" using \<open>P:Prof\<close> by(simp add:Prof_def Pi_def Top_in_Lin)
  have top: "!!i c. b\<noteq>c \<Longrightarrow> (c,b) : Top {a,b} (P i)"
    using abP by(auto simp:Top_def)
  have "Top {b} o ?abP = ?abP" using \<open>P:Prof\<close>
    by (simp add:fun_eq_iff top Top_top Prof_def Pi_def Top_in_Lin)
  moreover have "f(Top {b} o ?abP) = b"
    by (metis una_Top[OF \<open>?abP : Prof\<close>] empty_not_insert singletonE)
  ultimately have "f ?abP = b" by simp
  thus "a\<noteq>b \<and> f ?abP = b" using \<open>a\<noteq>b\<close> by blast
qed

lemma IIA_swf: "IIA(swf f)"
proof(clarsimp simp: IIA_def)
  fix P P' a b
  assume "P:Prof" "P':Prof" and iff: "\<forall>i. ((a,b) \<in> P i) = ((a,b) \<in> P' i)"
  hence [simp]: "!!i x. (x,x) ~: P i \<and> (x,x) ~: P' i"
    by(simp add:Prof_def Pi_def slo_defs)
  have iff':  "a\<noteq>b \<longrightarrow> (\<forall>i. ((b,a) \<in> P i) = ((b,a) \<in> P' i))"
    using iff \<open>P:Prof\<close> \<open>P':Prof\<close> unfolding Prof_def Pi_def
    by simp (metis iff notin_Lin_iff)
  let ?abP = "Top {a,b} o P" let ?abP' = "Top {a,b} o P'"
  have "\<forall>i c. (c, f ?abP) : ?abP i \<longrightarrow> (c, f ?abP) : ?abP' i"
    using una_Top[of P "{a,b}", OF \<open>P:Prof\<close>] iff iff' by(auto simp add:Top_def)
  then have "f (Top {a,b} \<circ> P) = f (Top {a,b} \<circ> P')"
    using Top_in_Prof[OF \<open>P:Prof\<close>] Top_in_Prof[OF \<open>P':Prof\<close>]
          mono[of "Top {a, b} \<circ> P"]  by metis
  thus "(a <\<^bsub>swf f P\<^esub> b) = (a <\<^bsub>swf f P'\<^esub> b)" by(simp add: swf_def)
qed

lemma dict_swf: assumes "dictator (swf f) i" shows "dict f i"
proof (auto simp:dict_def)
  fix P a assume "P:Prof" "a\<noteq>f P"
  have "f (Top {a,f P} \<circ> P) = f P"
    using mono[OF \<open>P:Prof\<close> Top_in_Prof[OF \<open>P:Prof\<close>,of "{a,f P}"]]
    by (auto simp:Top_def)
  moreover have "P i = {(a,b). a\<noteq>b \<and> f(Top {a,b} \<circ> P) = b}"
    using assms \<open>P:Prof\<close> by(simp add:dictator_def swf_def)
  ultimately show "(a,f P) : P i" using \<open>a\<noteq>f P\<close> by simp
qed


theorem Gibbard_Satterthwaite:
  "\<exists>i. dict f i"
by (metis Arrow SWF_swf una_swf IIA_swf dict_swf)

end

theorem Gibbard_Satterthwaite:
  "\<not> manipulable f \<Longrightarrow> \<forall>a.\<exists>P\<in>Prof. a = f P \<Longrightarrow> \<exists>i. dict f i"
using GS.Gibbard_Satterthwaite[of f,unfolded GS_def]
by blast

end
