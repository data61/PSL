(* Title: Resumption.thy
  Author: Andreas Lochbihler, ETH Zurich *)

section \<open>The resumption-error monad\<close>

theory Resumption
imports
  Misc_CryptHOL
  Partial_Function_Set
begin

codatatype (results: 'a, outputs: 'out, 'in) resumption
  = Done (result: "'a option")
  | Pause ("output": 'out) (resume: "'in \<Rightarrow> ('a, 'out, 'in) resumption")
where
  "resume (Done a) = (\<lambda>inp. Done None)"

code_datatype Done Pause

primcorec bind_resumption :: 
  "('a, 'out, 'in) resumption
     \<Rightarrow> ('a \<Rightarrow> ('b, 'out, 'in) resumption) \<Rightarrow> ('b, 'out, 'in) resumption"
where
  "\<lbrakk> is_Done x; result x \<noteq> None \<longrightarrow> is_Done (f (the (result x))) \<rbrakk> \<Longrightarrow> is_Done (bind_resumption x f)"
| "result (bind_resumption x f) = result x \<bind> result \<circ> f"
| "output (bind_resumption x f) = (if is_Done x then output (f (the (result x))) else output x)"
| "resume (bind_resumption x f) = (\<lambda>inp. if is_Done x then resume (f (the (result x))) inp else bind_resumption (resume x inp) f)"

declare bind_resumption.sel [simp del]

adhoc_overloading Monad_Syntax.bind bind_resumption

lemma is_Done_bind_resumption [simp]:
  "is_Done (x \<bind> f) \<longleftrightarrow> is_Done x \<and> (result x \<noteq> None \<longrightarrow> is_Done (f (the (result x))))"
by(simp add: bind_resumption_def)

lemma result_bind_resumption [simp]:
  "is_Done (x \<bind> f) \<Longrightarrow> result (x \<bind> f) = result x \<bind> result \<circ> f"
by(simp add: bind_resumption_def)

lemma output_bind_resumption [simp]:
  "\<not> is_Done (x \<bind> f) \<Longrightarrow> output (x \<bind> f) = (if is_Done x then output (f (the (result x))) else output x)"
by(simp add: bind_resumption_def)

lemma resume_bind_resumption [simp]:
  "\<not> is_Done (x \<bind> f) \<Longrightarrow>
  resume (x \<bind> f) = 
  (if is_Done x then resume (f (the (result x))) 
   else (\<lambda>inp. resume x inp \<bind> f))"
by(auto simp add: bind_resumption_def)

definition DONE :: "'a \<Rightarrow> ('a, 'out, 'in) resumption"
where "DONE = Done \<circ> Some"

definition ABORT :: "('a, 'out, 'in) resumption"
where "ABORT = Done None"

lemma [simp]:
  shows is_Done_DONE: "is_Done (DONE a)"
  and is_Done_ABORT: "is_Done ABORT"
  and result_DONE: "result (DONE a) = Some a"
  and result_ABORT: "result ABORT = None"
  and DONE_inject: "DONE a = DONE b \<longleftrightarrow> a = b"
  and DONE_neq_ABORT: "DONE a \<noteq> ABORT"
  and ABORT_neq_DONE: "ABORT \<noteq> DONE a"
  and ABORT_eq_Done: "\<And>a. ABORT = Done a \<longleftrightarrow> a = None"
  and Done_eq_ABORT: "\<And>a. Done a = ABORT \<longleftrightarrow> a = None"
  and DONE_eq_Done: "\<And>b. DONE a = Done b \<longleftrightarrow> b = Some a"
  and Done_eq_DONE: "\<And>b. Done b = DONE a \<longleftrightarrow> b = Some a"
  and DONE_neq_Pause: "DONE a \<noteq> Pause out c"
  and Pause_neq_DONE: "Pause out c \<noteq> DONE a"
  and ABORT_neq_Pause: "ABORT \<noteq> Pause out c"
  and Pause_neq_ABORT: "Pause out c \<noteq> ABORT"
by(auto simp add: DONE_def ABORT_def)

lemma resume_ABORT [simp]:
  "resume (Done r) = (\<lambda>inp. ABORT)"
by(simp add: ABORT_def)

declare resumption.sel(3)[simp del]

lemma results_DONE [simp]: "results (DONE x) = {x}"
by(simp add: DONE_def)

lemma results_ABORT [simp]: "results ABORT = {}"
by(simp add: ABORT_def)

lemma outputs_ABORT [simp]: "outputs ABORT = {}"
by(simp add: ABORT_def)

lemma outputs_DONE [simp]: "outputs (DONE x) = {}"
by(simp add: DONE_def)

lemma is_Done_cases [cases pred]:
  assumes "is_Done r"
  obtains (DONE) x where "r = DONE x" | (ABORT) "r = ABORT"
using assms by(cases r) auto

lemma not_is_Done_conv_Pause: "\<not> is_Done r \<longleftrightarrow> (\<exists>out c. r = Pause out c)"
by(cases r) auto

lemma Done_bind [code]:
  "Done a \<bind> f = (case a of None \<Rightarrow> Done None | Some a \<Rightarrow> f a)"
by(rule resumption.expand)(auto split: option.split)

lemma DONE_bind [simp]:
  "DONE a \<bind> f = f a"
by(simp add: DONE_def Done_bind)

lemma bind_resumption_Pause [simp, code]: fixes cont shows
  "Pause out cont \<bind> f
  = Pause out (\<lambda>inp. cont inp \<bind> f)"
by(rule resumption.expand)(simp_all)

lemma bind_DONE [simp]:
  "x \<bind> DONE = x"
by(coinduction arbitrary: x)(auto simp add: split_beta o_def)

lemma bind_bind_resumption:
  fixes r :: "('a, 'in, 'out) resumption" 
  shows "(r \<bind> f) \<bind> g = do { x \<leftarrow> r; f x \<bind> g }"
apply(coinduction arbitrary: r rule: resumption.coinduct_strong)
apply(auto simp add: split_beta bind_eq_Some_conv)
apply(case_tac [!] "result r")
apply simp_all
done

lemmas resumption_monad = DONE_bind bind_DONE bind_bind_resumption

lemma ABORT_bind [simp]: "ABORT \<bind> f = ABORT"
by(simp add: ABORT_def Done_bind)

lemma bind_resumption_is_Done: "is_Done f \<Longrightarrow> f \<bind> g = (if result f = None then ABORT else g (the (result f)))"
by(rule resumption.expand) auto

lemma bind_resumption_eq_Done_iff [simp]:
  "f \<bind> g = Done x \<longleftrightarrow> (\<exists>y. f = DONE y \<and> g y = Done x) \<or> f = ABORT \<and> x = None"
by(cases f)(auto simp add: Done_bind split: option.split)

lemma bind_resumption_cong:
  assumes "x = y"
  and "\<And>z. z \<in> results y \<Longrightarrow> f z = g z"
  shows "x \<bind> f = y \<bind> g"
using assms(2) unfolding \<open>x = y\<close>
proof(coinduction arbitrary: y rule: resumption.coinduct_strong)
  case Eq_resumption thus ?case
    by(auto intro: resumption.set_sel simp add: is_Done_def rel_fun_def)
      (fastforce del: exI intro!: exI intro: resumption.set_sel(2) simp add: is_Done_def)
qed

lemma results_bind_resumption: (* Move to Resumption *)
  "results (bind_resumption x f) = (\<Union>a\<in>results x. results (f a))"
  (is "?lhs = ?rhs")
proof(intro set_eqI iffI)
  show "z \<in> ?rhs" if "z \<in> ?lhs" for z using that
  proof(induction r\<equiv>"x \<bind> f" arbitrary: x)
    case (Done z z' x)
    from Done(1) Done(2)[symmetric] show ?case by(auto)
  next
    case (Pause out c r z x)
    then show ?case
    proof(cases x)
      case (Done x')
      show ?thesis
      proof(cases x')
        case None
        with Done Pause(4) show ?thesis by(auto simp add: ABORT_def[symmetric])
      next
        case (Some x'')
        thus ?thesis using Pause(1,2,4) Done
          by(auto 4 3 simp add: DONE_def[unfolded o_def, symmetric, unfolded fun_eq_iff] dest: sym)
      qed
    qed(fastforce)
  qed
next
  fix z 
  assume "z \<in> ?rhs"
  then obtain z' where z': "z' \<in> results x"
    and z: "z \<in> results (f z')" by blast
  from z' show "z \<in> ?lhs"
  proof(induction z'\<equiv>z' x)
    case (Done r)
    then show ?case using z
      by(auto simp add: DONE_def[unfolded o_def, symmetric, unfolded fun_eq_iff])
  qed auto
qed

lemma outputs_bind_resumption [simp]:
  "outputs (bind_resumption r f) = outputs r \<union> (\<Union>x\<in>results r. outputs (f x))"
  (is "?lhs = ?rhs")
proof(rule set_eqI iffI)+
  show "x \<in> ?rhs" if "x \<in> ?lhs" for x using that
  proof(induction r'\<equiv>"bind_resumption r f" arbitrary: r)
    case (Pause1 out c)
    thus ?case by(cases r)(auto simp add: Done_bind split: option.split_asm dest: sym)
  next
    case (Pause2 out c r' x)
    thus ?case by(cases r)(auto 4 3 simp add: Done_bind split: option.split_asm dest: sym)
  qed
next
  fix x
  assume "x \<in> ?rhs"
  then consider (left) "x \<in> outputs r" | (right) a where "a \<in> results r" "x \<in> outputs (f a)" by auto
  then show "x \<in> ?lhs"
  proof cases
    { case left  thus ?thesis by induction auto }
    { case right thus ?thesis by induction(auto simp add: Done_bind) }
  qed
qed

primrec ensure :: "bool \<Rightarrow> (unit, 'out, 'in) resumption"
where
  "ensure True = DONE ()" 
| "ensure False = ABORT"

lemma is_Done_map_resumption [simp]:
  "is_Done (map_resumption f1 f2 r) \<longleftrightarrow> is_Done r"
by(cases r) simp_all

lemma result_map_resumption [simp]: 
  "is_Done r \<Longrightarrow> result (map_resumption f1 f2 r) = map_option f1 (result r)"
by(clarsimp simp add: is_Done_def)

lemma output_map_resumption [simp]:
  "\<not> is_Done r \<Longrightarrow> output (map_resumption f1 f2 r) = f2 (output r)"
by(cases r) simp_all

lemma resume_map_resumption [simp]:
  "\<not> is_Done r
  \<Longrightarrow> resume (map_resumption f1 f2 r) = map_resumption f1 f2 \<circ> resume r"
by(cases r) simp_all

lemma rel_resumption_is_DoneD: "rel_resumption A B r1 r2 \<Longrightarrow> is_Done r1 \<longleftrightarrow> is_Done r2"
by(cases r1 r2 rule: resumption.exhaust[case_product resumption.exhaust]) simp_all

lemma rel_resumption_resultD1:
  "\<lbrakk> rel_resumption A B r1 r2; is_Done r1 \<rbrakk> \<Longrightarrow> rel_option A (result r1) (result r2)"
by(cases r1 r2 rule: resumption.exhaust[case_product resumption.exhaust]) simp_all

lemma rel_resumption_resultD2:
  "\<lbrakk> rel_resumption A B r1 r2; is_Done r2 \<rbrakk> \<Longrightarrow> rel_option A (result r1) (result r2)"
by(cases r1 r2 rule: resumption.exhaust[case_product resumption.exhaust]) simp_all

lemma rel_resumption_outputD1:
  "\<lbrakk> rel_resumption A B r1 r2; \<not> is_Done r1 \<rbrakk> \<Longrightarrow> B (output r1) (output r2)"
by(cases r1 r2 rule: resumption.exhaust[case_product resumption.exhaust]) simp_all

lemma rel_resumption_outputD2:
  "\<lbrakk> rel_resumption A B r1 r2; \<not> is_Done r2 \<rbrakk> \<Longrightarrow> B (output r1) (output r2)"
by(cases r1 r2 rule: resumption.exhaust[case_product resumption.exhaust]) simp_all

lemma rel_resumption_resumeD1:
  "\<lbrakk> rel_resumption A B r1 r2; \<not> is_Done r1 \<rbrakk>
  \<Longrightarrow> rel_resumption A B (resume r1 inp) (resume r2 inp)"
by(cases r1 r2 rule: resumption.exhaust[case_product resumption.exhaust])(auto dest: rel_funD)

lemma rel_resumption_resumeD2:
  "\<lbrakk> rel_resumption A B r1 r2; \<not> is_Done r2 \<rbrakk>
  \<Longrightarrow> rel_resumption A B (resume r1 inp) (resume r2 inp)"
by(cases r1 r2 rule: resumption.exhaust[case_product resumption.exhaust])(auto dest: rel_funD)

lemma rel_resumption_coinduct
  [consumes 1, case_names Done Pause,
   case_conclusion Done is_Done result,
   case_conclusion Pause "output" resume,
   coinduct pred: rel_resumption]:
  assumes X: "X r1 r2"
  and Done: "\<And>r1 r2. X r1 r2 \<Longrightarrow> (is_Done r1 \<longleftrightarrow> is_Done r2) \<and> (is_Done r1 \<longrightarrow> is_Done r2 \<longrightarrow> rel_option A (result r1) (result r2))"
  and Pause: "\<And>r1 r2. \<lbrakk> X r1 r2; \<not> is_Done r1; \<not> is_Done r2 \<rbrakk> \<Longrightarrow> B (output r1) (output r2) \<and> (\<forall>inp. X (resume r1 inp) (resume r2 inp))" 
  shows "rel_resumption A B r1 r2"
using X
apply(rule resumption.rel_coinduct)
apply(unfold rel_fun_def)
apply(rule conjI)
 apply(erule Done[THEN conjunct1])
apply(rule conjI)
 apply(erule Done[THEN conjunct2])
apply(rule impI)+
apply(drule (2) Pause)
apply blast
done

subsection \<open>Setup for \<open>partial_function\<close>\<close>

context includes lifting_syntax begin

coinductive resumption_ord :: "('a, 'out, 'in) resumption \<Rightarrow> ('a, 'out, 'in) resumption \<Rightarrow> bool"
where
  Done_Done: "flat_ord None a a' \<Longrightarrow> resumption_ord (Done a) (Done a')"
| Done_Pause: "resumption_ord ABORT (Pause out c)"
| Pause_Pause: "((=) ===> resumption_ord) c c' \<Longrightarrow> resumption_ord (Pause out c) (Pause out c')"

inductive_simps resumption_ord_simps [simp]:
  "resumption_ord (Pause out c) r"
  "resumption_ord r (Done a)"

lemma resumption_ord_is_DoneD:
  "\<lbrakk> resumption_ord r r'; is_Done r' \<rbrakk> \<Longrightarrow> is_Done r"
by(cases r')(auto simp add: fun_ord_def)

lemma resumption_ord_resultD:
  "\<lbrakk> resumption_ord r r'; is_Done r' \<rbrakk> \<Longrightarrow> flat_ord None (result r) (result r')"
by(cases r')(auto simp add: flat_ord_def)

lemma resumption_ord_outputD:
  "\<lbrakk> resumption_ord r r'; \<not> is_Done r \<rbrakk> \<Longrightarrow> output r = output r'"
by(cases r) auto

lemma resumption_ord_resumeD:
  "\<lbrakk> resumption_ord r r'; \<not> is_Done r \<rbrakk> \<Longrightarrow> ((=) ===> resumption_ord) (resume r) (resume r')"
by(cases r) auto

lemma resumption_ord_abort:
  "\<lbrakk> resumption_ord r r'; is_Done r; \<not> is_Done r' \<rbrakk> \<Longrightarrow> result r = None"
by(auto elim: resumption_ord.cases)

lemma resumption_ord_coinduct [consumes 1, case_names Done Abort Pause, case_conclusion Pause "output" resume, coinduct pred: resumption_ord]:
  assumes "X r r'"
  and Done: "\<And>r r'. \<lbrakk> X r r'; is_Done r' \<rbrakk> \<Longrightarrow> is_Done r \<and> flat_ord None (result r) (result r')"
  and Abort: "\<And>r r'. \<lbrakk> X r r'; \<not> is_Done r'; is_Done r \<rbrakk> \<Longrightarrow> result r = None"
  and Pause: "\<And>r r'. \<lbrakk> X r r'; \<not> is_Done r; \<not> is_Done r' \<rbrakk> 
  \<Longrightarrow> output r = output r' \<and> ((=) ===> (\<lambda>r r'. X r r' \<or> resumption_ord r r')) (resume r) (resume r')"
  shows "resumption_ord r r'"
using \<open>X r r'\<close>
proof coinduct
  case (resumption_ord r r')
  thus ?case
    by(cases r r' rule: resumption.exhaust[case_product resumption.exhaust])(auto dest: Done Pause Abort)
qed

end

lemma resumption_ord_ABORT [intro!, simp]: "resumption_ord ABORT r"
by(cases r)(simp_all add: flat_ord_def resumption_ord.Done_Pause)

lemma resumption_ord_ABORT2 [simp]: "resumption_ord r ABORT \<longleftrightarrow> r = ABORT"
by(simp add: ABORT_def flat_ord_def)

lemma resumption_ord_DONE1 [simp]: "resumption_ord (DONE x) r \<longleftrightarrow> r = DONE x"
by(cases r)(auto simp add: option_ord_Some1_iff DONE_def dest: resumption_ord_abort)

lemma resumption_ord_refl: "resumption_ord r r"
by(coinduction arbitrary: r)(auto simp add: flat_ord_def)

lemma resumption_ord_antisym:
  "\<lbrakk> resumption_ord r r'; resumption_ord r' r \<rbrakk>
  \<Longrightarrow> r = r'"
proof(coinduction arbitrary: r r' rule: resumption.coinduct_strong)
  case (Eq_resumption r r')
  thus ?case
    by cases(auto simp add: flat_ord_def rel_fun_def)
qed

lemma resumption_ord_trans:
  "\<lbrakk> resumption_ord r r'; resumption_ord r' r'' \<rbrakk>
  \<Longrightarrow> resumption_ord r r''"
proof(coinduction arbitrary: r r' r'')
  case (Done r r' r'')
  thus ?case by(auto 4 4 elim: resumption_ord.cases simp add: flat_ord_def)
next
  case (Abort r r' r'')
  thus ?case by(auto 4 4 elim: resumption_ord.cases simp add: flat_ord_def)
next
  case (Pause r r' r'')
  hence "resumption_ord r r'" "resumption_ord r' r''" by simp_all
  thus ?case using \<open>\<not> is_Done r\<close> \<open>\<not> is_Done r''\<close>
    by(cases)(auto simp add: rel_fun_def)
qed

primcorec resumption_lub :: "('a, 'out, 'in) resumption set \<Rightarrow> ('a, 'out, 'in) resumption"
where
  "\<forall>r \<in> R. is_Done r \<Longrightarrow> is_Done (resumption_lub R)"
| "result (resumption_lub R) = flat_lub None (result ` R)"
| "output (resumption_lub R) = (THE out. out \<in> output ` (R \<inter> {r. \<not> is_Done r}))"
| "resume (resumption_lub R) = (\<lambda>inp. resumption_lub ((\<lambda>c. c inp) ` resume ` (R \<inter> {r. \<not> is_Done r})))"

lemma is_Done_resumption_lub [simp]:
  "is_Done (resumption_lub R) \<longleftrightarrow> (\<forall>r \<in> R. is_Done r)"
by(simp add: resumption_lub_def)

lemma result_resumption_lub [simp]:
  "\<forall>r \<in> R. is_Done r \<Longrightarrow> result (resumption_lub R) = flat_lub None (result ` R)"
by(simp add: resumption_lub_def)

lemma output_resumption_lub [simp]:
  "\<exists>r\<in>R. \<not> is_Done r \<Longrightarrow> output (resumption_lub R) = (THE out. out \<in> output ` (R \<inter> {r. \<not> is_Done r}))"
by(simp add: resumption_lub_def)

lemma resume_resumption_lub [simp]:
  "\<exists>r\<in>R. \<not> is_Done r
  \<Longrightarrow> resume (resumption_lub R) inp = 
     resumption_lub ((\<lambda>c. c inp) ` resume ` (R \<inter> {r. \<not> is_Done r}))"
by(simp add: resumption_lub_def)

lemma resumption_lub_empty: "resumption_lub {} = ABORT"
by(subst resumption_lub.code)(simp add: flat_lub_def)

context
  fixes R state inp R'
  defines R'_def: "R' \<equiv> (\<lambda>c. c inp) ` resume ` (R \<inter> {r. \<not> is_Done r})"
  assumes chain: "Complete_Partial_Order.chain resumption_ord R"
begin

lemma resumption_ord_chain_resume: "Complete_Partial_Order.chain resumption_ord R'"
proof(rule chainI)
  fix r' r''
  assume "r' \<in> R'"
    and "r'' \<in> R'"
  then obtain \<r>' \<r>'' 
    where r': "r' = resume \<r>' inp" "\<r>' \<in> R" "\<not> is_Done \<r>'"
    and r'': "r'' = resume \<r>'' inp" "\<r>'' \<in> R" "\<not> is_Done \<r>''"
    by(auto simp add: R'_def)
  from chain \<open>\<r>' \<in> R\<close> \<open>\<r>'' \<in> R\<close>
  have "resumption_ord \<r>' \<r>'' \<or> resumption_ord \<r>'' \<r>'"
    by(auto elim: chainE)
  with r' r''
  have "resumption_ord (resume \<r>' inp) (resume \<r>'' inp) \<or>
        resumption_ord (resume \<r>'' inp) (resume \<r>' inp)"
    by(auto elim: resumption_ord.cases simp add: rel_fun_def)
  with r' r''
  show "resumption_ord r' r'' \<or> resumption_ord r'' r'" by auto
qed

end

lemma resumption_partial_function_definition:
  "partial_function_definitions resumption_ord resumption_lub"
proof
  show "resumption_ord r r" for r :: "('a, 'b, 'c) resumption" by(rule resumption_ord_refl)
  show "resumption_ord r r''" if "resumption_ord r r'" "resumption_ord r' r''"
    for r r' r'' :: "('a, 'b, 'c) resumption" using that by(rule resumption_ord_trans)
  show "r = r'" if "resumption_ord r r'" "resumption_ord r' r" for r r' :: "('a, 'b, 'c) resumption"
    using that by(rule resumption_ord_antisym)
next
  fix R and r :: "('a, 'b, 'c) resumption"
  assume "Complete_Partial_Order.chain resumption_ord R" "r \<in> R"
  thus "resumption_ord r (resumption_lub R)"
  proof(coinduction arbitrary: r R)
    case (Done r R)
    note chain = \<open>Complete_Partial_Order.chain resumption_ord R\<close>
      and r = \<open>r \<in> R\<close>
    from \<open>is_Done (resumption_lub R)\<close> have A: "\<forall>r \<in> R. is_Done r" by simp
    with r obtain a' where "r = Done a'" by(cases r) auto
    { fix r'
      assume "a' \<noteq> None"
      hence "(THE x. x \<in> result ` R \<and> x \<noteq> None) = a'"
        using r A \<open>r = Done a'\<close>
        by(auto 4 3 del: the_equality intro!: the_equality intro: rev_image_eqI elim: chainE[OF chain] simp add: flat_ord_def is_Done_def) 
    }
    with A r \<open>r = Done a'\<close> show ?case
      by(cases a')(auto simp add: flat_ord_def flat_lub_def)
  next
    case (Abort r R)
    hence chain: "Complete_Partial_Order.chain resumption_ord R" and "r \<in> R" by simp_all
    from \<open>r \<in> R\<close> \<open>\<not> is_Done (resumption_lub R)\<close> \<open>is_Done r\<close>
    show ?case by(auto elim: chainE[OF chain] dest: resumption_ord_abort resumption_ord_is_DoneD)
  next
    case (Pause r R)
    hence chain: "Complete_Partial_Order.chain resumption_ord R"
      and r: "r \<in> R" by simp_all
    have ?resume 
      using r \<open>\<not> is_Done r\<close> resumption_ord_chain_resume[OF chain]
      by(auto simp add: rel_fun_def bexI)
    moreover
    from r \<open>\<not> is_Done r\<close> have "output (resumption_lub R) = output r"
      by(auto 4 4 simp add: bexI del: the_equality intro!: the_equality elim: chainE[OF chain] dest: resumption_ord_outputD)
    ultimately show ?case by simp
  qed
next
  fix R and r :: "('a, 'b, 'c) resumption"
  assume "Complete_Partial_Order.chain resumption_ord R" "\<And>r'. r' \<in> R \<Longrightarrow> resumption_ord r' r"
  thus "resumption_ord (resumption_lub R) r"
  proof(coinduction arbitrary: R r)
    case (Done R r)
    hence chain: "Complete_Partial_Order.chain resumption_ord R"
      and ub: "\<forall>r'\<in>R. resumption_ord r' r" by simp_all
    from \<open>is_Done r\<close> ub have is_Done: "\<forall>r' \<in> R. is_Done r'"
      and ub': "\<And>r'. r' \<in> result ` R \<Longrightarrow> flat_ord None r' (result r)"
      by(auto dest: resumption_ord_is_DoneD resumption_ord_resultD)
    from is_Done have chain': "Complete_Partial_Order.chain (flat_ord None) (result ` R)"
      by(auto 5 2 intro!: chainI elim: chainE[OF chain] dest: resumption_ord_resultD)
    hence "flat_ord None (flat_lub None (result ` R)) (result r)"
      by(rule partial_function_definitions.lub_least[OF flat_interpretation])(rule ub')
    thus ?case using is_Done by simp
  next
    case (Abort R r)
    hence chain: "Complete_Partial_Order.chain resumption_ord R"
      and ub: "\<forall>r'\<in>R. resumption_ord r' r" by simp_all
    from \<open>\<not> is_Done r\<close> \<open>is_Done (resumption_lub R)\<close> ub
    show ?case by(auto simp add: flat_lub_def dest: resumption_ord_abort)
  next
    case (Pause R r)
    hence chain: "Complete_Partial_Order.chain resumption_ord R"
      and ub: "\<And>r'. r'\<in>R \<Longrightarrow> resumption_ord r' r" by simp_all
    from \<open>\<not> is_Done (resumption_lub R)\<close> have exR: "\<exists>r \<in> R. \<not> is_Done r" by simp
    then obtain r' where r': "r' \<in> R" "\<not> is_Done r'" by auto
    with ub[of r'] have "output r = output r'" by(auto dest: resumption_ord_outputD)
    also have [symmetric]: "output (resumption_lub R) = output r'" using exR r'
      by(auto 4 4 elim: chainE[OF chain] dest: resumption_ord_outputD)
    finally have ?output ..
    moreover 
    { fix inp r''
      assume "r'' \<in> R" "\<not> is_Done r''"
      with ub[of r'']
      have "resumption_ord (resume r'' inp) (resume r inp)"
        by(auto dest!: resumption_ord_resumeD simp add: rel_fun_def) }
    with exR resumption_ord_chain_resume[OF chain] r'
    have ?resume by(auto simp add: rel_fun_def)
    ultimately show ?case ..
  qed
qed

interpretation resumption:
  partial_function_definitions resumption_ord resumption_lub
  rewrites "resumption_lub {} = (ABORT :: ('a, 'b, 'c) resumption)"
by (rule resumption_partial_function_definition resumption_lub_empty)+

declaration \<open>Partial_Function.init "resumption" @{term resumption.fixp_fun}
  @{term resumption.mono_body} @{thm resumption.fixp_rule_uc} @{thm resumption.fixp_induct_uc} NONE\<close>

abbreviation "mono_resumption \<equiv> monotone (fun_ord resumption_ord) resumption_ord"

lemma mono_resumption_resume:
  assumes "mono_resumption B"
  shows "mono_resumption (\<lambda>f. resume (B f) inp)"
proof
  fix f g :: "'a \<Rightarrow> ('b, 'c, 'd) resumption"
  assume fg: "fun_ord resumption_ord f g"
  hence "resumption_ord (B f) (B g)" by(rule monotoneD[OF assms])
  with resumption_ord_resumeD[OF this]
  show "resumption_ord (resume (B f) inp) (resume (B g) inp)"
    by(cases "is_Done (B f)")(auto simp add: rel_fun_def is_Done_def)
qed

lemma bind_resumption_mono [partial_function_mono]:
  assumes mf: "mono_resumption B"
  and mg: "\<And>y. mono_resumption (C y)"
  shows "mono_resumption (\<lambda>f. do { y \<leftarrow> B f; C y f })"
proof(rule monotoneI)
  fix f g :: "'a \<Rightarrow> ('b, 'c, 'd) resumption"
  assume *: "fun_ord resumption_ord f g"
  define f' where "f' \<equiv> B f" define g' where "g' \<equiv> B g"
  define h where "h \<equiv> \<lambda>x. C x f" define k where "k \<equiv> \<lambda>x. C x g"
  from mf[THEN monotoneD, OF *] mg[THEN monotoneD, OF *] f'_def g'_def h_def k_def
  have "resumption_ord f' g'" "\<And>x. resumption_ord (h x) (k x)" by auto
  thus "resumption_ord (f' \<bind> h) (g' \<bind> k)"
  proof(coinduction arbitrary: f' g' h k)
    case (Done f' g' h k)
    hence le: "resumption_ord f' g'"
      and mg: "\<And>y. resumption_ord (h y) (k y)" by simp_all
    from \<open>is_Done (g' \<bind> k)\<close>
    have done_Bg: "is_Done g'" 
      and "result g' \<noteq> None \<Longrightarrow> is_Done (k (the (result g')))" by simp_all
    moreover
    have "is_Done f'" using le done_Bg by(rule resumption_ord_is_DoneD)
    moreover
    from le done_Bg have "flat_ord None (result f') (result g')"
      by(rule resumption_ord_resultD)
    hence "result f' \<noteq> None \<Longrightarrow> result g' = result f'"
      by(auto simp add: flat_ord_def)
    moreover
    have "resumption_ord (h (the (result f'))) (k (the (result f')))" by(rule mg)
    ultimately show ?case
      by(subst (1 2) result_bind_resumption)(auto dest: resumption_ord_is_DoneD resumption_ord_resultD simp add: flat_ord_def bind_eq_None_conv)
  next
    case (Abort f' g' h k)
    hence "resumption_ord (h (the (result f'))) (k (the (result f')))" by simp
    thus ?case using Abort
      by(cases "is_Done g'")(auto 4 4 simp add: bind_eq_None_conv flat_ord_def dest: resumption_ord_abort resumption_ord_resultD resumption_ord_is_DoneD)
  next
    case (Pause f' g' h k)
    hence ?output
      by(auto 4 4 dest: resumption_ord_outputD resumption_ord_is_DoneD resumption_ord_resultD resumption_ord_abort simp add: flat_ord_def)
    moreover have ?resume
    proof(cases "is_Done f'")
      case False
      with Pause show ?thesis
        by(auto simp add: rel_fun_def dest: resumption_ord_is_DoneD intro: resumption_ord_resumeD[THEN rel_funD] del: exI intro!: exI)
    next
      case True
      hence "is_Done g'" using Pause by(auto dest: resumption_ord_abort)
      thus ?thesis using True Pause resumption_ord_resultD[OF \<open>resumption_ord f' g'\<close>]
        by(auto del: rel_funI intro!: rel_funI simp add: bind_resumption_is_Done flat_ord_def intro: resumption_ord_resumeD[THEN rel_funD] exI[where x=f'] exI[where x=g'])
    qed
    ultimately show ?case ..
  qed
qed

lemma fixes f F
  defines "F \<equiv> \<lambda>results r. case r of resumption.Done x \<Rightarrow> set_option x | resumption.Pause out c \<Rightarrow> \<Union>input. results (c input)"
  shows results_conv_fixp: "results \<equiv> ccpo.fixp (fun_lub Union) (fun_ord (\<subseteq>)) F" (is "_ \<equiv> ?fixp")
  and results_mono: "\<And>x. monotone (fun_ord (\<subseteq>)) (\<subseteq>) (\<lambda>f. F f x)" (is "PROP ?mono")
proof(rule eq_reflection ext antisym subsetI)+
  show mono: "PROP ?mono" unfolding F_def by(tactic \<open>Partial_Function.mono_tac @{context} 1\<close>)
  fix x r
  show "?fixp r \<subseteq> results r"
    by(induction arbitrary: r rule: lfp.fixp_induct_uc[of "\<lambda>x. x" F "\<lambda>x. x", OF mono reflexive refl])
      (fastforce simp add: F_def split: resumption.split_asm)+

  assume "x \<in> results r"
  thus "x \<in> ?fixp r" by induct(subst lfp.mono_body_fixp[OF mono]; auto simp add: F_def)+
qed

lemma mcont_case_resumption:
  fixes f g
  defines "h \<equiv> \<lambda>r. if is_Done r then f (result r) else g (output r) (resume r) r"
  assumes mcont1: "mcont (flat_lub None) option_ord lub ord f"
  and mcont2: "\<And>out. mcont (fun_lub resumption_lub) (fun_ord resumption_ord) lub ord (\<lambda>c. g out c (Pause out c))"
  and ccpo: "class.ccpo lub ord (mk_less ord)"
  and bot: "\<And>x. ord (f None) x"
  shows "mcont resumption_lub resumption_ord lub ord (\<lambda>r. case r of Done x \<Rightarrow> f x | Pause out c \<Rightarrow> g out c r)"
    (is "mcont ?lub ?ord _ _ ?f")
proof(rule resumption.mcont_if_bot[OF ccpo bot, where bound=ABORT and f=h])
  show "?f x = (if ?ord x ABORT then f None else h x)" for x
    by(simp add: h_def split: resumption.split)
  show "ord (h x) (h y)" if "?ord x y" "\<not> ?ord x ABORT" for x y using that
    by(cases x)(simp_all add: h_def mcont_monoD[OF mcont1] fun_ord_conv_rel_fun mcont_monoD[OF mcont2])
    
  fix Y :: "('a, 'b, 'c) resumption set"
  assume chain: "Complete_Partial_Order.chain ?ord Y"
    and Y: "Y \<noteq> {}"
    and nbot: "\<And>x. x \<in> Y \<Longrightarrow> \<not> ?ord x ABORT"
  show "h (?lub Y) = lub (h ` Y)"
  proof(cases "\<exists>x. DONE x \<in> Y")
    case True
    then obtain x where x: "DONE x \<in> Y" ..
    have is_Done: "is_Done r" if "r \<in> Y" for r using chainD[OF chain that x]
      by(auto dest: resumption_ord_is_DoneD)
    from is_Done have chain': "Complete_Partial_Order.chain (flat_ord None) (result ` Y)"
      by(auto 5 2 intro!: chainI elim: chainE[OF chain] dest: resumption_ord_resultD)
    from is_Done have "is_Done (?lub Y)" "Y \<inter> {r. is_Done r} = Y" "Y \<inter> {r. \<not> is_Done r} = {}" by auto
    then show ?thesis using Y by(simp add: h_def mcont_contD[OF mcont1 chain'] image_image)
  next
    case False
    have is_Done: "\<not> is_Done r" if "r \<in> Y" for r using that False nbot
      by(auto elim!: is_Done_cases)
    from Y obtain out c where Pause: "Pause out c \<in> Y"
      by(auto 5 2 dest: is_Done iff: not_is_Done_conv_Pause)
    
    have out: "(THE out. out \<in> output ` (Y \<inter> {r. \<not> is_Done r})) = out" using Pause
      by(auto 4 3 intro: rev_image_eqI iff: not_is_Done_conv_Pause dest: chainD[OF chain])
    have "(\<lambda>r. g (output r) (resume r) r) ` (Y \<inter> {r. \<not> is_Done r}) = (\<lambda>r. g out (resume r) r) ` (Y \<inter> {r. \<not> is_Done r})"
      by(auto 4 3 simp add: not_is_Done_conv_Pause dest: chainD[OF chain Pause] intro: rev_image_eqI)
    moreover have "\<not> is_Done (?lub Y)" using Y is_Done by(auto)
    moreover from is_Done have "Y \<inter> {r. is_Done r} = {}" "Y \<inter> {r. \<not> is_Done r} = Y" by auto
    moreover have "(\<lambda>inp. resumption_lub ((\<lambda>x. resume x inp) ` Y)) = fun_lub resumption_lub (resume ` Y)"
      by(auto simp add: fun_lub_def fun_eq_iff intro!: arg_cong[where f="resumption_lub"])
    moreover have "resumption_lub Y = Pause out (fun_lub resumption_lub (resume ` Y))"
      using Y is_Done out
      by(intro resumption.expand)(auto simp add: fun_lub_def fun_eq_iff image_image intro!: arg_cong[where f=resumption_lub])
    moreover have chain': "Complete_Partial_Order.chain resumption.le_fun (resume ` Y)" using chain
      by(rule chain_imageI)(auto dest!: is_Done simp add: not_is_Done_conv_Pause fun_ord_conv_rel_fun)
    moreover have "(\<lambda>r. g out (resume r) (Pause out (resume r))) ` Y = (\<lambda>r. g out (resume r) r) ` Y"
      by(intro image_cong[OF refl])(frule nbot; auto dest!: chainD[OF chain Pause] elim: resumption_ord.cases)
    ultimately show ?thesis using False out Y 
      by(simp add: h_def image_image mcont_contD[OF mcont2])
  qed
qed
    
lemma mcont2mcont_results[THEN mcont2mcont, cont_intro, simp]:
  shows mcont_results: "mcont resumption_lub resumption_ord Union (\<subseteq>) results"
apply(rule lfp.fixp_preserves_mcont1[OF results_mono results_conv_fixp])
apply(rule mcont_case_resumption)
apply(simp_all add: mcont_applyI)
done

lemma mono2mono_results[THEN lfp.mono2mono, cont_intro, simp]:
  shows monotone_results: "monotone resumption_ord (\<subseteq>) results"
using mcont_results by(rule mcont_mono)

lemma fixes f F
  defines "F \<equiv> \<lambda>outputs xs. case xs of resumption.Done x \<Rightarrow> {} | resumption.Pause out c \<Rightarrow> insert out (\<Union>input. outputs (c input))"
  shows outputs_conv_fixp: "outputs \<equiv> ccpo.fixp (fun_lub Union) (fun_ord (\<subseteq>)) F" (is "_ \<equiv> ?fixp")
  and outputs_mono: "\<And>x. monotone (fun_ord (\<subseteq>)) (\<subseteq>) (\<lambda>f. F f x)" (is "PROP ?mono")
proof(rule eq_reflection ext antisym subsetI)+
  show mono: "PROP ?mono" unfolding F_def by(tactic \<open>Partial_Function.mono_tac @{context} 1\<close>)
  show "?fixp r \<subseteq> outputs r" for r
    by(induct arbitrary: r rule: lfp.fixp_induct_uc[of "\<lambda>x. x" F "\<lambda>x. x", OF mono reflexive refl])(auto simp add: F_def split: resumption.split)
  show "x \<in> ?fixp r" if "x \<in> outputs r" for x r using that
    by induct(subst lfp.mono_body_fixp[OF mono]; auto simp add: F_def; fail)+
qed

lemma mcont2mcont_outputs[THEN lfp.mcont2mcont, cont_intro, simp]: 
  shows mcont_outputs: "mcont resumption_lub resumption_ord Union (\<subseteq>) outputs"
apply(rule lfp.fixp_preserves_mcont1[OF outputs_mono outputs_conv_fixp])
apply(auto intro: lfp.mcont2mcont intro!: mcont2mcont_insert mcont_SUP mcont_case_resumption)
done

lemma mono2mono_outputs[THEN lfp.mono2mono, cont_intro, simp]:
  shows monotone_outputs: "monotone resumption_ord (\<subseteq>) outputs"
using mcont_outputs by(rule mcont_mono)

lemma pred_resumption_antimono:
  assumes r: "pred_resumption A C r'"
  and le: "resumption_ord r r'"
  shows "pred_resumption A C r"
using r monotoneD[OF monotone_results le] monotoneD[OF monotone_outputs le]
by(auto simp add: pred_resumption_def)

subsection \<open>Setup for lifting and transfer\<close>

declare resumption.rel_eq [id_simps, relator_eq]
declare resumption.rel_mono [relator_mono]

lemma rel_resumption_OO [relator_distr]:
  "rel_resumption A B OO rel_resumption C D = rel_resumption (A OO C) (B OO D)" 
by(simp add: resumption.rel_compp)

lemma left_total_rel_resumption [transfer_rule]:
  "\<lbrakk> left_total R1; left_total R2 \<rbrakk> \<Longrightarrow> left_total (rel_resumption R1 R2)"
  by(simp only: left_total_alt_def resumption.rel_eq[symmetric] resumption.rel_conversep[symmetric] rel_resumption_OO resumption.rel_mono)

lemma left_unique_rel_resumption [transfer_rule]:
  "\<lbrakk> left_unique R1; left_unique R2 \<rbrakk> \<Longrightarrow> left_unique (rel_resumption R1 R2)"
  by(simp only: left_unique_alt_def resumption.rel_eq[symmetric] resumption.rel_conversep[symmetric] rel_resumption_OO resumption.rel_mono)

lemma right_total_rel_resumption [transfer_rule]:
  "\<lbrakk> right_total R1; right_total R2 \<rbrakk> \<Longrightarrow> right_total (rel_resumption R1 R2)"
  by(simp only: right_total_alt_def resumption.rel_eq[symmetric] resumption.rel_conversep[symmetric] rel_resumption_OO resumption.rel_mono)

lemma right_unique_rel_resumption [transfer_rule]:
  "\<lbrakk> right_unique R1; right_unique R2 \<rbrakk> \<Longrightarrow> right_unique (rel_resumption R1 R2)"
  by(simp only: right_unique_alt_def resumption.rel_eq[symmetric] resumption.rel_conversep[symmetric] rel_resumption_OO resumption.rel_mono)

lemma bi_total_rel_resumption [transfer_rule]:
  "\<lbrakk> bi_total A; bi_total B \<rbrakk> \<Longrightarrow> bi_total (rel_resumption A B)"
unfolding bi_total_alt_def
by(blast intro: left_total_rel_resumption right_total_rel_resumption)

lemma bi_unique_rel_resumption [transfer_rule]:
  "\<lbrakk> bi_unique A; bi_unique B \<rbrakk> \<Longrightarrow> bi_unique (rel_resumption A B)"
unfolding bi_unique_alt_def
by(blast intro: left_unique_rel_resumption right_unique_rel_resumption)

lemma Quotient_resumption [quot_map]:
  "\<lbrakk> Quotient R1 Abs1 Rep1 T1; Quotient R2 Abs2 Rep2 T2 \<rbrakk>
  \<Longrightarrow> Quotient (rel_resumption R1 R2) (map_resumption Abs1 Abs2) (map_resumption Rep1 Rep2) (rel_resumption T1 T2)"
  by(simp add: Quotient_alt_def5 resumption.rel_Grp[of UNIV _ UNIV _, symmetric, simplified] resumption.rel_compp resumption.rel_conversep[symmetric] resumption.rel_mono)

end
