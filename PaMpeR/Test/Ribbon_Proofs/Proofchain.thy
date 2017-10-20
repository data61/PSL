section {* Proof chains *}

theory Proofchain imports
  JHelper  
begin

text {* An (@{typ 'a}, @{typ 'c}) chain is a sequence of alternating 
  @{typ 'a}'s and @{typ 'c}'s, beginning and ending with an @{typ 'a}. Usually 
  @{typ 'a} represents some sort of assertion, and @{typ 'c} represents some 
  sort of command. Proof chains are useful for stating the SMain proof rule,
  and for conducting the proof of soundness. *}

datatype ('a,'c) chain = 
  cNil "'a"                         ("\<lbrace> _ \<rbrace>")
| cCons "'a" "'c" "('a,'c) chain"   ("\<lbrace> _ \<rbrace> \<cdot> _ \<cdot> _" [0,0,0] 60) 

text {* For example, @{term "\<lbrace> a \<rbrace> \<cdot> proof \<cdot> \<lbrace> chain \<rbrace> \<cdot> might \<cdot> \<lbrace> look \<rbrace> \<cdot> 
  like \<cdot> \<lbrace> this \<rbrace>"}. *}

subsection {* Projections *}

text {* Project first assertion. *}
fun
  pre :: "('a,'c) chain \<Rightarrow> 'a"
where
  "pre \<lbrace> P \<rbrace> = P"
| "pre (\<lbrace> P \<rbrace> \<cdot> _ \<cdot> _) = P"

text {* Project final assertion. *}
fun 
  post :: "('a,'c) chain \<Rightarrow> 'a"
where
  "post \<lbrace> P \<rbrace>  = P"
| "post (\<lbrace> _ \<rbrace> \<cdot> _ \<cdot> \<Pi>) = post \<Pi>"

text {* Project list of commands. *}
fun
  comlist :: "('a,'c) chain \<Rightarrow> 'c list"
where
  "comlist \<lbrace> _ \<rbrace> = []"
| "comlist (\<lbrace> _ \<rbrace> \<cdot> x \<cdot> \<Pi>) = x # (comlist \<Pi>)" 


subsection {* Chain length *}

fun
  chainlen :: "('a,'c) chain \<Rightarrow> nat"
where
  "chainlen \<lbrace> _ \<rbrace> = 0"
| "chainlen (\<lbrace> _ \<rbrace> \<cdot> _ \<cdot> \<Pi>) = 1 + (chainlen \<Pi>)"

lemma len_comlist_chainlen:
  "length (comlist \<Pi>) = chainlen \<Pi>"
by (induct \<Pi>, auto)

subsection {* Extracting triples from chains *}

text {* @{term "nthtriple \<Pi> n"} extracts the @{term n}th triple of @{term \<Pi>},
  counting from 0. The function is well-defined when @{term "chainlen \<Pi> > n"}. 
  *}
fun
  nthtriple :: "('a,'c) chain \<Rightarrow> nat \<Rightarrow> ('a * 'c * 'a)"
where
  "nthtriple (\<lbrace> P \<rbrace> \<cdot> x \<cdot> \<Pi>) 0 = (P, x, pre \<Pi>)"
| "nthtriple (\<lbrace> P \<rbrace> \<cdot> x \<cdot> \<Pi>) (Suc n) = nthtriple \<Pi> n"

text {* The list of middle components of @{term \<Pi>}'s triples is the list of
   @{term \<Pi>}'s commands. *}
lemma snds_of_triples_form_comlist:
  fixes \<Pi> i
  shows "i < chainlen \<Pi> \<Longrightarrow> snd3 (nthtriple \<Pi> i) = (comlist \<Pi>)!i"
apply (induct \<Pi> arbitrary: i)
apply simp
apply (case_tac i)
apply (auto simp add: snd3_def)
done

subsection {* Evaluating a predicate on each triple of a chain *}

text {* @{term "chain_all \<phi>"} holds of @{term \<Pi>} iff @{term \<phi>} holds for each
  of @{term \<Pi>}'s individual triples. *} 
fun
  chain_all :: "(('a \<times> 'c \<times> 'a) \<Rightarrow> bool) \<Rightarrow> ('a,'c) chain \<Rightarrow> bool"
where
  "chain_all \<phi> \<lbrace> \<sigma> \<rbrace> = True"
| "chain_all \<phi> (\<lbrace> \<sigma> \<rbrace> \<cdot> x \<cdot> \<Pi>) = (\<phi> (\<sigma>,x,pre \<Pi>) \<and> chain_all \<phi> \<Pi>)"

lemma chain_all_mono [mono]:
  "x \<le> y \<Longrightarrow> chain_all x \<le> chain_all y"
proof (intro le_funI le_boolI)
  fix f g :: "('a \<times> 'b \<times> 'a) \<Rightarrow> bool"
  fix \<Pi> :: "('a, 'b) chain"
  assume "f \<le> g"
  assume "chain_all f \<Pi>"
  thus "chain_all g \<Pi>"
  apply (induct \<Pi>)
  apply simp
  apply (metis `f \<le> g` chain_all.simps(2) predicate1D)
  done
qed
  
lemma chain_all_nthtriple:
  "(chain_all \<phi> \<Pi>) = (\<forall>i < chainlen \<Pi>. \<phi> (nthtriple \<Pi> i))"
proof (intro iffI allI impI)
  fix i
  assume "chain_all \<phi> \<Pi>" and "i < chainlen \<Pi>"
  thus "\<phi> (nthtriple \<Pi> i)"
  proof (induct i arbitrary: \<Pi>)
    case 0
    then obtain \<sigma> x \<Pi>' where \<Pi>_def: "\<Pi> = \<lbrace> \<sigma> \<rbrace> \<cdot> x \<cdot> \<Pi>'"
    by (metis chain.exhaust chainlen.simps(1) less_nat_zero_code)
    show ?case 
    by (insert "0.prems"(1), unfold \<Pi>_def, auto)
  next
    case (Suc i)
    then obtain \<sigma> x \<Pi>' where \<Pi>_def: "\<Pi> = \<lbrace> \<sigma> \<rbrace> \<cdot> x \<cdot> \<Pi>'"
    by (metis chain.exhaust chainlen.simps(1) less_nat_zero_code)
    show ?case
    apply (unfold \<Pi>_def nthtriple.simps)
    apply (intro Suc.hyps, insert Suc.prems, auto simp add: \<Pi>_def)
    done
  qed
next
  assume "\<forall>i<chainlen \<Pi>. \<phi> (nthtriple \<Pi> i)"
  hence "\<And>i. i < chainlen \<Pi> \<Longrightarrow> \<phi> (nthtriple \<Pi> i)" by auto
  thus "chain_all \<phi> \<Pi>"
  proof (induct \<Pi>)
    case (cCons \<sigma> x \<Pi>')
    show ?case
    apply (simp, intro conjI)
    apply (subgoal_tac "\<phi> (nthtriple (\<lbrace> \<sigma> \<rbrace> \<cdot> x \<cdot> \<Pi>') 0)", simp)
    apply (intro cCons.prems, simp)
    apply (intro cCons.hyps)
    proof -
      fix i
      assume "i < chainlen \<Pi>'"
      hence "Suc i < chainlen (\<lbrace> \<sigma> \<rbrace> \<cdot> x \<cdot> \<Pi>')" by auto
      from cCons.prems[OF this] show "\<phi> (nthtriple \<Pi>' i)" by auto
    qed
  qed(auto)
qed

subsection {* A map function for proof chains *}

text {* @{term "chainmap f g \<Pi>"} maps @{term f} over each of @{term \<Pi>}'s 
  assertions, and @{term g} over each of @{term \<Pi>}'s commands. *}
fun
  chainmap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('a,'c) chain \<Rightarrow> ('b,'d) chain"
where
  "chainmap f g \<lbrace> P \<rbrace> = \<lbrace> f P \<rbrace>"
| "chainmap f g (\<lbrace> P \<rbrace> \<cdot> x \<cdot> \<Pi>) = \<lbrace> f P \<rbrace> \<cdot> g x \<cdot> chainmap f g \<Pi>"

text {* Mapping over a chain preserves its length. *}
lemma chainmap_preserves_length: 
  "chainlen (chainmap f g \<Pi>) = chainlen \<Pi>"
by (induct \<Pi>, auto)

lemma pre_chainmap:
  "pre (chainmap f g \<Pi>) = f (pre \<Pi>)"
by (induct \<Pi>, auto)

lemma post_chainmap:
  "post (chainmap f g \<Pi>) = f (post \<Pi>)"
by (induct \<Pi>, auto)

lemma nthtriple_chainmap: 
  assumes "i < chainlen \<Pi>"
  shows "nthtriple (chainmap f g \<Pi>) i 
    = (\<lambda>t. (f (fst3 t), g (snd3 t), f (thd3 t))) (nthtriple \<Pi> i)"
using assms 
proof (induct \<Pi> arbitrary: i)
  case cCons
  thus ?case 
  by (induct i, auto simp add: pre_chainmap fst3_def snd3_def thd3_def)
qed (auto)

subsection {* Extending a chain on its right-hand side *}

fun
  cSnoc :: "('a,'c) chain \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> ('a,'c) chain"
where
  "cSnoc \<lbrace> \<sigma> \<rbrace> y \<tau> = \<lbrace> \<sigma> \<rbrace> \<cdot> y \<cdot> \<lbrace> \<tau> \<rbrace>"
| "cSnoc (\<lbrace> \<sigma> \<rbrace> \<cdot> x \<cdot> \<Pi>) y \<tau> = \<lbrace> \<sigma> \<rbrace> \<cdot> x \<cdot> (cSnoc \<Pi> y \<tau>)"

lemma len_snoc:
  fixes \<Pi> x P
  shows "chainlen (cSnoc \<Pi> x P) = 1 + (chainlen \<Pi>)"
by (induct \<Pi>, auto)

lemma pre_snoc: 
  "pre (cSnoc \<Pi> x P) = pre \<Pi>" 
by (induct \<Pi>, auto)

lemma post_snoc:
  "post (cSnoc \<Pi> x P) = P"
by (induct \<Pi>, auto)

lemma comlist_snoc:
  "comlist (cSnoc \<Pi> x p) = comlist \<Pi> @ [x]"
by (induct \<Pi>, auto)



end
