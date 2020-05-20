(*  Title:        C2KA Behaviour Structure (Concurrent Kleene Algebra)
    Author:       Maxime Buyse <maxime.buyse at polytechnique.edu>, 2019
    Maintainers:  Maxime Buyse <maxime.buyse at polytechnique.edu> and Jason Jaskolka <jason.jaskolka at carleton.ca>
*)

section \<open>Behaviour Structure \label{sec:behaviour_structure}\<close>

text \<open>
Hoare et al.~\cite{Hoare2011aa} presented the framework of Concurrent Kleene Algebra (\CKAabbrv) which captures the concurrent 
behaviour of agents. The framework of \CKAabbrv is adopted to describe agent behaviours in distributed 
systems. For a \CKAabbrv~$\CKAstructure$,~$\CKAset$ is a set of possible behaviours. The operator~$+$ is 
interpreted as a choice between two behaviours, the operator~$\CKAseq$ is interpreted as a sequential 
composition of two behaviours, and the operator~$\CKApar$ is interpreted as a parallel composition of 
two behaviours. The operators~$\CKAiterSeq{\,}$ and~$\CKAiterPar{\,}$ are interpreted as a finite sequential 
iteration and a finite parallel iteration of behaviours, respectively. The element~$0$ represents the 
behaviour of the \emph{inactive agent} and the element~$1$ represents the behaviour of the \emph{idle agent}. 
Associated with a \CKAabbrv~$\cka$ is a natural ordering relation~$\CKAle$ related to the semirings upon which the 
\CKAabbrv is built which is called the sub-behaviour relation. For behaviours~$a,b \in \CKAset$, we 
write~$a \CKAle b$ and say that~$a$ is a sub-behaviour of~$b$ if and only if~$a + b = b$.
\<close>

theory CKA
  imports Main
begin

no_notation
rtrancl ("(_\<^sup>*)" [1000] 999)

notation
times (infixl "*" 70)
and less_eq  ("'(\<le>\<^sub>\<K>')") 
and less_eq  ("(_/ \<le>\<^sub>\<K> _)"  [51, 51] 50)

text \<open>
The class \emph{cka} contains an axiomatisation of Concurrent Kleene Algebras and a selection of useful theorems.\<close>

class join_semilattice = ordered_ab_semigroup_add +
  assumes leq_def: "x \<le> y \<longleftrightarrow> x + y = y"
  and le_def: "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"
  and add_idem [simp]: "x + x = x"
begin

lemma inf_add_K_right: "a \<le>\<^sub>\<K> a + b"
  unfolding leq_def
  by (simp add:  add_assoc[symmetric])

lemma inf_add_K_left: "a \<le>\<^sub>\<K> b + a"
  by (simp only: add_commute, fact inf_add_K_right)

end

class dioid = semiring + one + zero + join_semilattice +
  assumes par_onel [simp]: "1 * x = x"
  and par_oner [simp]: "x * 1 = x"
  and add_zerol [simp]: "0 + x = x"
  and annil [simp]: "0 * x = 0"
  and annir [simp]: "x * 0 = 0"

class kleene_algebra = dioid + 
  fixes star :: "'a \<Rightarrow> 'a" ("_\<^sup>*" [101] 100)
  assumes star_unfoldl: "1 + x * x\<^sup>* \<le>\<^sub>\<K> x\<^sup>*"  
  and star_unfoldr: "1 + x\<^sup>* * x \<le>\<^sub>\<K> x\<^sup>*"
  and star_inductl: "z + x * y \<le>\<^sub>\<K> y \<Longrightarrow> x\<^sup>* * z \<le>\<^sub>\<K> y"
  and star_inductr: "z + y * x \<le>\<^sub>\<K> y \<Longrightarrow> z * x\<^sup>* \<le>\<^sub>\<K> y"

class cka = kleene_algebra +
  fixes seq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";" 70)
  and seqstar :: "'a \<Rightarrow> 'a" ("_\<^sup>;" [101] 100)
  assumes seq_assoc: "x ; (y ; z) = (x ; y) ; z"
  and seq_rident [simp]: "x ; 1 = x"
  and seq_lident [simp]: "1 ; x = x"
  and seq_rdistrib [simp]: "(x + y);z = x;z + y;z"
  and seq_ldistrib [simp]: "x;(y + z) = x;y + x;z"
  and seq_annir [simp]: "x ; 0 = 0"
  and seq_annil [simp]: "0 ; x = 0" 
  and seqstar_unfoldl: "1 + x ; x\<^sup>; \<le>\<^sub>\<K> x\<^sup>;"  
  and seqstar_unfoldr: "1 + x\<^sup>; ; x \<le>\<^sub>\<K> x\<^sup>;"
  and seqstar_inductl: "z + x ; y \<le>\<^sub>\<K> y \<Longrightarrow> x\<^sup>; ; z \<le>\<^sub>\<K> y"
  and seqstar_inductr: "z + y ; x \<le>\<^sub>\<K> y \<Longrightarrow> z ; x\<^sup>; \<le>\<^sub>\<K> y"
  and exchange: "(a*b) ; (c*d) \<le>\<^sub>\<K> (b;c) * (a;d)"
begin

interpretation cka: kleene_algebra plus less_eq less "1" "0" seq seqstar
  by (unfold_locales, simp_all add: seq_assoc seqstar_unfoldl seqstar_unfoldr seqstar_inductl seqstar_inductr)

lemma par_comm: "a * b = b * a"
proof -
  have "(b*a) ; (1*1) \<le>\<^sub>\<K> (a;1) * (b;1)" by (simp only:  exchange)
  hence "b * a \<le>\<^sub>\<K> a * b" by (simp)
  hence "a * b \<le>\<^sub>\<K> b * a \<longleftrightarrow> a * b  = b * a" by (rule antisym_conv)
  moreover have "a * b \<le>\<^sub>\<K> b * a" proof -
  have "(a*b) ; (1*1) \<le>\<^sub>\<K> (b;1) * (a;1)" by (rule  exchange)
    thus ?thesis  by (simp)
  qed
  ultimately show ?thesis by (auto)
qed

lemma exchange_2: "(a*b) ; (c*d) \<le>\<^sub>\<K> (a;c) * (b;d)"
proof -
  have "(b*a) ; (c*d) \<le>\<^sub>\<K> (a;c) * (b;d)" by (rule exchange)
  thus ?thesis by (simp add: par_comm)
qed

lemma seq_inf_par: "a ; b \<le>\<^sub>\<K> a * b" 
proof -
  have "(1*a) ; (1*b) \<le>\<^sub>\<K> (a;1) * (1;b)" by (rule exchange)
  thus ?thesis by simp
qed

lemma add_seq_inf_par: "a;b + b;a \<le>\<^sub>\<K> a*b"
proof -
  have "a;b \<le>\<^sub>\<K> a*b" by (rule seq_inf_par)
  moreover have "b;a \<le>\<^sub>\<K> b*a" by (rule seq_inf_par)
  ultimately have "a;b + b;a \<le>\<^sub>\<K> a*b + b*a" by (simp add: add_mono)
  thus ?thesis by (simp add: par_comm)
qed

lemma exchange_3: "(a*b) ; c \<le>\<^sub>\<K> a * (b;c)"
proof -
  have "(a*b) ; (1*c) \<le>\<^sub>\<K> (a;1) * (b;c)" by (rule exchange_2)
  thus ?thesis by simp
qed

lemma exchange_4: "a ; (b*c) \<le>\<^sub>\<K> (a;b) * c"
proof -
  have "(1*a) ; (b*c) \<le>\<^sub>\<K> (a;b) * (1;c)" by (rule exchange)
  thus ?thesis by simp
qed

lemma seqstar_inf_parstar: "a\<^sup>; \<le>\<^sub>\<K> a\<^sup>*"
proof -
  have "a ; a\<^sup>* \<le>\<^sub>\<K> a * a\<^sup>*" by (rule seq_inf_par)
  hence "1 + a ; a\<^sup>* \<le>\<^sub>\<K> 1 + a * a\<^sup>*" by (simp add: add_left_mono)
  hence "1 + a ; a\<^sup>* \<le>\<^sub>\<K> a\<^sup>*" by (simp add: star_unfoldl order_trans)
  hence "a\<^sup>; ; 1 \<le>\<^sub>\<K> a\<^sup>*" by (rule seqstar_inductl)
  thus ?thesis by simp
qed

end

end
