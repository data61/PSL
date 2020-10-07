subsubsection\<open>Tseytin transformation\<close>

theory Tseytin
imports Formulas CNF_Formulas
begin

text\<open>The @{const cnf} transformation clearly has exponential complexity.
If the intention is to use Resolution to decide validity of a formula,
that is clearly a deal-breaker for any practical implementation,
since validity can be decided by brute force in exponential time.
This theory pair shows the Tseytin transformation, a way to transform a formula
while preserving validity.
The @{const cnf} of the transformed formula will have clauses with maximally 3 atoms,
and an amount of clauses linear in the size of the formula,
at the cost of introducing one new atom for each subformula of \<open>F\<close> (i.e. @{term "size F"} many).
\<close>
  
definition "pair_fun_upd f p \<equiv> (case p of (k,v) \<Rightarrow> fun_upd f k v)"

lemma fold_pair_upd_triv: "A \<notin> fst ` set U \<Longrightarrow> foldl pair_fun_upd F U A = F A"
  by(induction U arbitrary: F; simp)
    (metis fun_upd_apply pair_fun_upd_def prod.simps(2) surjective_pairing)

lemma distinct_pair_update_one: "(k,v) \<in> set U \<Longrightarrow> distinct (map fst U) \<Longrightarrow> foldl pair_fun_upd F U k = v"
  by(induction U arbitrary: F; clarsimp simp add: pair_fun_upd_def fold_pair_upd_triv split: prod.splits) 
    (insert fold_pair_upd_triv, fastforce)
    
lemma distinct_zipunzip: "distinct xs \<Longrightarrow> distinct (map fst (zip xs ys))" by (simp add: distinct_conv_nth)
    
(* hm, this foldl pair_fun_upd business might have been a bad idea. *)
lemma foldl_pair_fun_upd_map_of: "distinct (map fst U) \<Longrightarrow> foldl pair_fun_upd F U = (\<lambda>k. case map_of U k of Some v \<Rightarrow> v | None \<Rightarrow> F k)"
  by(unfold fun_eq_iff; induction U arbitrary: F; clarsimp split: option.splits simp: pair_fun_upd_def rev_image_eqI)

lemma map_of_map_apsnd: "map_of (map (apsnd t) M) = map_option t \<circ> (map_of M)"
  by(unfold fun_eq_iff comp_def; induction M; simp)
    

definition biimp (infix "\<^bold>\<leftrightarrow>" 67) where "F \<^bold>\<leftrightarrow> G \<equiv> (F \<^bold>\<rightarrow> G) \<^bold>\<and> (G \<^bold>\<rightarrow> F)"
lemma atoms_biimp[simp]: "atoms (F \<^bold>\<leftrightarrow> G) = atoms F \<union> atoms G"
  unfolding biimp_def by auto
lemma biimp_size[simp]: "size (F \<^bold>\<leftrightarrow> G) = (2 * (size F + size G)) + 3"
  by(simp add: biimp_def)
  
locale freshstuff =
  fixes fresh :: "'a set \<Rightarrow> 'a"
  assumes isfresh: "finite S \<Longrightarrow> fresh S \<notin> S"
begin
  
primrec nfresh where
"nfresh S 0 = []" |
"nfresh S (Suc n) = (let f = fresh S in f # nfresh (f \<triangleright> S) n)"

lemma length_nfresh: "length (nfresh S n) = n"
  by(induction n arbitrary: S; simp add: Let_def)
    
lemma nfresh_isfresh: "finite S \<Longrightarrow> set (nfresh S n) \<inter> S = {}"
  by(induction n arbitrary: S; auto simp add: Let_def isfresh)
    
lemma nfresh_distinct: "finite S \<Longrightarrow> distinct (nfresh S n)"
  by(induction n arbitrary: S; simp add: Let_def; meson disjoint_iff_not_equal finite_insert insertI1 nfresh_isfresh)

definition "tseytin_assmt F \<equiv> let SF = remdups (subformulae F) in zip (nfresh (atoms F) (length SF)) SF"

lemma tseytin_assmt_distinct: "distinct (map fst (tseytin_assmt F))"
  unfolding tseytin_assmt_def using nfresh_distinct by (simp add: Let_def length_nfresh)
    
lemma tseytin_assmt_has: "G \<in> set (subformulae F) \<Longrightarrow> \<exists>n. (n,G) \<in> set (tseytin_assmt F)"
proof -
  assume "G \<in> set (subformulae F)"
  then have "\<exists>n. G = subformulae F ! n \<and> n < length (subformulae F)"
    by (simp add: set_conv_nth)
  then have "\<exists>a. (a, G) \<in> set (zip (nfresh (atoms F) (length (subformulae F))) (subformulae F))"
    by (metis (no_types) in_set_zip length_nfresh prod.sel(1) prod.sel(2))
  thus ?thesis by(simp add: tseytin_assmt_def Let_def) (metis fst_conv in_set_conv_nth in_set_zip length_nfresh set_remdups snd_conv)
qed

lemma tseytin_assmt_new_atoms: "(k,l) \<in> set (tseytin_assmt F) \<Longrightarrow> k \<notin> atoms F"
  unfolding tseytin_assmt_def Let_def using nfresh_isfresh by (fastforce dest: set_zip_leftD)

primrec tseytin_tran1 where
"tseytin_tran1 S (Atom k) = [Atom k \<^bold>\<leftrightarrow> S (Atom k)]" |
"tseytin_tran1 S \<bottom> = [\<bottom> \<^bold>\<leftrightarrow> S \<bottom>]" |
"tseytin_tran1 S (Not F) = [S (Not F) \<^bold>\<leftrightarrow> Not (S F)] @ tseytin_tran1 S F" |
"tseytin_tran1 S (And F G) = [S (And F G) \<^bold>\<leftrightarrow> And (S F) (S G)] @ tseytin_tran1 S F @ tseytin_tran1 S G" |
"tseytin_tran1 S (Or F G) = [S (Or F G) \<^bold>\<leftrightarrow> Or (S F) (S G)] @ tseytin_tran1 S F @ tseytin_tran1 S G" |
"tseytin_tran1 S (Imp F G) = [S (Imp F G) \<^bold>\<leftrightarrow> Imp (S F) (S G)] @ tseytin_tran1 S F @ tseytin_tran1 S G"
definition "tseytin_toatom F \<equiv> Atom \<circ> the \<circ> map_of (map (\<lambda>(a,b). (b,a)) (tseytin_assmt F))"
definition "tseytin_tran F \<equiv> \<^bold>\<And>(let S = tseytin_toatom F in S F # tseytin_tran1 S F)"
  
lemma distinct_snd_tseytin_assmt: "distinct (map snd (tseytin_assmt F))" 
  unfolding tseytin_assmt_def by(simp add: Let_def length_nfresh)

lemma tseytin_assmt_backlookup: assumes "J \<in> set (subformulae F)" 
  shows "(the (map_of (map (\<lambda>(a, b). (b, a)) (tseytin_assmt F)) J), J) \<in> set (tseytin_assmt F)"
proof -
  have 1: "distinct (map snd M) \<Longrightarrow> J \<in> snd ` set M \<Longrightarrow> (the (map_of (map (\<lambda>(a, b). (b, a)) M) J), J) \<in> set M" for J M
    by(induction M; clarsimp split: prod.splits)
  have 2: "J \<in> set (subformulae F) \<Longrightarrow> J \<in> snd ` set (tseytin_assmt F)" for J using image_iff tseytin_assmt_has by fastforce
  from 1[OF distinct_snd_tseytin_assmt 2, OF assms] show ?thesis .
qed

lemma tseytin_tran_small_clauses: "\<forall>C \<in> cnf (nnf (tseytin_tran F)). card C \<le> 3"
proof -
  have 3: "card S \<le> 2 \<Longrightarrow> card (a \<triangleright> S) \<le> 3" for a S 
    by(cases "finite S"; simp add: card_insert_le_m1)
  have 2: "card S \<le> 1 \<Longrightarrow> card (a \<triangleright> S) \<le> 2" for a S 
    by(cases "finite S"; simp add: card_insert_le_m1)
  have 1: "card S \<le> 0 \<Longrightarrow> card (a \<triangleright> S) \<le> 1" for a S 
    by(cases "finite S"; simp add: card_insert_le_m1)
  have *: "\<lbrakk>G \<in> set (tseytin_tran1 (Atom \<circ> S) F); C \<in> cnf (nnf G)\<rbrakk> \<Longrightarrow> card C \<le> 3" for G C S
    by(induction F arbitrary: G; simp add: biimp_def; (elim disjE exE conjE | intro 1 2 3 | simp)+)
  show ?thesis
    unfolding tseytin_tran_def  tseytin_toatom_def Let_def
    by(clarsimp simp add: cnf_BigAnd nnf_BigAnd comp_assoc *)
qed
  
lemma tseytin_tran_few_clauses: "card (cnf (nnf (tseytin_tran F))) \<le> 3 * size F + 1"
proof -
  have "size Bot = 1" by simp  (* just a thing to keep in mind. *)
  have ws: "{c \<triangleright> D |D. D = {c1} \<or> D = {c2}} = {{c,c1},{c,c2}}" for c1 c2 c by auto
  have grr: "Suc (card S) \<le> c \<Longrightarrow> card (a \<triangleright> S) \<le> c" for a S c
    by(cases "finite S"; simp add: card_insert_le_m1)
  have *: "card (\<Union>a\<in>set (tseytin_tran1 (Atom \<circ> S) F). cnf (nnf a)) \<le> 3 * size F" for S
    by(induction F; simp add: biimp_def; ((intro grr card_Un_le[THEN le_trans] | simp add: ws)+)?) 
  show ?thesis
    unfolding tseytin_tran_def tseytin_toatom_def Let_def
    by(clarsimp simp: nnf_BigAnd cnf_BigAnd; intro grr; simp add: comp_assoc *)
qed
  
lemma tseytin_tran_new_atom_count: "card (atoms (tseytin_tran F)) \<le> size F + card (atoms F)"
proof -
  have tseytin_tran1_atoms: "H \<in> set (tseytin_tran1 (tseytin_toatom F) G) \<Longrightarrow> G \<in> set (subformulae F) \<Longrightarrow>
    atoms H \<subseteq> atoms F \<union> (\<Union>I \<in> set (subformulae F). atoms (tseytin_toatom F I))" for G H
  proof(induction G arbitrary: H)
    case (Atom k)
    hence "k \<in> atoms F"
      by simp (meson formula.set_intros(1) rev_subsetD subformula_atoms)
    with Atom show ?case by simp blast
  next
    case Bot then show ?case by simp blast
  next
    case (Not G)
    show ?case by(insert Not.prems(1,2); 
         frule subformulas_in_subformulas; simp; elim disjE; (elim Not.IH | force))
  next
    case (And G1 G2)
    show ?case by(insert And.prems(1,2); 
         frule subformulas_in_subformulas; simp; elim disjE; (elim And.IH; simp | force))
  next
    case (Or G1 G2)
    show ?case by(insert Or.prems(1,2); 
         frule subformulas_in_subformulas; simp; elim disjE; (elim Or.IH; simp | force))
  next
    case (Imp G1 G2)
    show ?case by(insert Imp.prems(1,2); 
         frule subformulas_in_subformulas; simp; elim disjE; (elim Imp.IH; simp | force))
  qed
  have tseytin_tran1_atoms: "(\<Union>G\<in>set (tseytin_tran1 (tseytin_toatom F) F). atoms G) \<subseteq>
      atoms F \<union> (\<Union>I\<in>set (subformulae F). atoms (tseytin_toatom F I))"
    using tseytin_tran1_atoms[OF _ subformulae_self] by blast
  have 1: "card (atoms (tseytin_tran F)) \<le>
  card (atoms (tseytin_toatom F F) \<union> (\<Union>x\<in>set (tseytin_tran1 (tseytin_toatom F) F). atoms x))" 
    unfolding tseytin_tran_def by(simp add: Let_def tseytin_tran1_atoms)
  have 2: "atoms (tseytin_toatom F F) \<union> (\<Union>x\<in>set (tseytin_tran1 (tseytin_toatom F) F). atoms x) \<subseteq>
     (atoms F \<union> (\<Union>I\<in>set (subformulae F). atoms (tseytin_toatom F I)))"
    using tseytin_tran1_atoms by blast
  have twofin: "finite (atoms F \<union> (\<Union>I\<in>set (subformulae F). atoms (tseytin_toatom F I)))" by simp
  have card_subformulae: "card (set (subformulae F)) \<le> size F" using length_subformulae by (metis card_length)
  have card_singleton_union: "finite S \<Longrightarrow> card (\<Union>x\<in>S. {f x}) \<le> card S" for f S 
    by(induction S rule: finite_induct; simp add: card_insert_if)
  have 3: "card (\<Union>I\<in>set (subformulae F). atoms (tseytin_toatom F I)) \<le> size F"
    unfolding tseytin_toatom_def using le_trans[OF card_singleton_union card_subformulae]
    by simp fast
  have 4: "card (atoms (tseytin_tran F)) \<le> card (atoms F) + card (\<Union>f\<in>set (subformulae F). atoms (tseytin_toatom F f))"
    using le_trans[OF 1 card_mono[OF twofin 2]] card_Un_le le_trans by blast
  show ?thesis using 3 4 by linarith
qed
    
end

definition "freshnat S \<equiv>  Suc (Max (0 \<triangleright> S))"
primrec nfresh_natcode where
"nfresh_natcode S 0 = []" |
"nfresh_natcode S (Suc n) = (let f = freshnat S in f # nfresh_natcode (f \<triangleright> S) n)"
interpretation freshnats: freshstuff freshnat unfolding freshnat_def by standard (meson Max_ge Suc_n_not_le_n finite_insert insertCI)
(* interpreting the locale is easy. making it executable\<dots> not so. *)
lemma [code_unfold]: "freshnats.nfresh = nfresh_natcode"
proof -
  have "freshnats.nfresh S n  = nfresh_natcode S n" for S n by(induction n arbitrary: S; simp)
  thus ?thesis by auto
qed
lemmas freshnats_code[code_unfold] = freshnats.tseytin_tran_def freshnats.tseytin_toatom_def freshnats.tseytin_assmt_def freshnats.nfresh.simps
  
lemma "freshnats.tseytin_tran (Atom 0 \<^bold>\<rightarrow> (\<^bold>\<not> (Atom 1))) = \<^bold>\<And>[
  Atom 2,
  Atom 2 \<^bold>\<leftrightarrow> Atom 3 \<^bold>\<rightarrow> Atom 4,
  Atom 0 \<^bold>\<leftrightarrow> Atom 3,
  Atom 4 \<^bold>\<leftrightarrow> \<^bold>\<not> (Atom 5),
  Atom 1 \<^bold>\<leftrightarrow> Atom 5
]" (is "?l = ?r")
proof -
  have "cnf (nnf ?r) =
    {{Pos 2},
     {Neg 4, Pos 2}, {Pos 3, Pos 2}, {Neg 2, Neg 3, Pos 4},
     {Neg 3, Pos 0}, {Neg 0, Pos 3},
     {Pos 5, Pos 4}, {Neg 4, Neg 5},
     {Neg 5, Pos 1}, {Neg 1, Pos 5}}" by eval
  have ?thesis by eval
  show ?thesis by code_simp
qed
    
end
