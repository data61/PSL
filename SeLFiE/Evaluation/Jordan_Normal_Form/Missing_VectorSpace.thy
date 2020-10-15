(*
    Author:      René Thiemann
                 Akihisa Yamada
                 Jose Divasón
    License:     BSD
*)
(* with contributions from Alexander Bentkamp, Universität des Saarlandes *)

section \<open>Missing Vector Spaces\<close>

text \<open>This theory provides some lemmas which we required when working with vector spaces.\<close>

theory Missing_VectorSpace
imports
  VectorSpace.VectorSpace
  Missing_Ring
  "HOL-Library.Multiset"
begin


(**** The following lemmas that could be moved to HOL/Finite_Set.thy  ****)

(*This a generalization of comp_fun_commute. It is a similar definition, but restricted to a set. 
  When "A = UNIV::'a set", we have "comp_fun_commute_on f A = comp_fun_commute f"*)
locale comp_fun_commute_on = 
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and A::"'a set"
  assumes comp_fun_commute_restrict: "\<forall>y\<in>A. \<forall>x\<in>A. \<forall>z\<in>A. f y (f x z) = f x (f y z)"
  and f: "f : A \<rightarrow> A \<rightarrow> A" 
begin

lemma comp_fun_commute_on_UNIV:
  assumes "A = (UNIV :: 'a set)"
  shows "comp_fun_commute f"
  unfolding comp_fun_commute_def 
  using assms comp_fun_commute_restrict f by auto

lemma fun_left_comm: 
  assumes "y \<in> A" and "x \<in> A" and "z \<in> A" shows "f y (f x z) = f x (f y z)"
  using comp_fun_commute_restrict assms by auto

lemma commute_left_comp: 
  assumes "y \<in> A" and "x\<in>A" and "z\<in>A" and "g \<in> A \<rightarrow> A" 
  shows "f y (f x (g z)) = f x (f y (g z))"
  using assms by (auto simp add: Pi_def o_assoc comp_fun_commute_restrict)

lemma fold_graph_finite:
  assumes "fold_graph f z B y"
  shows "finite B"
  using assms by induct simp_all

lemma fold_graph_closed:
  assumes "fold_graph f z B y" and "B \<subseteq> A" and "z \<in> A"
  shows "y \<in> A"
  using assms 
proof (induct set: fold_graph)
  case emptyI
  then show ?case by auto
next
  case (insertI x B y)
  then show ?case using insertI f by auto
qed

lemma fold_graph_insertE_aux:
  "fold_graph f z B y \<Longrightarrow> a \<in> B \<Longrightarrow> z\<in>A
  \<Longrightarrow> B \<subseteq> A
  \<Longrightarrow>  \<exists>y'. y = f a y' \<and> fold_graph f z (B - {a}) y' \<and> y' \<in> A"
proof (induct set: fold_graph)
  case emptyI
  then show ?case by auto
next
  case (insertI x B y)
  show ?case
  proof (cases "x = a")
    case True 
    show ?thesis
    proof (rule exI[of _ y])
      have B: "(insert x B - {a}) = B" using True insertI by auto 
      have "f x y = f a y" by (simp add: True) 
      moreover have "fold_graph f z (insert x B - {a}) y" by (simp add: B insertI)
      moreover have "y \<in> A" using insertI fold_graph_closed[of z B] by auto
      ultimately show " f x y = f a y \<and> fold_graph f z (insert x B - {a}) y \<and> y \<in> A" by simp
    qed
  next
    case False
    then obtain y' where y: "y = f a y'" and y': "fold_graph f z (B - {a}) y'" and y'_in_A: "y' \<in> A"
      using insertI f by auto
    have "f x y = f a (f x y')"
      unfolding y 
    proof (rule fun_left_comm)
      show "x \<in> A" using insertI by auto
      show "a \<in> A" using insertI by auto
      show "y' \<in> A" using y'_in_A by auto
    qed  
    moreover have "fold_graph f z (insert x B - {a}) (f x y')"
      using y' and \<open>x \<noteq> a\<close> and \<open>x \<notin> B\<close>
      by (simp add: insert_Diff_if fold_graph.insertI)    
    moreover have "(f x y') \<in> A" using insertI f y'_in_A by auto
    ultimately show ?thesis using y'_in_A
      by auto
  qed
qed
    
lemma fold_graph_insertE:
  assumes "fold_graph f z (insert x B) v" and "x \<notin> B" and "insert x B \<subseteq> A" and "z\<in>A"
  obtains y where "v = f x y" and "fold_graph f z B y"
  using assms by (auto dest: fold_graph_insertE_aux [OF _ insertI1])

lemma fold_graph_determ: "fold_graph f z B x \<Longrightarrow> fold_graph f z B y \<Longrightarrow>  B \<subseteq> A \<Longrightarrow> z\<in>A \<Longrightarrow> y = x"
proof (induct arbitrary: y set: fold_graph)
  case emptyI
  then show ?case
    by (meson empty_fold_graphE)
next
  case (insertI x B y v)
  from \<open>fold_graph f z (insert x B) v\<close> and \<open>x \<notin> B\<close> and \<open>insert x B \<subseteq> A\<close> and  \<open>z \<in> A\<close>
  obtain y' where "v = f x y'" and "fold_graph f z B y'"
    by (rule fold_graph_insertE)
  from \<open>fold_graph f z B y'\<close> and \<open>insert x B \<subseteq> A\<close> have "y' = y" using insertI by auto    
  with \<open>v = f x y'\<close> show "v = f x y"
    by simp
qed

lemma fold_equality: "fold_graph f z B y \<Longrightarrow> B \<subseteq> A \<Longrightarrow> z \<in> A \<Longrightarrow> Finite_Set.fold f z B = y"
  by (cases "finite B") 
  (auto simp add: Finite_Set.fold_def intro: fold_graph_determ dest: fold_graph_finite)
    
lemma fold_graph_fold:
  assumes f: "finite B" and BA: "B\<subseteq>A" and z: "z \<in> A"
  shows "fold_graph f z B (Finite_Set.fold f z B)"
proof -
   have "\<exists>x. fold_graph f z B x"
    by (rule finite_imp_fold_graph[OF f])
  moreover note fold_graph_determ
  ultimately have "\<exists>!x. fold_graph f z B x" using f BA z by auto    
  then have "fold_graph f z B (The (fold_graph f z B))"
    by (rule theI')
  with assms show ?thesis
    by (simp add: Finite_Set.fold_def)
qed
  
(*This lemma is a generalization of thm comp_fun_commute.fold_insert*)
lemma fold_insert [simp]:
  assumes "finite B" and "x \<notin> B" and BA: "insert x B \<subseteq> A" and z: "z \<in> A"
  shows "Finite_Set.fold f z (insert x B) = f x (Finite_Set.fold f z B)"
  proof (rule fold_equality[OF _ BA z])
  from \<open>finite B\<close> have "fold_graph f z B (Finite_Set.fold f z B)"
   using BA fold_graph_fold z by auto
  hence "fold_graph f z (insert x B) (f x (Finite_Set.fold f z B))"
    using BA  fold_graph.insertI assms by auto
  then show "fold_graph f z (insert x B) (f x (Finite_Set.fold f z B))"
    by simp
qed
end

(*This lemma is a generalization of thm Finite_Set.fold_cong *)
lemma fold_cong:
  assumes f: "comp_fun_commute_on f A" and g: "comp_fun_commute_on g A"
    and "finite S"
    and cong: "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
    and "s = t" and "S = T" 
    and SA: "S \<subseteq> A" and s: "s\<in>A"
  shows "Finite_Set.fold f s S = Finite_Set.fold g t T"
proof -
  have "Finite_Set.fold f s S = Finite_Set.fold g s S"
    using \<open>finite S\<close> cong SA s
  proof (induct S)
    case empty
    then show ?case by simp
  next
    case (insert x F)
    interpret f: comp_fun_commute_on f A by (fact f)
    interpret g: comp_fun_commute_on g A by (fact g)
    show ?case  using insert by auto
  qed
  with assms show ?thesis by simp
qed
                    
context comp_fun_commute_on
begin  

lemma comp_fun_Pi: "(\<lambda>x. f x ^^ g x) \<in> A \<rightarrow> A \<rightarrow> A"
proof -    
  have "(f x ^^ g x) y \<in> A" if y: "y \<in> A" and x: "x \<in> A" for x y
    using x y
   proof (induct "g x" arbitrary: g)
     case 0
     then show ?case by auto
   next
     case (Suc n g)
     define h where "h z = g z - 1" for z
     have hyp: "(f x ^^ h x) y \<in> A" 
       using h_def Suc.prems Suc.hyps diff_Suc_1 by metis
     have "g x = Suc (h x)" unfolding h_def
       using Suc.hyps(2) by auto     
     then show ?case using f x hyp unfolding Pi_def by auto
   qed 
  thus ?thesis by (auto simp add: Pi_def)
qed

(*This lemma is a generalization of thm comp_fun_commute.comp_fun_commute_funpow *)
lemma comp_fun_commute_funpow: "comp_fun_commute_on (\<lambda>x. f x ^^ g x) A"
proof -
  have f: " (f y ^^ g y) ((f x ^^ g x) z) = (f x ^^ g x) ((f y ^^ g y) z)"
    if x: "x\<in>A" and y: "y \<in> A" and z: "z \<in> A" for x y z
  proof (cases "x = y")
    case False
    show ?thesis
    proof (induct "g x" arbitrary: g)
      case (Suc n g)
      have hyp1: "(f y ^^ g y) (f x k) = f x ((f y ^^ g y) k)" if k: "k \<in> A" for k
      proof (induct "g y" arbitrary: g)
        case 0
        then show ?case by simp
      next
        case (Suc n g)       
        define h where "h z = g z - 1" for z
        with Suc have "n = h y"
          by simp
        with Suc have hyp: "(f y ^^ h y) (f x k) = f x ((f y ^^ h y) k)"
          by auto
        from Suc h_def have g: "g y = Suc (h y)"
          by simp
        have "((f y ^^ h y) k) \<in> A" using y k comp_fun_Pi[of h] unfolding Pi_def by auto
        then show ?case
          by (simp add: comp_assoc g hyp) (auto simp add: o_assoc comp_fun_commute_restrict x y k)
      qed
      define h where "h a = (if a = x then g x - 1 else g a)" for a
      with Suc have "n = h x"
        by simp
      with Suc have "(f y ^^ h y) ((f x ^^ h x) z) = (f x ^^ h x) ((f y ^^ h y) z)"
        by auto
      with False have Suc2: "(f x ^^ h x) ((f y ^^ g y) z) = (f y ^^ g y) ((f x ^^ h x) z)"
        using h_def by auto      
      from Suc h_def have g: "g x = Suc (h x)"
        by simp
      have "(f x ^^ h x) z \<in>A" using comp_fun_Pi[of h] x z unfolding Pi_def by auto
      hence *: "(f y ^^ g y) (f x ((f x ^^ h x) z)) = f x ((f y ^^ g y) ((f x ^^ h x) z))" 
        using hyp1 by auto
      thus ?case using g Suc2 by auto
    qed simp
  qed simp
  thus ?thesis by (auto simp add: comp_fun_commute_on_def comp_fun_Pi o_def)
qed

(*This lemma is a generalization of thm comp_fun_commute.fold_mset_add_mset*)
lemma fold_mset_add_mset: 
  assumes MA: "set_mset M \<subseteq> A" and s: "s \<in> A" and x: "x \<in> A"
  shows "fold_mset f s (add_mset x M) = f x (fold_mset f s M)"
proof -
  interpret mset: comp_fun_commute_on "\<lambda>y. f y ^^ count M y" A
    by (fact comp_fun_commute_funpow)
  interpret mset_union: comp_fun_commute_on "\<lambda>y. f y ^^ count (add_mset x M) y" A
    by (fact comp_fun_commute_funpow)
  show ?thesis
  proof (cases "x \<in> set_mset M")
    case False
    then have *: "count (add_mset x M) x = 1"
      by (simp add: not_in_iff)
     have "Finite_Set.fold (\<lambda>y. f y ^^ count (add_mset x M) y) s (set_mset M) =
      Finite_Set.fold (\<lambda>y. f y ^^ count M y) s (set_mset M)"
       by (rule fold_cong[of _ A], auto simp add: assms False comp_fun_commute_funpow)
    with False * s MA x show ?thesis
      by (simp add: fold_mset_def del: count_add_mset)
  next
    case True
    let ?f = "(\<lambda>xa. f xa ^^ count (add_mset x M) xa)"
    let ?f2 = "(\<lambda>x. f x ^^ count M x)"
    define N where "N = set_mset M - {x}"
    have F: "Finite_Set.fold ?f s (insert x N) = ?f x (Finite_Set.fold ?f s N)" 
      by (rule mset_union.fold_insert, auto simp add: assms N_def)
    have F2: "Finite_Set.fold ?f2 s (insert x N) = ?f2 x (Finite_Set.fold ?f2 s N)"
      by (rule mset.fold_insert, auto simp add: assms N_def)
    from N_def True have *: "set_mset M = insert x N" "x \<notin> N" "finite N" by auto
    then have "Finite_Set.fold (\<lambda>y. f y ^^ count (add_mset x M) y) s N =
      Finite_Set.fold (\<lambda>y. f y ^^ count M y) s N" 
      using MA N_def s 
      by (auto intro!: fold_cong comp_fun_commute_funpow)
    with * show ?thesis by (simp add: fold_mset_def del: count_add_mset, unfold F F2, auto)      
  qed
qed
end

(**** End of the lemmas that could be moved to HOL/Finite_Set.thy  ****)


lemma Diff_not_in: "a \<notin> A - {a}" by auto

context abelian_group begin

lemma finsum_restrict:
  assumes fA: "f : A \<rightarrow> carrier G"
      and restr: "restrict f A = restrict g A"
  shows "finsum G f A = finsum G g A"
proof (rule finsum_cong';rule?)
  fix a assume a: "a : A"
  have "f a = restrict f A a" using a by simp
  also have "... = restrict g A a" using restr by simp
  also have "... = g a" using a by simp
  finally show "f a = g a".
  thus "g a : carrier G" using fA a by force
qed

lemma minus_nonzero: "x : carrier G \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> \<ominus> x \<noteq> \<zero>"
  using r_neg by force

end

lemma (in ordered_comm_monoid_add) positive_sum:
  assumes X : "finite X"
      and "f : X \<rightarrow> { y :: 'a. y \<ge> 0 }"
  shows "sum f X \<ge> 0 \<and> (sum f X = 0 \<longrightarrow> f ` X \<subseteq> {0})"
  using assms
proof (induct set:finite)
  case (insert x X)
    hence x0: "f x \<ge> 0" and sum0: "sum f X \<ge> 0" by auto
    hence "sum f (insert x X) \<ge> 0" using insert by auto
    moreover
    { assume "sum f (insert x X) = 0"
      hence "f x = 0" "sum f X = 0"
        using sum0 x0 insert add_nonneg_eq_0_iff by auto
    }
    ultimately show ?case using insert by blast
qed auto


lemma insert_union: "insert x X = X \<union> {x}" by auto


context vectorspace begin

lemmas lincomb_insert2 = lincomb_insert[unfolded insert_union[symmetric]]

lemma lincomb_restrict:
  assumes U: "U \<subseteq> carrier V"
      and a: "a : U \<rightarrow> carrier K"
      and restr: "restrict a U = restrict b U"
  shows "lincomb a U = lincomb b U"
proof -
  let ?f = "\<lambda>a u. a u \<odot>\<^bsub>V\<^esub> u"
  have fa: "?f a : U \<rightarrow> carrier V" using a U by auto
  have "restrict (?f a) U = restrict (?f b) U"
  proof
    fix u
    have "u : U \<Longrightarrow> a u = b u" using restr unfolding restrict_def by metis
    thus "restrict (?f a) U u = restrict (?f b) U u" by auto
  qed
  thus ?thesis
    unfolding lincomb_def using finsum_restrict[OF fa] by auto
qed

lemma lindep_span:
  assumes U: "U \<subseteq> carrier V" and finU: "finite U"
  shows "lin_dep U = (\<exists>u \<in> U. u \<in> span (U - {u}))" (is "?l = ?r")
proof
  assume l: "?l" show "?r"
  proof -
    from l[unfolded lin_dep_def]
    obtain A a u
    where finA: "finite A"
      and AU: "A \<subseteq> U"
      and aA: "a : A \<rightarrow> carrier K"
      and aA0: "lincomb a A = zero V"
      and uA: "u:A"
      and au0: "a u \<noteq> zero K" by auto
    define a' where "a' = (\<lambda>v. (if v : A then a v else zero K))"
    have a'U: "a' : U \<rightarrow> carrier K" unfolding a'_def using aA by auto
    have uU: "u : U" using uA AU by auto
    have a'u0: "a' u \<noteq> zero K" unfolding a'_def using au0 uA by auto
    define B where "B = U - A"
    have B: "B \<subseteq> carrier V" unfolding B_def using U by auto
    have UAB: "U = A \<union> B" unfolding B_def using AU by auto
    have finB: "finite B" using finU B_def by auto
    have AB: "A \<inter> B = {}" unfolding B_def by auto
    let ?f = "\<lambda>v. a v \<odot>\<^bsub>V\<^esub> v"
    have fA: "?f : A \<rightarrow> carrier V" unfolding a'_def using aA AU U by auto
    let ?f' = "\<lambda>v. a' v \<odot>\<^bsub>V\<^esub> v"
    have "restrict ?f A = restrict ?f' A" unfolding a'_def by auto
    hence finsum: "finsum V ?f' A = finsum V ?f A"
      using finsum_restrict[OF fA] by simp
    have f'A: "?f' : A \<rightarrow> carrier V"
    proof
      fix x assume xA: "x \<in> A"
      show "?f' x : carrier V" unfolding a'_def using aA xA AU U by auto
    qed
    have f'B: "?f' : B \<rightarrow> carrier V"
    proof
      fix x assume xB: "x : B"
      have "x \<notin> A" using a'U xB unfolding B_def by auto
      thus "?f' x : carrier V"using xB B unfolding a'_def by auto
    qed
    have sumB0: "finsum V ?f' B = zero V"
    proof -
      { fix B'
        have "finite B' \<Longrightarrow> B' \<subseteq> B \<Longrightarrow> finsum V ?f' B' = zero V"
        proof(induct set:finite)
          case (insert b B')
            have finB': "finite B'" and bB': "b \<notin> B'" using insert by auto
            have f'B': "?f' : B' \<rightarrow> carrier V" using f'B insert by auto
            have bA: "b \<notin> A" using insert unfolding B_def by auto
            have b: "b : carrier V" using insert B by auto
            have foo: "a' b \<odot>\<^bsub>V\<^esub> b \<in> carrier V" unfolding a'_def using bA b by auto
            have IH: "finsum V ?f' B' = zero V" using insert by auto
            show ?case
              unfolding finsum_insert[OF finB' bB' f'B' foo]
              using IH a'_def bA b by auto
         qed auto
      }
      thus ?thesis using finB by auto
    qed
    have a'A0: "lincomb a' U = zero V"
      unfolding UAB
      unfolding lincomb_def
      unfolding finsum_Un_disjoint[OF finA finB AB f'A f'B]
      unfolding finsum
      unfolding aA0[unfolded lincomb_def]
      unfolding sumB0 by simp
    have uU: "u:U" using uA AU by auto
    moreover have "u : span (U - {u})"
      using lincomb_isolate(2)[OF finU U a'U uU a'u0 a'A0].
    ultimately show ?r by auto
  qed
  next assume r: "?r" show "?l"
  proof -
    from r obtain u where uU: "u : U" and uspan: "u : span (U-{u})" by auto
    hence u: "u : carrier V" using U by auto
    have finUu: "finite (U-{u})" using finU by auto
    have Uu: "U-{u} \<subseteq> carrier V" using U by auto
    obtain a
      where ulin: "u = lincomb a (U-{u})"
        and a: "a : U-{u} \<rightarrow> carrier K"
      using uspan unfolding finite_span[OF finUu Uu] by auto
    show "?l" unfolding lin_dep_def
    proof(intro exI conjI)
      let ?a = "\<lambda>v. if v = u then \<ominus>\<^bsub>K\<^esub> one K else a v"
      show "?a : U \<rightarrow> carrier K" using a by auto
      hence a': "?a : U-{u}\<union>{u} \<rightarrow> carrier K" by auto
      have "U = U-{u}\<union>{u}" using uU by auto
      also have "lincomb ?a ... = ?a u \<odot>\<^bsub>V\<^esub> u \<oplus>\<^bsub>V\<^esub> lincomb ?a (U-{u})"
        unfolding lincomb_insert[OF finUu Uu a' Diff_not_in u] by auto
      also have "restrict a (U-{u}) = restrict ?a (U-{u})" by auto
        hence "lincomb ?a (U-{u}) = lincomb a (U-{u})"
          using lincomb_restrict[OF Uu a] by auto
      also have "?a u \<odot>\<^bsub>V\<^esub> u = \<ominus>\<^bsub>V\<^esub> u" using smult_minus_1[OF u] by simp
      also have "lincomb a (U-{u}) = u" using ulin..
      also have "\<ominus>\<^bsub>V\<^esub> u \<oplus>\<^bsub>V\<^esub> u = zero V" using l_neg[OF u].
      finally show "lincomb ?a U = zero V" by auto
    qed (insert uU finU, auto)
  qed
qed

lemma not_lindepD:
  assumes "~ lin_dep S"
      and "finite A" "A \<subseteq> S" "f : A \<rightarrow> carrier K" "lincomb f A = zero V"
    shows "f : A \<rightarrow> {zero K}"
  using assms unfolding lin_dep_def by blast


lemma span_mem:
  assumes E: "E \<subseteq> carrier V" and uE: "u : E" shows "u : span E"
  unfolding span_def
proof (rule,intro exI conjI)
  show "u = lincomb (\<lambda>_. one K) {u}" unfolding lincomb_def using uE E by auto
  show "{u} \<subseteq> E" using uE by auto
qed auto

lemma lincomb_distrib:
  assumes U: "U \<subseteq> carrier V"
      and a: "a : U \<rightarrow> carrier K"
      and c: "c : carrier K"
  shows "c \<odot>\<^bsub>V\<^esub> lincomb a U = lincomb (\<lambda>u. c \<otimes>\<^bsub>K\<^esub> a u) U"
    (is "_ = lincomb ?b U")
  using U a
proof (induct U rule: infinite_finite_induct)
  case empty show ?case unfolding lincomb_def using c by simp next
  case (insert u U)
    then have U: "U \<subseteq> carrier V"
          and u: "u : carrier V"
          and a: "a : insert u U \<rightarrow> carrier K"
          and finU: "finite U" by auto
    hence aU: "a : U \<rightarrow> carrier K" by auto
    have b: "?b : insert u U \<rightarrow> carrier K" using a c by auto
    show ?case
      unfolding lincomb_insert2[OF finU U a \<open>u\<notin>U\<close> u]
      unfolding lincomb_insert2[OF finU U b \<open>u\<notin>U\<close> u]
      using insert U aU c u smult_r_distr smult_assoc1 by auto next
  case (infinite U)
    thus ?case unfolding lincomb_def using assms by simp
qed

lemma span_swap:
  assumes finE[simp]: "finite E"
      and E[simp]: "E \<subseteq> carrier V"
      and u[simp]: "u : carrier V"
      and usE: "u \<notin> span E"
      and v[simp]: "v : carrier V"
      and usEv: "u : span (insert v E)"
  shows "span (insert u E) \<subseteq> span (insert v E)" (is "?L \<subseteq> ?R")
proof -
  have Eu[simp]: "insert u E \<subseteq> carrier V" by auto
  have Ev[simp]: "insert v E \<subseteq> carrier V" by auto
  have finEu: "finite (insert u E)" and finEv: "finite (insert v E)"
    using finE by auto
  have uE: "u \<notin> E" using usE span_mem by force
  have vE: "v \<notin> E"
  proof
    assume "v : E"
    hence EvE: "insert v E = E" using insert_absorb by auto
    hence "u : span E" using usEv by auto
    thus "False" using usE by auto
  qed
  obtain ua
    where ua[simp]: "ua : (insert v E) \<rightarrow> carrier K"
      and uua: "u = lincomb ua (insert v E)"
    using usEv finite_span[OF finEv Ev]  by auto
  hence uaE[simp]: "ua : E \<rightarrow> carrier K" and [simp]: "ua v : carrier K"
    by auto

  show "?L \<subseteq> ?R"
  proof
    fix x assume "x : ?L"
    then obtain xa
    where xa: "xa : insert u E \<rightarrow> carrier K"
      and xxa: "x = lincomb xa (insert u E)"
      unfolding finite_span[OF finEu Eu] by auto
    hence xaE[simp]: "xa : E \<rightarrow> carrier K" and xau[simp]: "xa u : carrier K" by auto
    show "x : span (insert v E)"
      unfolding finite_span[OF finEv Ev]
    proof (rule,intro exI conjI)
      define a where "a = (\<lambda>e. xa u \<otimes>\<^bsub>K\<^esub> ua e)"
      define a' where "a' = (\<lambda>e. a e \<oplus>\<^bsub>K\<^esub> xa e)"
      define a'' where "a'' = (\<lambda>e. if e = v then xa u \<otimes>\<^bsub>K\<^esub> ua v else a' e)"
      have aE: "a : E \<rightarrow> carrier K" unfolding a_def using xau uaE u by blast
      hence a'E: "a' : E \<rightarrow> carrier K" unfolding a'_def using xaE by blast
      thus a'': "a'' : insert v E \<rightarrow> carrier K" unfolding a''_def by auto
      have restr: "restrict a' E = restrict a'' E"
        unfolding a''_def using vE by auto
      have "x = xa u \<odot>\<^bsub>V\<^esub> u \<oplus>\<^bsub>V\<^esub> lincomb xa E"
        using xxa lincomb_insert2 finE E xa uE u by auto
      also have
        "xa u \<odot>\<^bsub>V\<^esub> u = xa u \<odot>\<^bsub>V\<^esub> lincomb ua (insert v E)"
        using uua by auto
      also have "lincomb ua (insert v E) = ua v \<odot>\<^bsub>V\<^esub> v \<oplus>\<^bsub>V\<^esub> lincomb ua E"
        using lincomb_insert2 finE E ua vE v by auto
      also have "xa u \<odot>\<^bsub>V\<^esub> ... = xa u \<odot>\<^bsub>V\<^esub> (ua v \<odot>\<^bsub>V\<^esub> v) \<oplus>\<^bsub>V\<^esub> xa u \<odot>\<^bsub>V\<^esub> lincomb ua E"
        using smult_r_distr by auto
      also have "xa u \<odot>\<^bsub>V\<^esub> lincomb ua E = lincomb a E"
        unfolding a_def using lincomb_distrib[OF E] by auto
      finally have "x = xa u \<odot>\<^bsub>V\<^esub> (ua v \<odot>\<^bsub>V\<^esub> v) \<oplus>\<^bsub>V\<^esub> (lincomb a E \<oplus>\<^bsub>V\<^esub> lincomb xa E)"
        using a_assoc xau v aE xaE by auto
      also have "lincomb a E \<oplus>\<^bsub>V\<^esub> lincomb xa E = lincomb a' E"
        unfolding a'_def using lincomb_sum[OF finE E aE xaE]..
      also have "... = lincomb a'' E"
        using lincomb_restrict[OF E a'E ] restr by auto
      finally have "x = ((xa u \<otimes>\<^bsub>K\<^esub> ua v) \<odot>\<^bsub>V\<^esub> v) \<oplus>\<^bsub>V\<^esub> lincomb a'' E"
        using smult_assoc1 by auto
      also have "xa u \<otimes>\<^bsub>K\<^esub> ua v = a'' v" unfolding a''_def by simp
      also have "(a'' v \<odot>\<^bsub>V\<^esub> v) \<oplus>\<^bsub>V\<^esub> lincomb a'' E = lincomb a'' (insert v E)"
        using lincomb_insert2[OF finE E a'' vE] by auto
      finally show "x = lincomb a'' (insert v E)".
    qed
  qed
qed

lemma basis_swap:
  assumes finE[simp]: "finite E"
      and u[simp]: "u : carrier V"
      and uE[simp]: "u \<notin> E"
      and b: "basis (insert u E)"
      and v[simp]: "v : carrier V"
      and uEv: "u : span (insert v E)"
  shows "basis (insert v E)"
  unfolding basis_def
proof (intro conjI)
  have Eu[simp]: "insert u E \<subseteq> carrier V"
   and spanEu: "carrier V = span (insert u E)"
   and indEu: "~ lin_dep (insert u E)"
    using b[unfolded basis_def] by auto
  hence E[simp]: "E \<subseteq> carrier V" by auto
  thus Ev[simp]: "insert v E \<subseteq> carrier V" using v by auto
  have finEu: "finite (insert u E)"
   and finEv: "finite (insert v E)" using finE by auto
  have usE: "u \<notin> span E"
  proof
    assume "u : span E"
    hence "u : span (insert u E - {u})" using uE by auto
    moreover have "u : insert u E" by auto
    ultimately have "lin_dep (insert u E)"
      unfolding lindep_span[OF Eu finEu] by auto
    thus "False" using b unfolding basis_def by auto
  qed

  obtain ua
    where ua[simp]: "ua : insert v E \<rightarrow> carrier K"
      and uua: "u = lincomb ua (insert v E)"
    using uEv finite_span[OF finEv Ev]  by auto
  hence uaE[simp]: "ua : E \<rightarrow> carrier K"
    and uav[simp]: "ua v : carrier K"
    by auto

  have vE: "v \<notin> E"
  proof
    assume "v : E"
    hence EvE: "insert v E = E" using insert_absorb by auto
    hence "u : span E" using uEv by auto
    thus "False" using usE by auto
  qed
  have vsE: "v \<notin> span E"
  proof
    assume "v : span E"
    then obtain va
      where va[simp]: "va : E \<rightarrow> carrier K"
        and vva: "v = lincomb va E"
      using finite_span[OF finE E] by auto
    define va' where "va' = (\<lambda>e. ua v \<otimes>\<^bsub>K\<^esub> va e)"
    define va'' where "va'' = (\<lambda>e. va' e \<oplus>\<^bsub>K\<^esub> ua e)"
    have va'[simp]: "va' : E \<rightarrow> carrier K"
      unfolding va'_def using uav va by blast
    hence va''[simp]: "va'' : E \<rightarrow> carrier K"
      unfolding va''_def using ua by blast
    from uua
    have "u = ua v \<odot>\<^bsub>V\<^esub> v \<oplus>\<^bsub>V\<^esub> lincomb ua E"
      using lincomb_insert2 vE by auto
    also have "ua v \<odot>\<^bsub>V\<^esub> v = ua v \<odot>\<^bsub>V\<^esub> (lincomb va E)"
      using vva by auto
    also have "... = lincomb va' E"
      unfolding va'_def using lincomb_distrib by auto
    finally have "u = lincomb va'' E"
      unfolding va''_def
      using lincomb_sum[OF finE E] by auto
    hence "u : span E" using finite_span[OF finE E] va'' by blast
    hence "lin_dep (insert u E)" using lindep_span by simp
    then show False using indEu by auto
  qed

  have indE: "~ lin_dep E" using indEu subset_li_is_li by auto

  show "~ lin_dep (insert v E)" using lin_dep_iff_in_span[OF E indE v vE] vsE by auto

  show "span (insert v E) = carrier V" (is "?L = ?R")
  proof (rule)
    show "?L \<subseteq> ?R"
    proof
      have finEv: "finite (insert v E)" using finE by auto
      fix x assume "x : ?L"
      then obtain a
        where a: "a : insert v E \<rightarrow> carrier K"
          and x: "x = lincomb a (insert v E)"
        unfolding finite_span[OF finEv Ev] by auto
      from a have av: "a v : carrier K" by auto
      from a have a2: "a : E \<rightarrow> carrier K" by auto
      show "x : ?R"
        unfolding x
        unfolding lincomb_insert2[OF finE E a vE v]
        using lincomb_closed[OF E a2] av v
        by auto
    qed
    show "?R \<subseteq> ?L"
      using span_swap[OF finE E u usE v uEv] spanEu by auto
  qed
qed

lemma span_empty: "span {} = {zero V}"
  unfolding finite_span[OF finite.emptyI empty_subsetI]
  unfolding lincomb_def by simp

lemma span_self: assumes [simp]: "v : carrier V" shows "v : span {v}"
proof -
  have "v = lincomb (\<lambda>x. one K) {v}" unfolding lincomb_def by auto
  thus ?thesis using finite_span by auto
qed

lemma span_zero: "zero V : span U" unfolding span_def lincomb_def by force

definition emb where "emb f D x = (if x : D then f x else zero K)"

lemma emb_carrier[simp]: "f : D \<rightarrow> R \<Longrightarrow> emb f D : D \<rightarrow> R"
  apply rule unfolding emb_def by auto

lemma emb_restrict: "restrict (emb f D) D = restrict f D"
  apply rule unfolding restrict_def emb_def by auto

lemma emb_zero: "emb f D : X - D \<rightarrow> { zero K }"
  apply rule unfolding emb_def by auto

lemma lincomb_clean:
  assumes A: "A \<subseteq> carrier V"
    and Z: "Z \<subseteq> carrier V"
    and finA: "finite A"
    and finZ: "finite Z"
    and aA: "a : A \<rightarrow> carrier K"
    and aZ: "a : Z \<rightarrow> { zero K }"
  shows "lincomb a (A \<union> Z) = lincomb a A"
  using finZ Z aZ
proof(induct set:finite)
  case empty thus ?case by simp next
  case (insert z Z) show ?case
    proof (cases "z : A")
      case True hence "A \<union> insert z Z = A \<union> Z" by auto
        thus ?thesis using insert by simp next
      case False
        have finAZ: "finite (A \<union> Z)" using finA insert by simp
        have AZ: "A \<union> Z \<subseteq> carrier V" using A insert by simp
        have a: "a : insert z (A \<union> Z) \<rightarrow> carrier K" using insert aA by force
        have "a z = zero K" using insert by auto
        also have "... \<odot>\<^bsub>V\<^esub> z = zero V" using insert by auto
        also have "... \<oplus>\<^bsub>V\<^esub> lincomb a (A \<union> Z) = lincomb a (A \<union> Z)"
          using insert AZ aA by auto
        also have "... = lincomb a A" using insert by simp
        finally have "a z \<odot>\<^bsub>V\<^esub> z \<oplus>\<^bsub>V\<^esub> lincomb a (A \<union> Z) = lincomb a A".
        thus ?thesis
          using lincomb_insert2[OF finAZ AZ a] False insert by auto
    qed
qed

lemma span_add1:
  assumes U: "U \<subseteq> carrier V" and v: "v : span U" and w: "w : span U"
  shows "v \<oplus>\<^bsub>V\<^esub> w : span U"
proof -
  from v obtain a A
    where finA: "finite A"
      and va: "lincomb a A = v"
      and AU: "A \<subseteq> U"
      and a: "a : A \<rightarrow> carrier K"
    unfolding span_def by auto
  hence A: "A \<subseteq> carrier V" using U by auto
  from w obtain b B
    where finB: "finite B"
      and wb: "lincomb b B = w"
      and BU: "B \<subseteq> U"
      and b: "b : B \<rightarrow> carrier K"
    unfolding span_def by auto
  hence B: "B \<subseteq> carrier V" using U by auto

  have B_A: "B - A \<subseteq> carrier V" and A_B: "A - B \<subseteq> carrier V" using A B by auto

  have a': "emb a A : A \<union> B \<rightarrow> carrier K"
    apply (rule Pi_I) unfolding emb_def using a by auto
  hence a'A: "emb a A : A \<rightarrow> carrier K" by auto
  have a'Z: "emb a A : B - A \<rightarrow> { zero K }"
    apply (rule Pi_I) unfolding emb_def using a by auto

  have b': "emb b B : A \<union> B \<rightarrow> carrier K"
    apply (rule Pi_I) unfolding emb_def using b by auto
  hence b'B: "emb b B : B \<rightarrow> carrier K" by auto
  have b'Z: "emb b B : A - B \<rightarrow> { zero K }"
    apply (rule Pi_I) unfolding emb_def using b by auto

  show ?thesis
    unfolding span_def
    proof (rule,intro exI conjI)
      let ?v = "lincomb (emb a A) (A \<union> B)"
      let ?w = "lincomb (emb b B) (A \<union> B)"
      let ?ab = "\<lambda>u. (emb a A) u \<oplus>\<^bsub>K\<^esub> (emb b B) u"
      show finAB: "finite (A \<union> B)" using finA finB by auto
      show "A \<union> B \<subseteq> U" using AU BU by auto
      show "?ab : A \<union> B \<rightarrow> carrier K" using a' b' by auto
      have "v = ?v"
        using va lincomb_restrict[OF A a emb_restrict[symmetric]]
        using lincomb_clean[OF A B_A] a'A a'Z finA finB by simp
      moreover have "w = ?w"
        apply (subst Un_commute)
        using wb lincomb_restrict[OF B b emb_restrict[symmetric]]
        using lincomb_clean[OF B A_B] finA finB b'B b'Z by simp
      ultimately show "v \<oplus>\<^bsub>V\<^esub> w = lincomb ?ab (A \<union> B)"
        using lincomb_sum[OF finAB] A B a' b' by simp
    qed
qed

lemma span_neg:
  assumes U: "U \<subseteq> carrier V" and vU: "v : span U"
  shows "\<ominus>\<^bsub>V\<^esub> v : span U"
proof -
  have v: "v : carrier V" using vU U unfolding span_def by auto
  from vU[unfolded span_def]
  obtain a A
    where finA: "finite A"
      and AU: "A \<subseteq> U"
      and a: "a \<in> A \<rightarrow> carrier K"
      and va: "v = lincomb a A" by auto
  hence A: "A \<subseteq> carrier V" using U by simp
  let ?a = "\<lambda>u. \<ominus>\<^bsub>K\<^esub> one K \<otimes>\<^bsub>K\<^esub> a u"

  have "\<ominus>\<^bsub>V\<^esub> v = \<ominus>\<^bsub>K\<^esub> one K \<odot>\<^bsub>V\<^esub> v" using smult_minus_1_back[OF v].
  also have "... = \<ominus>\<^bsub>K\<^esub> one K \<odot>\<^bsub>V\<^esub> lincomb a A" using va by simp
  finally have main: "\<ominus>\<^bsub>V\<^esub> v = lincomb ?a A"
    unfolding lincomb_distrib[OF A a R.a_inv_closed[OF R.one_closed]] by auto
  show ?thesis
    unfolding span_def
    apply rule
    using main a finA AU by force
qed

lemma span_closed[simp]: "U \<subseteq> carrier V \<Longrightarrow> v : span U \<Longrightarrow> v : carrier V"
  unfolding span_def by auto

lemma span_add:
  assumes U: "U \<subseteq> carrier V" and vU: "v : span U" and w[simp]: "w : carrier V"
  shows "w : span U \<longleftrightarrow> v \<oplus>\<^bsub>V\<^esub> w : span U" (is "?L \<longleftrightarrow> ?R")
proof
  show "?L \<Longrightarrow> ?R" using span_add1[OF U vU] by auto
  assume R: "?R" show "?L"
  proof -
    have v[simp]: "v : carrier V" using vU U by simp
    have "w = zero V \<oplus>\<^bsub>V\<^esub> w" using M.l_zero by auto
    also have "... = \<ominus>\<^bsub>V\<^esub> v \<oplus>\<^bsub>V\<^esub> v \<oplus>\<^bsub>V\<^esub> w" using M.l_neg by auto
    also have "... = \<ominus>\<^bsub>V\<^esub> v \<oplus>\<^bsub>V\<^esub> (v \<oplus>\<^bsub>V\<^esub> w)"
      using M.l_zero M.a_assoc M.a_closed by auto
    also have "... : span U" using span_neg[OF U vU] span_add1[OF U] R by auto
    finally show ?thesis.
  qed
qed


lemma lincomb_union:
  assumes U: "U \<subseteq> carrier V"
      and U'[simp]: "U' \<subseteq> carrier V"
      and disj: "U \<inter> U' = {}"
      and finU: "finite U"
      and finU': "finite U'"
      and a: "a : U \<union> U' \<rightarrow> carrier K"
    shows "lincomb a (U \<union> U') = lincomb a U \<oplus>\<^bsub>V\<^esub> lincomb a U'"
  using finU U disj a
proof (induct set:finite)
  case empty thus ?case by (subst(2) lincomb_def, simp) next
  case (insert u U) thus ?case
    unfolding Un_insert_left
    using lincomb_insert2 finU' insert a_assoc by auto
qed

lemma span_union1:
  assumes U: "U \<subseteq> carrier V" and U': "U' \<subseteq> carrier V" and UU': "span U = span U'"
      and W: "W \<subseteq> carrier V" and W': "W' \<subseteq> carrier V" and WW': "span W = span W'"
  shows "span (U \<union> W) \<subseteq> span (U' \<union> W')" (is "?L \<subseteq> ?R")
proof
  fix x assume "x : ?L"
  then obtain a A
    where finA: "finite A"
      and AUW: "A \<subseteq> U \<union> W"
      and x: "x = lincomb a A"
      and a: "a : A \<rightarrow> carrier K"
    unfolding span_def by auto
  let ?AU = "A \<inter> U" and ?AW = "A \<inter> W - U"
  have AU: "?AU \<subseteq> carrier V" using U by auto
  have AW: "?AW \<subseteq> carrier V" using W by auto
  have disj: "?AU \<inter> ?AW = {}" by auto
  have U'W': "U' \<union> W' \<subseteq> carrier V" using U' W' by auto

  have "?AU \<union> ?AW = A" using AUW by auto
  hence "x = lincomb a (?AU \<union> ?AW)" using x by auto
  hence "x = lincomb a ?AU \<oplus>\<^bsub>V\<^esub> lincomb a ?AW"
    using lincomb_union[OF AU AW disj] finA a by auto
  moreover
    have "lincomb a ?AU : span U" and "lincomb a ?AW : span W"
      unfolding span_def using AU a finA by auto
    hence "lincomb a ?AU : span U'" and "lincomb a ?AW : span W'"
      using UU' WW' by auto
    hence "lincomb a ?AU : ?R" and "lincomb a ?AW : ?R"
      using span_is_monotone[OF Un_upper1, of U']
      using span_is_monotone[OF Un_upper2, of W'] by auto
  ultimately
    show "x : ?R" using span_add1[OF U'W'] by auto
qed

lemma span_Un:
  assumes U: "U \<subseteq> carrier V" and U': "U' \<subseteq> carrier V" and UU': "span U = span U'"
      and W: "W \<subseteq> carrier V" and W': "W' \<subseteq> carrier V" and WW': "span W = span W'"
  shows "span (U \<union> W) = span (U' \<union> W')" (is "?L = ?R")
  using span_union1[OF assms]
  using span_union1[OF U' U UU'[symmetric] W' W WW'[symmetric]]
  by auto

lemma lincomb_zero:
  assumes U: "U \<subseteq> carrier V" and a: "a : U \<rightarrow> {zero K}"
  shows "lincomb a U = zero V"
  using U a
proof (induct U rule: infinite_finite_induct)
  case empty show ?case unfolding lincomb_def by auto next
  case (insert u U)
    hence "a \<in> insert u U \<rightarrow> carrier K" using zero_closed by force
    thus ?case using insert by (subst lincomb_insert2; auto)
qed (auto simp: lincomb_def)

end

context module
begin

lemma lincomb_empty[simp]: "lincomb a {} = \<zero>\<^bsub>M\<^esub>"
  unfolding lincomb_def by auto

end

context linear_map
begin

interpretation Ker: vectorspace K "(V.vs kerT)"
  using kerT_is_subspace
  using V.subspace_is_vs by blast

interpretation im: vectorspace K "(W.vs imT)"
  using imT_is_subspace
  using W.subspace_is_vs by blast

lemma inj_imp_Ker0:
assumes "inj_on T (carrier V)"
shows "carrier (V.vs kerT) = {\<zero>\<^bsub>V\<^esub>}"
  unfolding mod_hom.ker_def
  using assms inj_on_contraD by fastforce

lemma Ke0_imp_inj:
assumes c: "carrier (V.vs kerT) = {\<zero>\<^bsub>V\<^esub>}"
shows "inj_on T (carrier V)"
proof (auto simp add: inj_on_def)
  fix x y
  assume x: "x \<in> carrier V" and y: "y \<in> carrier V"
  and Tx_Ty: "T x = T y" 
  hence "T x \<ominus>\<^bsub>W\<^esub> T y = \<zero>\<^bsub>W\<^esub>" using W.module.M.minus_other_side by auto
  hence "T (x \<ominus>\<^bsub>V\<^esub> y) = \<zero>\<^bsub>W\<^esub>" by (simp add: x y)
  hence "x \<ominus>\<^bsub>V\<^esub> y \<in> carrier (V.vs kerT)" by (simp add: mod_hom.ker_def x y) 
  hence "x \<ominus>\<^bsub>V\<^esub> y = \<zero>\<^bsub>V\<^esub>" using c by fast
  thus "x = y" by (simp add: x y)
qed

corollary Ke0_iff_inj: "inj_on T (carrier V) = (carrier (V.vs kerT) = {\<zero>\<^bsub>V\<^esub>})"
using inj_imp_Ker0 Ke0_imp_inj by auto

lemma inj_imp_dim_ker0:
assumes "inj_on T (carrier V)"
shows "vectorspace.dim K (V.vs kerT) = 0"
proof (unfold Ker.dim_def, rule Least_eq_0, rule exI[of _ "{}"])
    have Ker_rw: "carrier (V.vs kerT) = {\<zero>\<^bsub>V\<^esub>}" 
      unfolding mod_hom.ker_def
      using assms inj_on_contraD by fastforce
    have "finite {}" by simp 
    moreover have "card {} = 0" by simp
    moreover have "{} \<subseteq> carrier (V.vs kerT)" by simp
    moreover have "Ker.gen_set {}" unfolding Ker_rw by (simp add: Ker.span_empty)
    ultimately show "finite {} \<and> card {} = 0 \<and> {} \<subseteq> carrier (V.vs kerT) \<and> Ker.gen_set {}" by simp
qed


lemma surj_imp_imT_carrier:
assumes surj: "T` (carrier V) = carrier W"
shows "(imT) = carrier W"
by (simp add: surj im_def) 

lemma dim_eq:
assumes fin_dim_V: "V.fin_dim"
and i: "inj_on T (carrier V)" and surj: "T` (carrier V) = carrier W"
shows "V.dim = W.dim"
proof -
  have dim0: "vectorspace.dim K (V.vs kerT) = 0" 
    by (rule inj_imp_dim_ker0[OF i])
  have imT_W: "(imT) = carrier W"
    by (rule surj_imp_imT_carrier[OF surj])
  have rnt: "vectorspace.dim K (W.vs imT) + vectorspace.dim K (V.vs kerT) = V.dim"
    by (rule rank_nullity[OF fin_dim_V])
  hence "V.dim = vectorspace.dim K (W.vs imT)" using dim0 by auto
  also have "...  = W.dim" using imT_W by auto
  finally show ?thesis using fin_dim_V by auto
qed       


lemma lincomb_linear_image:
assumes inj_T: "inj_on T (carrier V)"
assumes A_in_V: "A \<subseteq> carrier V" and a: "a \<in> (T`A) \<rightarrow> carrier K"
assumes f: "finite A"
shows "W.module.lincomb a (T`A) = T (V.module.lincomb (a \<circ> T) A)"
using f using A_in_V a
proof (induct A)
  case empty thus ?case by auto
next
  case (insert x A)
  have T_insert_rw: "T ` insert x A = insert (T x) (T` A)" by simp
  have "W.module.lincomb a (T ` insert x A) = W.module.lincomb a (insert (T x) (T` A))" 
    unfolding T_insert_rw ..
  also have "... =  a (T x) \<odot>\<^bsub>W\<^esub> (T x) \<oplus>\<^bsub>W\<^esub> W.module.lincomb a (T` A)"
  proof (rule W.lincomb_insert2)
    show "finite (T ` A)" by (simp add: insert.hyps(1))
    show "T ` A \<subseteq> carrier W" using insert.prems(1) by auto
    show "a \<in> insert (T x) (T ` A) \<rightarrow> carrier K" 
      using insert.prems(2) by blast
    show "T x \<notin> T ` A" 
      by (meson inj_T inj_on_image_mem_iff_alt insert.hyps(2) insert.prems(1) insert_subset)
    show "T x \<in> carrier W" using insert.prems(1) by blast
  qed
  also have "... = a (T x) \<odot>\<^bsub>W\<^esub> (T x) \<oplus>\<^bsub>W\<^esub> (T (V.module.lincomb (a \<circ> T) A))"
    using insert.hyps(3) insert.prems(1) insert.prems(2) by fastforce 
  also have "... = T (a (T x) \<odot>\<^bsub>V\<^esub> x) \<oplus>\<^bsub>W\<^esub> (T (V.module.lincomb (a \<circ> T) A))"
    using insert.prems(1) insert.prems(2) by auto
  also have "... = T ((a (T x) \<odot>\<^bsub>V\<^esub> x) \<oplus>\<^bsub>V\<^esub> (V.module.lincomb (a \<circ> T) A))"
  proof (rule T_add[symmetric])
    show "a (T x) \<odot>\<^bsub>V\<^esub> x \<in> carrier V" using insert.prems(1) insert.prems(2) by auto
    show "V.module.lincomb (a \<circ> T) A \<in> carrier V"
    proof (rule V.module.lincomb_closed)
      show "A \<subseteq> carrier V" using insert.prems(1) by blast
      show "a \<circ> T \<in> A \<rightarrow> carrier K" using coeff_in_ring insert.prems(2) by auto
    qed
  qed
  also have "... = T (V.module.lincomb (a \<circ> T) (insert x A))"
  proof (rule arg_cong[of _ _ T])
    have "a \<circ> T \<in> insert x A \<rightarrow> carrier K"
      using comp_def insert.prems(2) by auto
    then show "a (T x) \<odot>\<^bsub>V\<^esub> x \<oplus>\<^bsub>V\<^esub> V.module.lincomb (a \<circ> T) A 
      = V.module.lincomb (a \<circ> T) (insert x A)"
      using V.lincomb_insert2 insert.hyps(1) insert.hyps(2) insert.prems(1) by force
  qed
  finally show ?case .
qed
   


lemma surj_fin_dim:  
  assumes fd: "V.fin_dim" and surj: "T` (carrier V) = carrier W"
  shows image_fin_dim: "W.fin_dim"
    using rank_nullity_main(2)[OF fd surj] .

lemma linear_inj_image_is_basis:
assumes inj_T: "inj_on T (carrier V)" and surj: "T` (carrier V) = carrier W"
and basis_B: "V.basis B"
and fin_dim_V: "V.fin_dim"
shows "W.basis (T`B)"
proof (rule W.dim_li_is_basis)
  have lm: "linear_map K V W T" by intro_locales
  have inj_TB: "inj_on T B"
    by (meson basis_B inj_T subset_inj_on V.basis_def)
  show "W.fin_dim" by (rule surj_fin_dim[OF fin_dim_V surj])  
  show "finite (T ` B)"
  proof (rule finite_imageI, rule V.fin[OF fin_dim_V])
    show "V.module.lin_indpt B" using basis_B unfolding V.basis_def by auto
    show "B \<subseteq> carrier V" using basis_B unfolding V.basis_def by auto
  qed
  show "T ` B \<subseteq> carrier W" using basis_B unfolding V.basis_def by auto
  show "W.dim \<le> card (T ` B)"
  proof -
    have d: "V.dim = W.dim" by (rule dim_eq[OF fin_dim_V inj_T surj])
    have "card (T` B) = card B" by (simp add: card_image inj_TB)
    also have "... = V.dim" using basis_B fin_dim_V V.basis_def V.dim_basis V.fin by auto
    finally show ?thesis using d by simp
  qed
  show "W.module.lin_indpt (T ` B)"
  proof (rule W.module.finite_lin_indpt2)
     show fin_TB: "finite (T ` B)" by fact
     show TB_W: "T ` B \<subseteq> carrier W" by fact
     fix a assume a: "a \<in> T ` B \<rightarrow> carrier K" and lc_a: "W.module.lincomb a (T ` B) = \<zero>\<^bsub>W\<^esub>"
     show "\<forall>v\<in>T ` B. a v = \<zero>\<^bsub>K\<^esub>" 
     proof (rule ballI)
      fix v assume v: "v \<in> T ` B"
      have "W.module.lincomb a (T ` B) = T (V.module.lincomb (a \<circ> T) B)"
      proof (rule lincomb_linear_image[OF inj_T])
        show "B \<subseteq> carrier V" using V.vectorspace_axioms basis_B vectorspace.basis_def by blast
        show "a \<in> T ` B \<rightarrow> carrier K" by (simp add: a)
        show "finite B" using fin_TB finite_image_iff inj_TB by blast
      qed
      hence T_lincomb: "T (V.module.lincomb (a \<circ> T) B) = \<zero>\<^bsub>W\<^esub>" using lc_a by simp
      have lincomb_0: "V.module.lincomb (a \<circ> T) B = \<zero>\<^bsub>V\<^esub>"
      proof -
        have "a \<circ> T \<in> B \<rightarrow> carrier K"
          using a by auto
        then show ?thesis
          by (metis V.module.M.zero_closed V.module.lincomb_closed 
            T_lincomb basis_B f0_is_0 inj_T inj_onD  V.basis_def)
      qed 
      have "(a \<circ> T) \<in> B \<rightarrow> {\<zero>\<^bsub>K\<^esub>}" 
      proof (rule V.not_lindepD[OF _ _ _ _ lincomb_0])
        show "V.module.lin_indpt B" using V.basis_def basis_B by blast
        show "finite B" using fin_TB finite_image_iff inj_TB by auto
        show "B \<subseteq> B" by auto
        show "a \<circ> T \<in> B \<rightarrow> carrier K" using a by auto
      qed
      thus "a v = \<zero>\<^bsub>K\<^esub>" using v by auto
    qed
  qed
qed

end

lemma (in vectorspace) dim1I:
assumes "gen_set {v}"
assumes "v \<noteq> \<zero>\<^bsub>V\<^esub>" "v \<in> carrier V"
shows "dim = 1"
proof -
  have "basis {v}" by (metis assms(1) assms(2) assms(3) basis_def empty_iff empty_subsetI
   finite.emptyI finite_lin_indpt2 insert_iff insert_subset insert_union lin_dep_iff_in_span
   span_empty)
  then show ?thesis using dim_basis by force
qed

lemma (in vectorspace) dim0I:
assumes "gen_set {\<zero>\<^bsub>V\<^esub>}"
shows "dim = 0"
proof -
  have "basis {}" unfolding basis_def using already_in_span assms finite_lin_indpt2 span_zero by auto
  then show ?thesis using dim_basis by force
qed

lemma (in vectorspace) dim_le1I:
assumes "gen_set {v}"
assumes "v \<in> carrier V"
shows "dim \<le> 1"
by (metis One_nat_def assms(1) assms(2) bot.extremum card.empty card.insert empty_iff finite.intros(1)
finite.intros(2) insert_subset vectorspace.gen_ge_dim vectorspace_axioms)

definition find_indices where "find_indices x xs \<equiv> [i \<leftarrow> [0..<length xs]. xs!i = x]"

lemma find_indices_Nil [simp]:
  "find_indices x [] = []"
  by (simp add: find_indices_def)

lemma find_indices_Cons:
  "find_indices x (y#ys) = (if x = y then Cons 0 else id) (map Suc (find_indices x ys))"
apply (unfold find_indices_def length_Cons, subst upt_conv_Cons, simp)
apply (fold map_Suc_upt, auto simp: filter_map o_def) done

lemma find_indices_snoc [simp]:
  "find_indices x (ys@[y]) = find_indices x ys @ (if x = y then [length ys] else [])"
  by (unfold find_indices_def, auto intro!: filter_cong simp: nth_append)

lemma mem_set_find_indices [simp]: "i \<in> set (find_indices x xs) \<longleftrightarrow> i < length xs \<and> xs!i = x"
  by (auto simp: find_indices_def)

lemma distinct_find_indices: "distinct (find_indices x xs)"
  unfolding find_indices_def by simp 

context abelian_monoid begin

definition sumlist
  where "sumlist xs \<equiv> foldr (\<oplus>) xs \<zero>"
  (* fold is not good as it reverses the list, although the most general locale for monoids with
     \<oplus> is already Abelian in Isabelle 2016-1. foldl is OK but it will not simplify Cons. *)

lemma [simp]:
  shows sumlist_Cons: "sumlist (x#xs) = x \<oplus> sumlist xs"
    and sumlist_Nil: "sumlist [] = \<zero>"
  by (simp_all add: sumlist_def)

lemma sumlist_carrier [simp]:
  assumes "set xs \<subseteq> carrier G" shows "sumlist xs \<in> carrier G"
  using assms by (induct xs, auto)

lemma sumlist_neutral:
  assumes "set xs \<subseteq> {\<zero>}" shows "sumlist xs = \<zero>"
proof (insert assms, induct xs)
  case (Cons x xs)
  then have "x = \<zero>" and "set xs \<subseteq> {\<zero>}" by auto
  with Cons.hyps show ?case by auto
qed simp

lemma sumlist_append:
  assumes "set xs \<subseteq> carrier G" and "set ys \<subseteq> carrier G"
  shows "sumlist (xs @ ys) = sumlist xs \<oplus> sumlist ys"
proof (insert assms, induct xs arbitrary: ys)
  case (Cons x xs)
  have "sumlist (xs @ ys) = sumlist xs \<oplus> sumlist ys"
    using Cons.prems by (auto intro: Cons.hyps)
  with Cons.prems show ?case by (auto intro!: a_assoc[symmetric])
qed auto

lemma sumlist_snoc:
  assumes "set xs \<subseteq> carrier G" and "x \<in> carrier G"
  shows "sumlist (xs @ [x]) = sumlist xs \<oplus> x"
  by (subst sumlist_append, insert assms, auto)

lemma sumlist_as_finsum:
  assumes "set xs \<subseteq> carrier G" and "distinct xs" shows "sumlist xs = (\<Oplus>x\<in>set xs. x)"
  using assms by (induct xs, auto intro:finsum_insert[symmetric])

lemma sumlist_map_as_finsum:
  assumes "f : set xs \<rightarrow> carrier G" and "distinct xs"
  shows "sumlist (map f xs) = (\<Oplus>x \<in> set xs. f x)"
  using assms by (induct xs, auto)

definition summset where "summset M \<equiv> fold_mset (\<oplus>) \<zero> M"

lemma summset_empty [simp]: "summset {#} = \<zero>" by (simp add: summset_def)

lemma fold_mset_add_carrier: "a \<in> carrier G \<Longrightarrow> set_mset M \<subseteq> carrier G \<Longrightarrow> fold_mset (\<oplus>) a M \<in> carrier G" 
proof (induct M arbitrary: a)
  case (add x M)
  thus ?case by 
    (subst comp_fun_commute_on.fold_mset_add_mset[of _ "carrier G"], unfold_locales, auto simp: a_lcomm)
qed simp

lemma summset_carrier[intro]: "set_mset M \<subseteq> carrier G \<Longrightarrow> summset M \<in> carrier G" 
  unfolding summset_def by (rule fold_mset_add_carrier, auto)  

lemma summset_add_mset[simp]:
  assumes a: "a \<in> carrier G" and MG: "set_mset M \<subseteq> carrier G"
  shows "summset (add_mset a M) = a \<oplus> summset M"
  using assms 
  by (auto simp add: summset_def)
   (rule comp_fun_commute_on.fold_mset_add_mset, unfold_locales, auto simp add: a_lcomm)    
 
lemma sumlist_as_summset:
  assumes "set xs \<subseteq> carrier G" shows "sumlist xs = summset (mset xs)"
  by (insert assms, induct xs, auto)

lemma sumlist_rev:
  assumes "set xs \<subseteq> carrier G"
  shows "sumlist (rev xs) = sumlist xs"
  using assms by (simp add: sumlist_as_summset)

lemma sumlist_as_fold:
  assumes "set xs \<subseteq> carrier G"
  shows "sumlist xs = fold (\<oplus>) xs \<zero>"
  by (fold sumlist_rev[OF assms], simp add: sumlist_def foldr_conv_fold)

end

context Module.module begin

definition lincomb_list
where "lincomb_list c vs = sumlist (map (\<lambda>i. c i \<odot>\<^bsub>M\<^esub> vs ! i) [0..<length vs])"

lemma lincomb_list_carrier:
  assumes "set vs \<subseteq> carrier M" and "c : {0..<length vs} \<rightarrow> carrier R"
  shows "lincomb_list c vs \<in> carrier M"
  by (insert assms, unfold lincomb_list_def, intro sumlist_carrier, auto intro!: smult_closed)

lemma lincomb_list_Nil [simp]: "lincomb_list c [] = \<zero>\<^bsub>M\<^esub>"
  by (simp add: lincomb_list_def)

lemma lincomb_list_Cons [simp]:
  "lincomb_list c (v#vs) = c 0 \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> lincomb_list (c o Suc) vs"
  by (unfold lincomb_list_def length_Cons, subst upt_conv_Cons, simp, fold map_Suc_upt, simp add: o_def)

lemma lincomb_list_eq_0:
  assumes "\<And>i. i < length vs \<Longrightarrow> c i \<odot>\<^bsub>M\<^esub> vs ! i = \<zero>\<^bsub>M\<^esub>"
  shows "lincomb_list c vs = \<zero>\<^bsub>M\<^esub>"
proof (insert assms, induct vs arbitrary:c)
  case (Cons v vs)
  from Cons.prems[of 0] have [simp]: "c 0 \<odot>\<^bsub>M\<^esub> v = \<zero>\<^bsub>M\<^esub>" by auto
  from Cons.prems[of "Suc _"] Cons.hyps have "lincomb_list (c \<circ> Suc) vs = \<zero>\<^bsub>M\<^esub>" by auto
  then show ?case by (simp add: o_def)
qed simp

definition mk_coeff where "mk_coeff vs c v \<equiv> R.sumlist (map c (find_indices v vs))"

lemma mk_coeff_carrier:
  assumes "c : {0..<length vs} \<rightarrow> carrier R" shows "mk_coeff vs c w \<in> carrier R"
  by (insert assms, auto simp: mk_coeff_def find_indices_def intro!:R.sumlist_carrier elim!:funcset_mem)

lemma mk_coeff_Cons:
  assumes "c : {0..<length (v#vs)} \<rightarrow> carrier R"
  shows "mk_coeff (v#vs) c = (\<lambda>w. (if w = v then c 0 else \<zero>) \<oplus> mk_coeff vs (c o Suc) w)"
proof-
  from assms have "c o Suc : {0..<length vs} \<rightarrow> carrier R" by auto
  from mk_coeff_carrier[OF this] assms
  show ?thesis by (auto simp add: mk_coeff_def find_indices_Cons)
qed

lemma mk_coeff_0[simp]:
  assumes "v \<notin> set vs"
  shows "mk_coeff vs c v = \<zero>"
proof -
  have "(find_indices v vs) = []" using assms unfolding find_indices_def
    by (simp add: in_set_conv_nth)
  thus ?thesis  unfolding mk_coeff_def by auto
qed  

lemma lincomb_list_as_lincomb:
  assumes vs_M: "set vs \<subseteq> carrier M" and c: "c : {0..<length vs} \<rightarrow> carrier R"
  shows "lincomb_list c vs = lincomb (mk_coeff vs c) (set vs)"
proof (insert assms, induct vs arbitrary: c)
  case (Cons v vs)
  have mk_coeff_Suc_closed: "mk_coeff vs (c \<circ> Suc) a \<in> carrier R" for a
    apply (rule mk_coeff_carrier)
    using Cons.prems unfolding Pi_def by auto
  have x_in: "x \<in> carrier M" if x: "x\<in> set vs" for x using Cons.prems x by auto
  show ?case apply (unfold mk_coeff_Cons[OF Cons.prems(2)] lincomb_list_Cons)
    apply (subst Cons) using Cons apply (force, force)
  proof (cases "v \<in> set vs", auto simp:insert_absorb)
    case False
    let ?f = "(\<lambda>va. ((if va = v then c 0 else \<zero>) \<oplus> mk_coeff vs (c \<circ> Suc) va) \<odot>\<^bsub>M\<^esub> va)"
    have mk_0: "mk_coeff vs (c \<circ> Suc) v = \<zero>" using False by auto
    have [simp]: "(c 0 \<oplus> \<zero>) = c 0"
      using Cons.prems(2) by force
    have finsum_rw: "(\<Oplus>\<^bsub>M\<^esub>va\<in>insert v (set vs). ?f va) = (?f v) \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs). ?f va)"
    proof (rule finsum_insert, auto simp add: False, rule smult_closed, rule R.a_closed)
      fix x
      show "mk_coeff vs (c \<circ> Suc) x \<in> carrier R" 
        using mk_coeff_Suc_closed by auto
      show "c 0 \<odot>\<^bsub>M\<^esub> v \<in> carrier M"
      proof (rule smult_closed)
        show "c 0 \<in> carrier R"
          using Cons.prems(2) by fastforce
        show "v \<in> carrier M"
          using Cons.prems(1) by auto
      qed
      show "\<zero> \<in> carrier R"
        by simp
      assume x: "x \<in> set vs" show "x \<in> carrier M"
        using Cons.prems(1) x by auto
    qed
    have finsum_rw2: 
      "(\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs). ?f va) = (\<Oplus>\<^bsub>M\<^esub>va\<in>set vs. (mk_coeff vs (c \<circ> Suc) va) \<odot>\<^bsub>M\<^esub> va)"
    proof (rule finsum_cong2, auto simp add: False)
      fix i assume i: "i \<in> set vs"
      have "c \<circ> Suc \<in> {0..<length vs} \<rightarrow> carrier R" using Cons.prems by auto
      then have [simp]: "mk_coeff vs (c \<circ> Suc) i \<in> carrier R" 
        using mk_coeff_Suc_closed by auto
      have "\<zero> \<oplus> mk_coeff vs (c \<circ> Suc) i = mk_coeff vs (c \<circ> Suc) i" by (rule R.l_zero, simp)
      then show "(\<zero> \<oplus> mk_coeff vs (c \<circ> Suc) i) \<odot>\<^bsub>M\<^esub> i = mk_coeff vs (c \<circ> Suc) i \<odot>\<^bsub>M\<^esub> i" 
        by auto
      show "(\<zero> \<oplus> mk_coeff vs (c \<circ> Suc) i) \<odot>\<^bsub>M\<^esub> i \<in> carrier M"
        using Cons.prems(1) i by auto
    qed
    show "c 0 \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> lincomb (mk_coeff vs (c \<circ> Suc)) (set vs) =
    lincomb (\<lambda>a. (if a = v then c 0 else \<zero>) \<oplus> mk_coeff vs (c \<circ> Suc) a) (insert v (set vs))" 
      unfolding lincomb_def
      unfolding finsum_rw mk_0 
      unfolding finsum_rw2 by auto
  next
    case True
    let ?f = "\<lambda>va. ((if va = v then c 0 else \<zero>) \<oplus> mk_coeff vs (c \<circ> Suc) va) \<odot>\<^bsub>M\<^esub> va"
    have rw: "(c 0 \<oplus> mk_coeff vs (c \<circ> Suc) v) \<odot>\<^bsub>M\<^esub> v 
      = (c 0 \<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (mk_coeff vs (c \<circ> Suc) v) \<odot>\<^bsub>M\<^esub> v"      
      using Cons.prems(1) Cons.prems(2) atLeast0_lessThan_Suc_eq_insert_0 
      using mk_coeff_Suc_closed smult_l_distr by auto
    have rw2: "((mk_coeff vs (c \<circ> Suc) v) \<odot>\<^bsub>M\<^esub> v) 
      \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs - {v}). ?f va) = (\<Oplus>\<^bsub>M\<^esub>v\<in>set vs. mk_coeff vs (c \<circ> Suc) v \<odot>\<^bsub>M\<^esub> v)"
    proof -
      have "(\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs - {v}). ?f va) = (\<Oplus>\<^bsub>M\<^esub>v\<in>set vs - {v}. mk_coeff vs (c \<circ> Suc) v \<odot>\<^bsub>M\<^esub> v)"
        by (rule finsum_cong2, unfold Pi_def, auto simp add: mk_coeff_Suc_closed x_in)
      moreover have "(\<Oplus>\<^bsub>M\<^esub>v\<in>set vs. mk_coeff vs (c \<circ> Suc) v \<odot>\<^bsub>M\<^esub> v) = ((mk_coeff vs (c \<circ> Suc) v) \<odot>\<^bsub>M\<^esub> v) 
        \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>v\<in>set vs - {v}. mk_coeff vs (c \<circ> Suc) v \<odot>\<^bsub>M\<^esub> v)"
        by (rule M.add.finprod_split, auto simp add: mk_coeff_Suc_closed True x_in)
      ultimately show ?thesis by auto
    qed
    have "lincomb (\<lambda>a. (if a = v then c 0 else \<zero>) \<oplus> mk_coeff vs (c \<circ> Suc) a) (set vs) 
      = (\<Oplus>\<^bsub>M\<^esub>va\<in>set vs. ?f va)" unfolding lincomb_def ..
    also have "... = ?f v \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs - {v}). ?f va)"
    proof (rule M.add.finprod_split)
      have c0_mkcoeff_in: "c 0 \<oplus> mk_coeff vs (c \<circ> Suc) v \<in> carrier R" 
      proof (rule R.a_closed)
        show "c 0 \<in> carrier R " using Cons.prems by auto
        show "mk_coeff vs (c \<circ> Suc) v \<in> carrier R"
          using mk_coeff_Suc_closed by auto
    qed
    moreover have "(\<zero> \<oplus> mk_coeff vs (c \<circ> Suc) va) \<odot>\<^bsub>M\<^esub> va \<in> carrier M"
      if va: "va \<in> carrier M" for va 
      by (rule smult_closed[OF _ va], rule R.a_closed, auto simp add: mk_coeff_Suc_closed)
    ultimately show "?f ` set vs \<subseteq> carrier M" using Cons.prems(1) by auto        
      show "finite (set vs)" by simp
      show "v \<in> set vs" using True by simp
    qed
    also have "... = (c 0 \<oplus> mk_coeff vs (c \<circ> Suc) v) \<odot>\<^bsub>M\<^esub> v 
      \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs - {v}). ?f va)" by auto
    also have "... = ((c 0 \<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (mk_coeff vs (c \<circ> Suc) v) \<odot>\<^bsub>M\<^esub> v) 
      \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs - {v}). ?f va)" unfolding rw by simp
    also have "... = (c 0 \<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (((mk_coeff vs (c \<circ> Suc) v) \<odot>\<^bsub>M\<^esub> v) 
      \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>va\<in>(set vs - {v}). ?f va))"
    proof (rule M.a_assoc)
      show "c 0 \<odot>\<^bsub>M\<^esub> v \<in> carrier M" 
        using Cons.prems(1) Cons.prems(2) by auto
      show "mk_coeff vs (c \<circ> Suc) v \<odot>\<^bsub>M\<^esub> v \<in> carrier M"
        using Cons.prems(1) mk_coeff_Suc_closed by auto
      show "(\<Oplus>\<^bsub>M\<^esub>va\<in>set vs - {v}. ((if va = v then c 0 else \<zero>) 
        \<oplus> mk_coeff vs (c \<circ> Suc) va) \<odot>\<^bsub>M\<^esub> va) \<in> carrier M"
        by (rule M.add.finprod_closed) (auto simp add: mk_coeff_Suc_closed x_in)
    qed
    also have "... = c 0 \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> (\<Oplus>\<^bsub>M\<^esub>v\<in>set vs. mk_coeff vs (c \<circ> Suc) v \<odot>\<^bsub>M\<^esub> v)"
      unfolding rw2 ..
    also have "... = c 0 \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> lincomb (mk_coeff vs (c \<circ> Suc)) (set vs)" 
      unfolding lincomb_def ..
    finally show "c 0 \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> lincomb (mk_coeff vs (c \<circ> Suc)) (set vs) 
      = lincomb (\<lambda>a. (if a = v then c 0 else \<zero>) \<oplus> mk_coeff vs (c \<circ> Suc) a) (set vs)" ..         
  qed
qed simp

definition "span_list vs \<equiv> {lincomb_list c vs | c. c : {0..<length vs} \<rightarrow> carrier R}"

lemma in_span_listI:
  assumes "c : {0..<length vs} \<rightarrow> carrier R" and "v = lincomb_list c vs"
  shows "v \<in> span_list vs"
  using assms by (auto simp: span_list_def)

lemma in_span_listE:
  assumes "v \<in> span_list vs"
      and "\<And>c. c : {0..<length vs} \<rightarrow> carrier R \<Longrightarrow> v = lincomb_list c vs \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto simp: span_list_def)

lemmas lincomb_insert2 = lincomb_insert[unfolded insert_union[symmetric]]

lemma lincomb_zero:
  assumes U: "U \<subseteq> carrier M" and a: "a : U \<rightarrow> {zero R}"
  shows "lincomb a U = zero M"
  using U a
proof (induct U rule: infinite_finite_induct)
  case empty show ?case unfolding lincomb_def by auto next
  case (insert u U)
    hence "a \<in> insert u U \<rightarrow> carrier R" using zero_closed by force
    thus ?case using insert by (subst lincomb_insert2; auto)
qed (auto simp: lincomb_def)

end

hide_const (open) Multiset.mult
end
