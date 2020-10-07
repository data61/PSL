(*  Title:       Reasoning about Lists via List Interleaving
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems - Gep S.p.A.
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjowiggins-it dot com
*)

section "List interleaving"

theory ListInterleaving
imports Main
begin

text \<open>
\null

Among the various mathematical tools introduced in his outstanding work on Communicating Sequential
Processes \cite{R2}, Hoare has defined \emph{interleaves} as the predicate satisfied by any three
lists \emph{s}, \emph{t}, emph{u} such that \emph{s} may be split into sublists alternately
extracted from \emph{t} and \emph{u}, whatever is the criterion for extracting an item from either
\emph{t} or \emph{u} in each step.

This paper enriches Hoare's definition by identifying such criterion with the truth value of a
predicate taking as inputs the head and the tail of \emph{s}. This enhanced \emph{interleaves}
predicate turns out to permit the proof of equalities between lists without the need of an
induction. Some rules that allow to infer \emph{interleaves} statements without induction,
particularly applying to the addition of a prefix to the input lists, are also proven. Finally, a
stronger version of the predicate, named \emph{Interleaves}, is shown to fulfil further rules
applying to the addition of a suffix to the input lists.

Throughout this paper, the salient points of definitions and proofs are commented; for additional
information, cf. Isabelle documentation, particularly \cite{R3}, \cite{R4}, \cite{R5}, and
\cite{R6}. For a sample nontrivial application of the mathematical machinery developed in this
paper, cf. \cite{R1}.
\<close>


subsection "A first version of interleaving"

text \<open>
Here below is the definition of predicate \<open>interleaves\<close>, as well as of a convenient symbolic
notation for it. As in the definition of predicate \emph{interleaves} formulated in \cite{R2}, the
recursive decomposition of the input lists is performed by item prepending. In the case of a list
\<open>ws\<close> constructed recursively by item appending rather than prepending, the statement that it
satisfies predicate \<open>interleaves\<close> with two further lists can nevertheless be proven by
induction using as input @{term "rev ws"}, rather than \<open>ws\<close> itself.

With respect to Hoare's homonymous predicate, \<open>interleaves\<close> takes as an additional input a
predicate \<open>P\<close>, which is a function of a single item and a list. Then, for statement
@{term "interleaves P (x # xs) (y # ys) (z # zs)"} to hold, the item picked for being \<open>x\<close> must
be \<open>y\<close> if \<open>P x xs\<close>, \<open>z\<close> otherwise. On the contrary, in case either the second or
the third list is empty, the truth value of \<open>P x xs\<close> does not matter and list
@{term "x # xs"} just has to match the other nonempty one, if any.

\null
\<close>

fun interleaves ::
 "('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"interleaves P (x # xs) (y # ys) (z # zs) = (if P x xs
  then x = y \<and> interleaves P xs ys (z # zs)
  else x = z \<and> interleaves P xs (y # ys) zs)" |
"interleaves P (x # xs) (y # ys) [] =
  (x = y \<and> interleaves P xs ys [])" |
"interleaves P (x # xs) [] (z # zs) =
  (x = z \<and> interleaves P xs [] zs)" |
"interleaves _ (_ # _) [] [] = False" |
"interleaves _ [] (_ # _) _ = False" |
"interleaves _ [] _ (_ # _) = False" |
"interleaves _ [] [] [] = True"

abbreviation interleaves_syntax ::
    "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> bool" 
    ("(_ \<simeq> {_, _, _})" [60, 60, 60] 51)
  where "xs \<simeq> {ys, zs, P} \<equiv> interleaves P xs ys zs"

text \<open>
\null

The advantage provided by this enhanced \emph{interleaves} predicate is that in case
@{term "xs \<simeq> {ys, zs, P}"}, fixing the values of \<open>xs\<close> and either \<open>ys\<close> or \<open>zs\<close> has
the effect of fixing the value of the remaining list, too. Namely, if @{term "xs \<simeq> {ys', zs, P}"}
also holds, then @{term "ys = ys'"}, and likewise, if @{term "xs \<simeq> {ys, zs', P}"} also holds, then
@{term "zs = zs'"}. Therefore, once two \emph{interleaves} statements @{term "xs \<simeq> {ys, zs, P}"},
@{term "xs' \<simeq> {ys', zs', P'}"} have been proven along with equalities @{term "xs = xs'"},
@{term "P = P'"}, and either @{term "zs = zs'"} or @{term "ys = ys'"}, possibly by induction, the
remaining equality, i.e. respectively @{term "ys = ys'"} and @{term "zs = zs'"}, can be inferred
without the need of a further induction.

Here below is the proof of this property as well as of other ones. Particularly, it is also proven
that in case @{term "xs \<simeq> {ys, zs, P}"}, lists \<open>ys\<close> and \<open>zs\<close> can be swapped by
replacing predicate \<open>P\<close> with its negation.

It is worth noting that fixing the values of \<open>ys\<close> and \<open>zs\<close> does not fix the value of
\<open>xs\<close> instead. A counterexample is @{term "ys = [y]"}, @{term "zs = [z]"} with @{term "y \<noteq> z"},
@{term "P y [z] = True"}, @{term "P z [y] = False"}, in which case both of the \emph{interleaves}
statements @{term "[y, z] \<simeq> {ys, zs, P}"} and @{term "[z, y] \<simeq> {ys, zs, P}"} hold.

\null
\<close>

lemma interleaves_length [rule_format]:
 "xs \<simeq> {ys, zs, P} \<longrightarrow> length xs = length ys + length zs"
proof (induction P xs ys zs rule: interleaves.induct, simp_all)
qed (rule conjI, (rule_tac [!] impI)+, simp_all)

lemma interleaves_nil:
 "[] \<simeq> {ys, zs, P} \<Longrightarrow> ys = [] \<and> zs = []"
by (rule interleaves.cases [of "(P, [], ys, zs)"], simp_all)

lemma interleaves_swap:
 "xs \<simeq> {ys, zs, P} = xs \<simeq> {zs, ys, \<lambda>w ws. \<not> P w ws}"
proof (induction P xs ys zs rule: interleaves.induct, simp_all)
  fix y' :: 'a and ys' zs' P'
  show "\<not> [] \<simeq> {zs', y' # ys', \<lambda>w ws. \<not> P' w ws}" by (cases zs', simp_all)
qed

lemma interleaves_equal_fst [rule_format]:
 "xs \<simeq> {ys, zs, P} \<longrightarrow> xs \<simeq> {ys', zs, P} \<longrightarrow> ys = ys'"
proof (induction xs arbitrary: ys ys' zs, (rule_tac [!] impI)+)
  fix ys ys' zs
  assume "[] \<simeq> {ys, zs, P}"
  hence "ys = [] \<and> zs = []" by (rule interleaves_nil)
  moreover assume "[] \<simeq> {ys', zs, P}"
  hence "ys' = [] \<and> zs = []" by (rule interleaves_nil)
  ultimately show "ys = ys'" by simp
next
  fix x xs ys ys' zs
  assume
    A: "\<And>ys ys' zs. xs \<simeq> {ys, zs, P} \<longrightarrow> xs \<simeq> {ys', zs, P} \<longrightarrow> ys = ys'" and
    B: "x # xs \<simeq> {ys, zs, P}" and
    B': "x # xs \<simeq> {ys', zs, P}"
  show "ys = ys'"
  proof (cases zs, case_tac [2] ys, case_tac [2-3] ys', simp_all)
    assume C: "zs = []"
    hence "\<exists>w ws. ys = w # ws" using B by (cases ys, simp_all)
    then obtain w ws where Y: "ys = w # ws" by blast
    hence D: "w = x" using B and C by simp
    have "xs \<simeq> {ws, [], P}" using B and C and Y by simp
    moreover have "\<exists>w' ws'. ys' = w' # ws'"
     using B' and C by (cases ys', simp_all)
    then obtain w' ws' where Y': "ys' = w' # ws'" by blast
    hence D': "w' = x" using B' and C by simp
    have "xs \<simeq> {ws', [], P}" using B' and C and Y' by simp
    moreover have "xs \<simeq> {ws, [], P} \<longrightarrow> xs \<simeq> {ws', [], P} \<longrightarrow> ws = ws'"
     using A .
    ultimately have "ws = ws'" by simp
    with Y and Y' and D and D' show ?thesis by simp
  next
    fix v vs w' ws'
    assume C: "zs = v # vs" and "ys = []"
    hence D: "xs \<simeq> {[], vs, P}" using B by simp
    assume E: "ys' = w' # ws'"
    have "P x xs \<or> \<not> P x xs" by simp
    moreover {
      assume "P x xs"
      hence "xs \<simeq> {ws', v # vs, P}" using B' and C and E by simp
      hence "length xs = Suc (length vs) + length ws'"
       by (simp add: interleaves_length)
      moreover have "length xs = length vs"
       using D by (simp add: interleaves_length)
      ultimately have False by simp
    }
    moreover {
      assume "\<not> P x xs"
      hence "xs \<simeq> {w' # ws', vs, P}" using B' and C and E by simp
      moreover have "xs \<simeq> {[], vs, P} \<longrightarrow> xs \<simeq> {w' # ws', vs, P} \<longrightarrow>
        [] = w' # ws'"
       using A .
      ultimately have "[] = w' # ws'" using D by simp
      hence False by simp
    }
    ultimately show False ..
  next
    fix v vs w ws
    assume C: "zs = v # vs" and "ys' = []"
    hence D: "xs \<simeq> {[], vs, P}" using B' by simp
    assume E: "ys = w # ws"
    have "P x xs \<or> \<not> P x xs" by simp
    moreover {
      assume "P x xs"
      hence "xs \<simeq> {ws, v # vs, P}" using B and C and E by simp
      hence "length xs = Suc (length vs) + length ws"
       by (simp add: interleaves_length)
      moreover have "length xs = length vs"
       using D by (simp add: interleaves_length)
      ultimately have False by simp
    }
    moreover {
      assume "\<not> P x xs"
      hence "xs \<simeq> {w # ws, vs, P}" using B and C and E by simp
      moreover have "xs \<simeq> {[], vs, P} \<longrightarrow> xs \<simeq> {w # ws, vs, P} \<longrightarrow> [] = w # ws"
       using A .
      ultimately have "[] = w # ws" using D by simp
      hence False by simp
    }
    ultimately show False ..
  next
    fix v vs w ws w' ws'
    assume C: "zs = v # vs" and D: "ys = w # ws" and D': "ys' = w' # ws'"
    have "P x xs \<or> \<not> P x xs" by simp
    moreover {
      assume E: "P x xs"
      hence F: "w = x" using B and C and D by simp
      have "xs \<simeq> {ws, v # vs, P}" using B and C and D and E by simp
      moreover have F': "w' = x" using B' and C and D' and E by simp
      have "xs \<simeq> {ws', v # vs, P}" using B' and C and D' and E by simp
      moreover have "xs \<simeq> {ws, v # vs, P} \<longrightarrow> xs \<simeq> {ws', v # vs, P} \<longrightarrow>
        ws = ws'"
       using A .
      ultimately have "ws = ws'" by simp
      hence "w = w' \<and> ws = ws'" using F and F' by simp
    }
    moreover {
      assume E: "\<not> P x xs"
      hence "xs \<simeq> {w # ws, vs, P}" using B and C and D by simp
      moreover have "xs \<simeq> {w' # ws', vs, P}"
       using B' and C and D' and E by simp
      moreover have "xs \<simeq> {w # ws, vs, P} \<longrightarrow> xs \<simeq> {w' # ws', vs, P} \<longrightarrow>
        w # ws = w' # ws'"
       using A .
      ultimately have "w # ws = w' # ws'" by simp
      hence "w = w' \<and> ws = ws'" by simp
    }
    ultimately show "w = w' \<and> ws = ws'" ..
  qed
qed

lemma interleaves_equal_snd:
 "xs \<simeq> {ys, zs, P} \<Longrightarrow> xs \<simeq> {ys, zs', P} \<Longrightarrow> zs = zs'"
by (subst (asm) (1 2) interleaves_swap, rule interleaves_equal_fst)

text \<open>
\null

Since \emph{interleaves} statements permit to prove equalities between lists without the need of an
induction, it is useful to search for rules that allow to infer such statements themselves without
induction, which is precisely what is done here below. Particularly, it is proven that under proper
assumptions, predicate @{term interleaves} keeps being satisfied by applying a filter, a mapping, or
the addition or removal of a prefix to the input lists.

\null
\<close>

lemma interleaves_all_nil:
 "xs \<simeq> {xs, [], P}"
by (induction xs, simp_all)

lemma interleaves_nil_all:
 "xs \<simeq> {[], xs, P}"
by (induction xs, simp_all)

lemma interleaves_equal_all_nil:
 "xs \<simeq> {ys, [], P} \<Longrightarrow> xs = ys"
by (insert interleaves_all_nil, rule interleaves_equal_fst)

lemma interleaves_equal_nil_all:
 "xs \<simeq> {[], zs, P} \<Longrightarrow> xs = zs"
by (insert interleaves_nil_all, rule interleaves_equal_snd)

lemma interleaves_filter [rule_format]:
  assumes A: "\<forall>x xs. P x (filter Q xs) = P x xs"
  shows "xs \<simeq> {ys, zs, P} \<longrightarrow> filter Q xs \<simeq> {filter Q ys, filter Q zs, P}"
proof (induction xs arbitrary: ys zs, rule_tac [!] impI, simp)
  fix ys zs
  assume "[] \<simeq> {ys, zs, P}"
  hence "ys = [] \<and> zs = []" by (rule interleaves_nil)
  thus "[] \<simeq> {filter Q ys, filter Q zs, P}" by simp
next
  fix x xs ys zs
  assume
    B: "\<And>ys' zs'. xs \<simeq> {ys', zs', P} \<longrightarrow>
      filter Q xs \<simeq> {filter Q ys', filter Q zs', P}" and
    C: "x # xs \<simeq> {ys, zs, P}"
  show "filter Q (x # xs) \<simeq> {filter Q ys, filter Q zs, P}"
  proof (cases ys, case_tac [!] zs, simp_all del: filter.simps, rule ccontr)
    assume "ys = []" and "zs = []"
    thus False using C by simp
  next
    fix z zs'
    assume "ys = []" and "zs = z # zs'"
    hence D: "x = z \<and> xs \<simeq> {[], zs', P}" using C by simp
    moreover have "xs \<simeq> {[], zs', P} \<longrightarrow>
      filter Q xs \<simeq> {filter Q [], filter Q zs', P}"
     using B .
    ultimately have "filter Q xs \<simeq> {[], filter Q zs', P}" by simp
    thus "filter Q (x # xs) \<simeq> {[], filter Q (z # zs'), P}" using D by simp
  next
    fix y ys'
    assume "ys = y # ys'" and "zs = []"
    hence D: "x = y \<and> xs \<simeq> {ys', [], P}" using C by simp
    moreover have "xs \<simeq> {ys', [], P} \<longrightarrow>
      filter Q xs \<simeq> {filter Q ys', filter Q [], P}"
     using B .
    ultimately have "filter Q xs \<simeq> {filter Q ys', [], P}" by simp
    thus "filter Q (x # xs) \<simeq> {filter Q (y # ys'), [], P}" using D by simp
  next
    fix y ys' z zs'
    assume "ys = y # ys'" and "zs = z # zs'"
    hence D: "x # xs \<simeq> {y # ys', z # zs', P}" using C by simp
    show "filter Q (x # xs) \<simeq> {filter Q (y # ys'), filter Q (z # zs'), P}"
    proof (cases "P x xs")
      case True
      hence E: "P x (filter Q xs)" using A by simp
      have F: "x = y \<and> xs \<simeq> {ys', z # zs', P}" using D and True by simp
      moreover have "xs \<simeq> {ys', z # zs', P} \<longrightarrow>
        filter Q xs \<simeq> {filter Q ys', filter Q (z # zs'), P}"
       using B .
      ultimately have G: "filter Q xs \<simeq> {filter Q ys', filter Q (z # zs'), P}"
       by simp
      show ?thesis
      proof (cases "Q x")
        assume "Q x"
        hence "filter Q (x # xs) = x # filter Q xs" by simp
        moreover have "filter Q (y # ys') = x # filter Q ys'"
         using \<open>Q x\<close> and F by simp
        ultimately show ?thesis using E and G
         by (cases "filter Q (z # zs')", simp_all)
      next
        assume "\<not> Q x"
        hence "filter Q (x # xs) = filter Q xs" by simp
        moreover have "filter Q (y # ys') = filter Q ys'"
         using \<open>\<not> Q x\<close> and F by simp
        ultimately show ?thesis using E and G
         by (cases "filter Q (z # zs')", simp_all)
      qed
    next
      case False
      hence E: "\<not> P x (filter Q xs)" using A by simp
      have F: "x = z \<and> xs \<simeq> {y # ys', zs', P}" using D and False by simp
      moreover have "xs \<simeq> {y # ys', zs', P} \<longrightarrow>
        filter Q xs \<simeq> {filter Q (y # ys'), filter Q zs', P}"
       using B .
      ultimately have G: "filter Q xs \<simeq> {filter Q (y # ys'), filter Q zs', P}"
       by simp
      show ?thesis
      proof (cases "Q x")
        assume "Q x"
        hence "filter Q (x # xs) = x # filter Q xs" by simp
        moreover have "filter Q (z # zs') = x # filter Q zs'"
         using \<open>Q x\<close> and F by simp
        ultimately show ?thesis using E and G
         by (cases "filter Q (y # ys')", simp_all)
      next
        assume "\<not> Q x"
        hence "filter Q (x # xs) = filter Q xs" by simp
        moreover have "filter Q (z # zs') = filter Q zs'"
         using \<open>\<not> Q x\<close> and F by simp
        ultimately show ?thesis using E and G
         by (cases "filter Q (z # zs')", simp_all)
      qed
    qed
  qed
qed

lemma interleaves_map [rule_format]:
  assumes A: "inj f"
  shows "xs \<simeq> {ys, zs, P} \<longrightarrow>
    map f xs \<simeq> {map f ys, map f zs, \<lambda>w ws. P (inv f w) (map (inv f) ws)}"
    (is "_ \<longrightarrow> _ \<simeq> {_, _, ?P'}")
proof (induction xs arbitrary: ys zs, rule_tac [!] impI, simp_all)
  fix ys zs
  assume "[] \<simeq> {ys, zs, P}"
  hence "ys = [] \<and> zs = []" by (rule interleaves_nil)
  thus "[] \<simeq> {map f ys, map f zs, ?P'}" by simp
next
  fix x xs ys zs
  assume
    B: "\<And>ys zs. xs \<simeq> {ys, zs, P} \<longrightarrow> map f xs \<simeq> {map f ys, map f zs, ?P'}" and
    C: "x # xs \<simeq> {ys, zs, P}"
  show "f x # map f xs \<simeq> {map f ys, map f zs, ?P'}"
  proof (cases ys, case_tac [!] zs, simp_all del: interleaves.simps(1))
    assume "ys = []" and "zs = []"
    thus False using C by simp
  next
    fix z zs'
    assume "ys = []" and "zs = z # zs'"
    hence "x = z \<and> xs \<simeq> {[], zs', P}" using C by simp
    moreover have "xs \<simeq> {[], zs', P} \<longrightarrow> map f xs \<simeq> {map f [], map f zs', ?P'}"
     using B .
    ultimately show "f x = f z \<and> map f xs \<simeq> {[], map f zs', ?P'}" by simp
  next
    fix y ys'
    assume "ys = y # ys'" and "zs = []"
    hence "x = y \<and> xs \<simeq> {ys', [], P}" using C by simp
    moreover have "xs \<simeq> {ys', [], P} \<longrightarrow> map f xs \<simeq> {map f ys', map f [], ?P'}"
     using B .
    ultimately show "f x = f y \<and> map f xs \<simeq> {map f ys', [], ?P'}" by simp
  next
    fix y ys' z zs'
    assume "ys = y # ys'" and "zs = z # zs'"
    hence D: "x # xs \<simeq> {y # ys', z # zs', P}" using C by simp
    show "f x # map f xs \<simeq> {f y # map f ys', f z # map f zs', ?P'}"
    proof (cases "P x xs")
      case True
      hence E: "?P' (f x) (map f xs)" using A by simp
      have "x = y \<and> xs \<simeq> {ys', z # zs', P}" using D and True by simp
      moreover have "xs \<simeq> {ys', z # zs', P} \<longrightarrow>
        map f xs \<simeq> {map f ys', map f (z # zs'), ?P'}"
       using B .
      ultimately have "f x = f y \<and> map f xs \<simeq> {map f ys', map f (z # zs'), ?P'}"
       by simp
      thus ?thesis using E by simp
    next
      case False
      hence E: "\<not> ?P' (f x) (map f xs)" using A by simp
      have "x = z \<and> xs \<simeq> {y # ys', zs', P}" using D and False by simp
      moreover have "xs \<simeq> {y # ys', zs', P} \<longrightarrow>
        map f xs \<simeq> {map f (y # ys'), map f zs', ?P'}"
       using B .
      ultimately have "f x = f z \<and> map f xs \<simeq> {map f (y # ys'), map f zs', ?P'}"
       by simp
      thus ?thesis using E by simp
    qed
  qed
qed

lemma interleaves_prefix_fst_1 [rule_format]:
  assumes A: "xs \<simeq> {ys, zs, P}"
  shows "(\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs)) \<longrightarrow>
    ws @ xs \<simeq> {ws @ ys, zs, P}"
proof (induction ws, simp_all add: A, rule impI)
  fix w ws
  assume B: "\<forall>n < Suc (length ws). P ((w # ws) ! n) (drop n ws @ xs)"
  assume "(\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs)) \<longrightarrow>
    ws @ xs \<simeq> {ws @ ys, zs, P}"
  moreover have "\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs)"
  proof (rule allI, rule impI)
    fix n
    assume "n < length ws"
    moreover have "Suc n < Suc (length ws) \<longrightarrow>
      P ((w # ws) ! (Suc n)) (drop (Suc n) ws @ xs)"
     using B ..
    ultimately show "P (ws ! n) (drop (Suc n) ws @ xs)" by simp
  qed
  ultimately have "ws @ xs \<simeq> {ws @ ys, zs, P}" ..
  moreover have "0 < Suc (length ws) \<longrightarrow> P ((w # ws) ! 0) (drop 0 ws @ xs)"
   using B ..
  hence "P w (ws @ xs)" by simp
  ultimately show "w # ws @ xs \<simeq> {w # ws @ ys, zs, P}" by (cases zs, simp_all)
qed

lemma interleaves_prefix_fst_2 [rule_format]:
 "ws @ xs \<simeq> {ws @ ys, zs, P} \<longrightarrow>
  (\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs)) \<longrightarrow>
  xs \<simeq> {ys, zs, P}"
proof (induction ws, simp_all, (rule impI)+)
  fix w ws
  assume A: "\<forall>n < Suc (length ws). P ((w # ws) ! n) (drop n ws @ xs)"
  hence "0 < Suc (length ws) \<longrightarrow> P ((w # ws) ! 0) (drop 0 ws @ xs)" ..
  hence "P w (ws @ xs)" by simp
  moreover assume "w # ws @ xs \<simeq> {w # ws @ ys, zs, P}"
  ultimately have "ws @ xs \<simeq> {ws @ ys, zs, P}" by (cases zs, simp_all)
  moreover assume "ws @ xs \<simeq> {ws @ ys, zs, P} \<longrightarrow>
    (\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs)) \<longrightarrow>
    xs \<simeq> {ys, zs, P}"
  ultimately have "(\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs)) \<longrightarrow>
    xs \<simeq> {ys, zs, P}"
   by simp
  moreover have "\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs)"
  proof (rule allI, rule impI)
    fix n
    assume "n < length ws"
    moreover have "Suc n < Suc (length ws) \<longrightarrow>
      P ((w # ws) ! (Suc n)) (drop (Suc n) ws @ xs)"
     using A ..
    ultimately show "P (ws ! n) (drop (Suc n) ws @ xs)" by simp
  qed
  ultimately show "xs \<simeq> {ys, zs, P}" ..
qed

lemma interleaves_prefix_fst [rule_format]:
 "\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs) \<Longrightarrow>
  xs \<simeq> {ys, zs, P} = ws @ xs \<simeq> {ws @ ys, zs, P}"
proof (rule iffI, erule interleaves_prefix_fst_1, simp)
qed (erule interleaves_prefix_fst_2, simp)

lemma interleaves_prefix_snd [rule_format]:
 "\<forall>n < length ws. \<not> P (ws ! n) (drop (Suc n) ws @ xs) \<Longrightarrow>
  xs \<simeq> {ys, zs, P} = ws @ xs \<simeq> {ys, ws @ zs, P}"
proof (subst (1 2) interleaves_swap)
qed (rule interleaves_prefix_fst, simp)


subsection "A second, stronger version of interleaving"

text \<open>
Simple counterexamples show that unlike prefixes, the addition or removal of suffixes to the input
lists does not generally preserve the validity of predicate @{term interleaves}. In fact, if
@{term "P y [x] = True"} with @{term "x \<noteq> y"}, then @{term "[y, x] \<simeq> {[x], [y], P}"} does not hold
although @{term "[y] \<simeq> {[], [y], \<lambda>w ws. P w (ws @ [x])}"} does, by virtue of lemma
@{thm interleaves_nil_all}. Similarly, @{term "[x, y] \<simeq> {[], [y, x], \<lambda>w ws. P w (ws @ [x])}"} does
not hold for @{term "x \<noteq> y"} even though @{term "[x, y, x] \<simeq> {[x], [y, x], P}"} does.

Both counterexamples would not work any longer if the truth value of the input predicate were
significant even if either the second or the third list is empty. In fact, in the former case,
condition @{term "P y [x] = True"} would entail the falseness of statement
@{term "[y] \<simeq> {[], [y], \<lambda>w ws. P w (ws @ [x])}"}, so that the validity of rule
@{term "[y] \<simeq> {[], [y], \<lambda>w ws. P w (ws @ [x])} \<Longrightarrow> [y, x] \<simeq> {[x], [y], P}"} would be preserved. In
the latter case, statement @{term "[x, y, x] \<simeq> {[x], [y, x], P}"} may only hold provided the last
item \<open>x\<close> of the first list is extracted from the third one, which would require that
@{term "\<not> P x []"}; thus, subordinating rule
@{term "[x, y, x] \<simeq> {[x], [y, x], P} \<Longrightarrow> [x, y] \<simeq> {[], [y, x], \<lambda>w ws. P w (ws @ [x])}"} to
condition @{term "P x []"} would preserve its validity.

This argument suggests that in order to obtain an \emph{interleaves} predicate whose validity is
also preserved upon the addition or removal of a suffix to the input lists, the truth value of the
input predicate must matter until both the second and the third list are empty. In what follows,
such a stronger version of the predicate, named \<open>Interleaves\<close>, is defined along with a
convenient symbolic notation for it.

\null
\<close>

fun Interleaves ::
 "('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"Interleaves P (x # xs) (y # ys) (z # zs) = (if P x xs
  then x = y \<and> Interleaves P xs ys (z # zs)
  else x = z \<and> Interleaves P xs (y # ys) zs)" |
"Interleaves P (x # xs) (y # ys) [] =
  (P x xs \<and> x = y \<and> Interleaves P xs ys [])" |
"Interleaves P (x # xs) [] (z # zs) =
  (\<not> P x xs \<and> x = z \<and> Interleaves P xs [] zs)" |
"Interleaves _ (_ # _) [] [] = False" |
"Interleaves _ [] (_ # _) _ = False" |
"Interleaves _ [] _ (_ # _) = False" |
"Interleaves _ [] [] [] = True"

abbreviation Interleaves_syntax ::
    "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> bool"
    ("(_ \<cong> {_, _, _})" [60, 60, 60] 51)
  where "xs \<cong> {ys, zs, P} \<equiv> Interleaves P xs ys zs"

text \<open>
\null

In what follows, it is proven that predicate @{term Interleaves} is actually not weaker than, viz.
is a sufficient condition for, predicate @{term interleaves}. Moreover, the former predicate is
shown to fulfil the same rules as the latter, although sometimes under more stringent assumptions
(cf. lemmas \<open>Interleaves_all_nil\<close>, \<open>Interleaves_nil_all\<close> with lemmas
@{thm interleaves_all_nil}, @{thm interleaves_nil_all}), and to have the further property that under
proper assumptions, its validity is preserved upon the addition or removal of a suffix to the input
lists.

\null
\<close>

lemma Interleaves_interleaves [rule_format]:
 "xs \<cong> {ys, zs, P} \<longrightarrow> xs \<simeq> {ys, zs, P}"
proof (induction P xs ys zs rule: interleaves.induct, simp_all)
qed (rule conjI, (rule_tac [!] impI)+, simp_all)

lemma Interleaves_length:
 "xs \<cong> {ys, zs, P} \<Longrightarrow> length xs = length ys + length zs"
by (drule Interleaves_interleaves, rule interleaves_length)

lemma Interleaves_nil:
 "[] \<cong> {ys, zs, P} \<Longrightarrow> ys = [] \<and> zs = []"
by (drule Interleaves_interleaves, rule interleaves_nil)

lemma Interleaves_swap:
 "xs \<cong> {ys, zs, P} = xs \<cong> {zs, ys, \<lambda>w ws. \<not> P w ws}"
proof (induction P xs ys zs rule: Interleaves.induct, simp_all)
  fix y' :: 'a and ys' zs' P'
  show "\<not> [] \<cong> {zs', y' # ys', \<lambda>w ws. \<not> P' w ws}" by (cases zs', simp_all)
qed

lemma Interleaves_equal_fst:
 "xs \<cong> {ys, zs, P} \<Longrightarrow> xs \<cong> {ys', zs, P} \<Longrightarrow> ys = ys'"
by ((drule Interleaves_interleaves)+, rule interleaves_equal_fst)

lemma Interleaves_equal_snd:
 "xs \<cong> {ys, zs, P} \<Longrightarrow> xs \<cong> {ys, zs', P} \<Longrightarrow> zs = zs'"
by ((drule Interleaves_interleaves)+, rule interleaves_equal_snd)

lemma Interleaves_equal_all_nil:
 "xs \<cong> {ys, [], P} \<Longrightarrow> xs = ys"
by (drule Interleaves_interleaves, rule interleaves_equal_all_nil)

lemma Interleaves_equal_nil_all:
 "xs \<cong> {[], zs, P} \<Longrightarrow> xs = zs"
by (drule Interleaves_interleaves, rule interleaves_equal_nil_all)

lemma Interleaves_filter [rule_format]:
  assumes A: "\<forall>x xs. P x (filter Q xs) = P x xs"
  shows "xs \<cong> {ys, zs, P} \<longrightarrow> filter Q xs \<cong> {filter Q ys, filter Q zs, P}"
proof (induction xs arbitrary: ys zs, rule_tac [!] impI, simp)
  fix ys zs
  assume "[] \<cong> {ys, zs, P}"
  hence "ys = [] \<and> zs = []" by (rule Interleaves_nil)
  thus "[] \<cong> {filter Q ys, filter Q zs, P}" by simp
next
  fix x xs ys zs
  assume
    B: "\<And>ys' zs'. xs \<cong> {ys', zs', P} \<longrightarrow>
      filter Q xs \<cong> {filter Q ys', filter Q zs', P}" and
    C: "x # xs \<cong> {ys, zs, P}"
  show "filter Q (x # xs) \<cong> {filter Q ys, filter Q zs, P}"
  proof (cases ys, case_tac [!] zs, simp_all del: filter.simps, rule ccontr)
    assume "ys = []" and "zs = []"
    thus False using C by simp
  next
    fix z zs'
    assume "ys = []" and "zs = z # zs'"
    hence D: "\<not> P x xs \<and> x = z \<and> xs \<cong> {[], zs', P}" using C by simp+
    moreover have "xs \<cong> {[], zs', P} \<longrightarrow>
      filter Q xs \<cong> {filter Q [], filter Q zs', P}"
     using B .
    ultimately have "filter Q xs \<cong> {[], filter Q zs', P}" by simp
    moreover have "\<not> P x (filter Q xs)" using A and D by simp+
    ultimately show "filter Q (x # xs) \<cong> {[], filter Q (z # zs'), P}"
     using D by simp
  next
    fix y ys'
    assume "ys = y # ys'" and "zs = []"
    hence D: "P x xs \<and> x = y \<and> xs \<cong> {ys', [], P}" using C by simp+
    moreover have "xs \<cong> {ys', [], P} \<longrightarrow>
      filter Q xs \<cong> {filter Q ys', filter Q [], P}"
     using B .
    ultimately have "filter Q xs \<cong> {filter Q ys', [], P}" by simp
    moreover have "P x (filter Q xs)" using A and D by simp+
    ultimately show "filter Q (x # xs) \<cong> {filter Q (y # ys'), [], P}"
     using D by simp
  next
    fix y ys' z zs'
    assume "ys = y # ys'" and "zs = z # zs'"
    hence D: "x # xs \<cong> {y # ys', z # zs', P}" using C by simp
    show "filter Q (x # xs) \<cong> {filter Q (y # ys'), filter Q (z # zs'), P}"
    proof (cases "P x xs")
      case True
      hence E: "P x (filter Q xs)" using A by simp
      have F: "x = y \<and> xs \<cong> {ys', z # zs', P}" using D and True by simp
      moreover have "xs \<cong> {ys', z # zs', P} \<longrightarrow>
        filter Q xs \<cong> {filter Q ys', filter Q (z # zs'), P}"
       using B .
      ultimately have G: "filter Q xs \<cong> {filter Q ys', filter Q (z # zs'), P}"
       by simp
      show ?thesis
      proof (cases "Q x")
        assume "Q x"
        hence "filter Q (x # xs) = x # filter Q xs" by simp
        moreover have "filter Q (y # ys') = x # filter Q ys'"
         using \<open>Q x\<close> and F by simp
        ultimately show ?thesis using E and G
         by (cases "filter Q (z # zs')", simp_all)
      next
        assume "\<not> Q x"
        hence "filter Q (x # xs) = filter Q xs" by simp
        moreover have "filter Q (y # ys') = filter Q ys'"
         using \<open>\<not> Q x\<close> and F by simp
        ultimately show ?thesis using E and G
         by (cases "filter Q (z # zs')", simp_all)
      qed
    next
      case False
      hence E: "\<not> P x (filter Q xs)" using A by simp
      have F: "x = z \<and> xs \<cong> {y # ys', zs', P}" using D and False by simp
      moreover have "xs \<cong> {y # ys', zs', P} \<longrightarrow>
        filter Q xs \<cong> {filter Q (y # ys'), filter Q zs', P}"
       using B .
      ultimately have G: "filter Q xs \<cong> {filter Q (y # ys'), filter Q zs', P}"
       by simp
      show ?thesis
      proof (cases "Q x")
        assume "Q x"
        hence "filter Q (x # xs) = x # filter Q xs" by simp
        moreover have "filter Q (z # zs') = x # filter Q zs'"
         using \<open>Q x\<close> and F by simp
        ultimately show ?thesis using E and G
         by (cases "filter Q (y # ys')", simp_all)
      next
        assume "\<not> Q x"
        hence "filter Q (x # xs) = filter Q xs" by simp
        moreover have "filter Q (z # zs') = filter Q zs'"
         using \<open>\<not> Q x\<close> and F by simp
        ultimately show ?thesis using E and G
         by (cases "filter Q (z # zs')", simp_all)
      qed
    qed
  qed
qed

lemma Interleaves_map [rule_format]:
  assumes A: "inj f"
  shows "xs \<cong> {ys, zs, P} \<longrightarrow>
    map f xs \<cong> {map f ys, map f zs, \<lambda>w ws. P (inv f w) (map (inv f) ws)}"
    (is "_ \<longrightarrow> _ \<cong> {_, _, ?P'}")
proof (induction xs arbitrary: ys zs, rule_tac [!] impI, simp_all)
  fix ys zs
  assume "[] \<cong> {ys, zs, P}"
  hence "ys = [] \<and> zs = []" by (rule Interleaves_nil)
  thus "[] \<cong> {map f ys, map f zs, ?P'}" by simp
next
  fix x xs ys zs
  assume
    B: "\<And>ys zs. xs \<cong> {ys, zs, P} \<longrightarrow> map f xs \<cong> {map f ys, map f zs, ?P'}" and
    C: "x # xs \<cong> {ys, zs, P}"
  show "f x # map f xs \<cong> {map f ys, map f zs, ?P'}"
  proof (cases ys, case_tac [!] zs, simp_all del: Interleaves.simps(1-3))
    assume "ys = []" and "zs = []"
    thus False using C by simp
  next
    fix z zs'
    assume "ys = []" and "zs = z # zs'"
    hence D: "\<not> P x xs \<and> x = z \<and> xs \<cong> {[], zs', P}" using C by simp+
    moreover have "xs \<cong> {[], zs', P} \<longrightarrow> map f xs \<cong> {map f [], map f zs', ?P'}"
     using B .
    ultimately have "map f xs \<cong> {[], map f zs', ?P'}" by simp
    moreover have "\<not> ?P' (f x) (map f xs)" using A and D by simp+
    ultimately show "f x # map f xs \<cong> {[], f z # map f zs', ?P'}"
     using D by simp
  next
    fix y ys'
    assume "ys = y # ys'" and "zs = []"
    hence D: "P x xs \<and> x = y \<and> xs \<cong> {ys', [], P}" using C by simp+
    moreover have "xs \<cong> {ys', [], P} \<longrightarrow> map f xs \<cong> {map f ys', map f [], ?P'}"
     using B .
    ultimately have "map f xs \<cong> {map f ys', [], ?P'}" by simp
    moreover have "?P' (f x) (map f xs)" using A and D by simp+
    ultimately show "f x # map f xs \<cong> {f y # map f ys', [], ?P'}"
     using D by simp
  next
    fix y ys' z zs'
    assume "ys = y # ys'" and "zs = z # zs'"
    hence D: "x # xs \<cong> {y # ys', z # zs', P}" using C by simp
    show "f x # map f xs \<cong> {f y # map f ys', f z # map f zs', ?P'}"
    proof (cases "P x xs")
      case True
      hence E: "?P' (f x) (map f xs)" using A by simp
      have "x = y \<and> xs \<cong> {ys', z # zs', P}" using D and True by simp
      moreover have "xs \<cong> {ys', z # zs', P} \<longrightarrow>
        map f xs \<cong> {map f ys', map f (z # zs'), ?P'}"
       using B .
      ultimately have "f x = f y \<and> map f xs \<cong> {map f ys', map f (z # zs'), ?P'}"
       by simp
      thus ?thesis using E by simp
    next
      case False
      hence E: "\<not> ?P' (f x) (map f xs)" using A by simp
      have "x = z \<and> xs \<cong> {y # ys', zs', P}" using D and False by simp
      moreover have "xs \<cong> {y # ys', zs', P} \<longrightarrow>
        map f xs \<cong> {map f (y # ys'), map f zs', ?P'}"
       using B .
      ultimately have "f x = f z \<and> map f xs \<cong> {map f (y # ys'), map f zs', ?P'}"
       by simp
      thus ?thesis using E by simp
    qed
  qed
qed

lemma Interleaves_prefix_fst_1 [rule_format]:
  assumes A: "xs \<cong> {ys, zs, P}"
  shows "(\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs)) \<longrightarrow>
    ws @ xs \<cong> {ws @ ys, zs, P}"
proof (induction ws, simp_all add: A, rule impI)
  fix w ws
  assume B: "\<forall>n < Suc (length ws). P ((w # ws) ! n) (drop n ws @ xs)"
  assume "(\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs)) \<longrightarrow>
    ws @ xs \<cong> {ws @ ys, zs, P}"
  moreover have "\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs)"
  proof (rule allI, rule impI)
    fix n
    assume "n < length ws"
    moreover have "Suc n < Suc (length ws) \<longrightarrow>
      P ((w # ws) ! (Suc n)) (drop (Suc n) ws @ xs)"
     using B ..
    ultimately show "P (ws ! n) (drop (Suc n) ws @ xs)" by simp
  qed
  ultimately have "ws @ xs \<cong> {ws @ ys, zs, P}" ..
  moreover have "0 < Suc (length ws) \<longrightarrow> P ((w # ws) ! 0) (drop 0 ws @ xs)"
   using B ..
  hence "P w (ws @ xs)" by simp
  ultimately show "w # ws @ xs \<cong> {w # ws @ ys, zs, P}" by (cases zs, simp_all)
qed

lemma Interleaves_prefix_fst_2 [rule_format]:
 "ws @ xs \<cong> {ws @ ys, zs, P} \<longrightarrow>
  (\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs)) \<longrightarrow>
  xs \<cong> {ys, zs, P}"
proof (induction ws, simp_all, (rule impI)+)
  fix w ws
  assume A: "\<forall>n < Suc (length ws). P ((w # ws) ! n) (drop n ws @ xs)"
  hence "0 < Suc (length ws) \<longrightarrow> P ((w # ws) ! 0) (drop 0 ws @ xs)" ..
  hence "P w (ws @ xs)" by simp
  moreover assume "w # ws @ xs \<cong> {w # ws @ ys, zs, P}"
  ultimately have "ws @ xs \<cong> {ws @ ys, zs, P}" by (cases zs, simp_all)
  moreover assume "ws @ xs \<cong> {ws @ ys, zs, P} \<longrightarrow>
    (\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs)) \<longrightarrow>
    xs \<cong> {ys, zs, P}"
  ultimately have "(\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs)) \<longrightarrow>
    xs \<cong> {ys, zs, P}"
   by simp
  moreover have "\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs)"
  proof (rule allI, rule impI)
    fix n
    assume "n < length ws"
    moreover have "Suc n < Suc (length ws) \<longrightarrow>
      P ((w # ws) ! (Suc n)) (drop (Suc n) ws @ xs)"
     using A ..
    ultimately show "P (ws ! n) (drop (Suc n) ws @ xs)" by simp
  qed
  ultimately show "xs \<cong> {ys, zs, P}" ..
qed

lemma Interleaves_prefix_fst [rule_format]:
 "\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws @ xs) \<Longrightarrow>
  xs \<cong> {ys, zs, P} = ws @ xs \<cong> {ws @ ys, zs, P}"
proof (rule iffI, erule Interleaves_prefix_fst_1, simp)
qed (erule Interleaves_prefix_fst_2, simp)

lemma Interleaves_prefix_snd [rule_format]:
 "\<forall>n < length ws. \<not> P (ws ! n) (drop (Suc n) ws @ xs) \<Longrightarrow>
  xs \<cong> {ys, zs, P} = ws @ xs \<cong> {ys, ws @ zs, P}"
proof (subst (1 2) Interleaves_swap)
qed (rule Interleaves_prefix_fst, simp)

lemma Interleaves_all_nil_1 [rule_format]:
 "xs \<cong> {xs, [], P} \<longrightarrow> (\<forall>n < length xs. P (xs ! n) (drop (Suc n) xs))"
proof (induction xs, simp_all, rule impI, erule conjE, rule allI, rule impI)
  fix x xs n
  assume
    "xs \<cong> {xs, [], P} \<longrightarrow> (\<forall>n < length xs. P (xs ! n) (drop (Suc n) xs))" and
    "xs \<cong> {xs, [], P}"
  hence A: "\<forall>n < length xs. P (xs ! n) (drop (Suc n) xs)" ..
  assume
    B: "P x xs" and
    C: "n < Suc (length xs)"
  show "P ((x # xs) ! n) (drop n xs)"
  proof (cases n, simp_all add: B)
    case (Suc m)
    have "m < length xs \<longrightarrow> P (xs ! m) (drop (Suc m) xs)" using A ..
    moreover have "m < length xs" using C and Suc by simp
    ultimately show "P (xs ! m) (drop (Suc m) xs)" ..
  qed
qed

lemma Interleaves_all_nil_2 [rule_format]:
 "\<forall>n < length xs. P (xs ! n) (drop (Suc n) xs) \<Longrightarrow> xs \<cong> {xs, [], P}"
by (insert Interleaves_prefix_fst [of xs P "[]" "[]" "[]"], simp)

lemma Interleaves_all_nil:
 "xs \<cong> {xs, [], P} = (\<forall>n < length xs. P (xs ! n) (drop (Suc n) xs))"
proof (rule iffI, rule allI, rule impI, rule Interleaves_all_nil_1, assumption+)
qed (rule Interleaves_all_nil_2, simp)

lemma Interleaves_nil_all:
 "xs \<cong> {[], xs, P} = (\<forall>n < length xs. \<not> P (xs ! n) (drop (Suc n) xs))"
by (subst Interleaves_swap, simp add: Interleaves_all_nil)

lemma Interleaves_suffix_one_aux:
  assumes A: "P x []"
  shows "\<not> xs @ [x] \<cong> {[], zs, P}"
proof (induction xs arbitrary: zs, simp_all, rule_tac [!] notI)
  fix zs
  assume "[x] \<cong> {[], zs, P}"
  thus False by (cases zs, simp_all add: A)
next
  fix w xs zs
  assume B: "\<And>zs. \<not> xs @ [x] \<cong> {[], zs, P}"
  assume "w # xs @ [x] \<cong> {[], zs, P}"
  thus False proof (cases zs, simp_all, (erule_tac conjE)+)
    fix zs'
    assume "xs @ [x] \<cong> {[], zs', P}"
    moreover have "\<not> xs @ [x] \<cong> {[], zs', P}" using B .
    ultimately show False by contradiction
  qed
qed

lemma Interleaves_suffix_one_fst_2 [rule_format]:
  assumes A: "P x []"
  shows "xs @ [x] \<cong> {ys @ [x], zs, P} \<longrightarrow> xs \<cong> {ys, zs, \<lambda>w ws. P w (ws @ [x])}"
    (is "_ \<longrightarrow> _ \<cong> {_, _, ?P'}")
proof (induction xs arbitrary: ys zs, rule_tac [!] impI, simp_all)
  fix ys zs
  assume "[x] \<cong> {ys @ [x], zs, P}"
  hence B: "length [x] = length (ys @ [x]) + length zs"
   by (rule Interleaves_length)
  have ys: "ys = []" by (cases ys, simp, insert B, simp)
  then have "zs = []" by (cases zs, simp, insert B, simp)
  with ys show "[] \<cong> {ys, zs, ?P'}" by simp
next
  fix w xs ys zs
  assume B: "\<And>ys zs. xs @ [x] \<cong> {ys @ [x], zs, P} \<longrightarrow> xs \<cong> {ys, zs, ?P'}"
  assume "w # xs @ [x] \<cong> {ys @ [x], zs, P}"
  thus "w # xs \<cong> {ys, zs, ?P'}"
  proof (cases zs, case_tac [!] ys, simp_all del: Interleaves.simps(1,3),
   (erule_tac [1-2] conjE)+)
    assume "xs @ [x] \<cong> {[], [], P}"
    thus False by (cases xs, simp_all)
  next
    fix ys'
    have "xs @ [x] \<cong> {ys' @ [x], [], P} \<longrightarrow> xs \<cong> {ys', [], ?P'}" using B .
    moreover assume "xs @ [x] \<cong> {ys' @ [x], [], P}"
    ultimately show "xs \<cong> {ys', [], ?P'}" ..
  next
    fix z' zs'
    assume "w # xs @ [x] \<cong> {[x], z' # zs', P}"
    thus "w # xs \<cong> {[], z' # zs', ?P'}"
    proof (cases "P w (xs @ [x])", simp_all, erule_tac [!] conjE)
      assume "xs @ [x] \<cong> {[], z' # zs', P}"
      moreover have "\<not> xs @ [x] \<cong> {[], z' # zs', P}"
       using A by (rule Interleaves_suffix_one_aux)
      ultimately show False by contradiction
    next
      have "xs @ [x] \<cong> {[x], zs', P} \<longrightarrow> xs \<cong> {[], zs', ?P'}" using B by simp
      moreover assume "xs @ [x] \<cong> {[x], zs', P}"
      ultimately show "xs \<cong> {[], zs', ?P'}" ..
    qed
  next
    fix y' ys' z' zs'
    assume "w # xs @ [x] \<cong> {y' # ys' @ [x], z' # zs', P}"
    thus "w # xs \<cong> {y' # ys', z' # zs', ?P'}"
    proof (cases "P w (xs @ [x])", simp_all, erule_tac [!] conjE)
      have "xs @ [x] \<cong> {ys' @ [x], z' # zs', P} \<longrightarrow> xs \<cong> {ys', z' # zs', ?P'}"
       using B .
      moreover assume "xs @ [x] \<cong> {ys' @ [x], z' # zs', P}"
      ultimately show "xs \<cong> {ys', z' # zs', ?P'}" ..
    next
      have "xs @ [x] \<cong> {y' # ys' @ [x], zs', P} \<longrightarrow> xs \<cong> {y' # ys', zs', ?P'}"
       using B by simp
      moreover assume "xs @ [x] \<cong> {y' # ys' @ [x], zs', P}"
      ultimately show "xs \<cong> {y' # ys', zs', ?P'}" ..
    qed
  qed
qed

lemma Interleaves_suffix_fst_1 [rule_format]:
  assumes A: "\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws)"
  shows "xs \<cong> {ys, zs, \<lambda>v vs. P v (vs @ ws)} \<longrightarrow> xs @ ws \<cong> {ys @ ws, zs, P}"
    (is "_ \<cong> {_, _, ?P'} \<longrightarrow> _")
proof (induction xs arbitrary: ys zs, rule_tac [!] impI, simp_all)
  fix ys zs
  assume "[] \<cong> {ys, zs, ?P'}"
  hence "ys = [] \<and> zs = []" by (rule Interleaves_nil)
  thus "ws \<cong> {ys @ ws, zs, P}" using A by (simp add: Interleaves_all_nil)
next
  fix x xs ys zs
  assume A: "\<And>ys zs. xs \<cong> {ys, zs, ?P'} \<longrightarrow> xs @ ws \<cong> {ys @ ws, zs, P}"
  assume "x # xs \<cong> {ys, zs, ?P'}"
  thus "x # xs @ ws \<cong> {ys @ ws, zs, P}"
  proof (rule_tac Interleaves.cases [of "(?P', x # xs, ys, zs)"],
   simp_all del: Interleaves.simps(1),
   (erule_tac conjE)+, (erule_tac [2] conjE)+, (erule_tac [3] conjE)+)
    fix P' x' xs' y' ys' z' zs'
    assume
      B: "x' # xs' \<cong> {y' # ys', z' # zs', P'}" and
      C: "?P' = P'" and
      D: "xs = xs'"
    show "x' # xs' @ ws \<cong> {y' # ys' @ ws, z' # zs', P}"
    proof (cases "P' x' xs'")
      have "xs \<cong> {ys', z' # zs', ?P'} \<longrightarrow> xs @ ws \<cong> {ys' @ ws, z' # zs', P}"
       using A .
      moreover case True
      hence "xs \<cong> {ys', z' # zs', ?P'}" using B and C and D by simp
      ultimately have "xs @ ws \<cong> {ys' @ ws, z' # zs', P}" ..
      moreover have "P x' (xs' @ ws)" using C [symmetric] and True by simp
      moreover have "x' = y'" using B and True by simp
      ultimately show ?thesis using D by simp
    next
      have "xs \<cong> {y' # ys', zs', ?P'} \<longrightarrow> xs @ ws \<cong> {(y' # ys') @ ws, zs', P}"
       using A .
      moreover case False
      hence "xs \<cong> {y' # ys', zs', ?P'}" using B and C and D by simp
      ultimately have "xs @ ws \<cong> {(y' # ys') @ ws, zs', P}" ..
      moreover have "\<not> P x' (xs' @ ws)" using C [symmetric] and False by simp
      moreover have "x' = z'" using B and False by simp
      ultimately show ?thesis using D by simp
    qed
  next
    fix P' x' xs' y' ys'
    have "xs \<cong> {ys', [], ?P'} \<longrightarrow> xs @ ws \<cong> {ys' @ ws, [], P}" using A .
    moreover assume
      "xs' \<cong> {ys', [], P'}" and
      B: "?P' = P'" and
      C: "xs = xs'"
    hence "xs \<cong> {ys', [], ?P'}" by simp
    ultimately have "xs' @ ws \<cong> {ys' @ ws, [], P}" using C by simp
    moreover assume
      "P' x' xs'" and
      "x' = y'"
    hence "P y' (xs' @ ws)" using B [symmetric] by simp
    ultimately show "P y' (xs' @ ws) \<and> xs' @ ws \<cong> {ys' @ ws, [], P}" by simp
  next
    fix P' x' xs' z' zs'
    have "xs \<cong> {[], zs', ?P'} \<longrightarrow> xs @ ws \<cong> {[] @ ws, zs', P}" using A .
    moreover assume
      "xs' \<cong> {[], zs', P'}" and
      B: "?P' = P'" and
      C: "xs = xs'"
    hence "xs \<cong> {[], zs', ?P'}" by simp
    ultimately have "xs' @ ws \<cong> {ws, zs', P}" using C by simp
    moreover assume
      "\<not> P' x' xs'" and
      "x' = z'"
    hence "\<not> P z' (xs' @ ws)" using B [symmetric] by simp
    ultimately show "z' # xs' @ ws \<cong> {ws, z' # zs', P}" by (cases ws, simp_all)
  qed
qed

lemma Interleaves_suffix_one_fst_1 [rule_format]:
 "P x [] \<Longrightarrow>
  xs \<cong> {ys, zs, \<lambda>w ws. P w (ws @ [x])} \<Longrightarrow> xs @ [x] \<cong> {ys @ [x], zs, P}"
by (rule Interleaves_suffix_fst_1, simp)

lemma Interleaves_suffix_one_fst:
 "P x [] \<Longrightarrow>
  xs \<cong> {ys, zs, \<lambda>w ws. P w (ws @ [x])} = xs @ [x] \<cong> {ys @ [x], zs, P}"
proof (rule iffI, rule Interleaves_suffix_one_fst_1, assumption+)
qed (rule Interleaves_suffix_one_fst_2)

lemma Interleaves_suffix_one_snd:
 "\<not> P x [] \<Longrightarrow>
  xs \<cong> {ys, zs, \<lambda>w ws. P w (ws @ [x])} = xs @ [x] \<cong> {ys, zs @ [x], P}"
by (subst (1 2) Interleaves_swap, rule Interleaves_suffix_one_fst)

lemma Interleaves_suffix_aux [rule_format]:
 "(\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws)) \<longrightarrow>
  x # xs @ ws \<cong> {ws, zs, P} \<longrightarrow>
  \<not> P x (xs @ ws)"
proof (induction ws arbitrary: P rule: rev_induct, simp_all,
 rule impI, (rule_tac [2] impI)+)
  fix P
  assume "x # xs \<cong> {[], zs, P}"
  thus "\<not> P x xs" by (cases zs, simp_all)
next
  fix w ws P
  assume
    A: "\<And>P'. (\<forall>n < length ws. P' (ws ! n) (drop (Suc n) ws)) \<longrightarrow>
      x # xs @ ws \<cong> {ws, zs, P'} \<longrightarrow> \<not> P' x (xs @ ws)" and
    B: "\<forall>n < Suc (length ws). P ((ws @ [w]) ! n)
      (drop (Suc n) ws @ drop (Suc n - length ws) [w])"
  assume "x # xs @ ws @ [w] \<cong> {ws @ [w], zs, P}"
  hence C: "(x # xs @ ws) @ [w] \<cong> {ws @ [w], zs, P}" by simp
  let ?P' = "\<lambda>v vs. P v (vs @ [w])"
  have "(\<forall>n < length ws. ?P' (ws ! n) (drop (Suc n) ws)) \<longrightarrow>
    x # xs @ ws \<cong> {ws, zs, ?P'} \<longrightarrow> \<not> ?P' x (xs @ ws)"
   using A .
  moreover have "\<forall>n < length ws. ?P' (ws ! n) (drop (Suc n) ws)"
  proof (rule allI, rule impI)
    fix n
    assume D: "n < length ws"
    moreover have "n < Suc (length ws) \<longrightarrow> P ((ws @ [w]) ! n)
      (drop (Suc n) ws @ drop (Suc n - length ws) [w])"
     using B ..
    ultimately have "P ((ws @ [w]) ! n) (drop (Suc n) ws @ [w])" by simp
    moreover have "n < length (butlast (ws @ [w]))" using D by simp
    hence "butlast (ws @ [w]) ! n = (ws @ [w]) ! n" by (rule nth_butlast)
    ultimately show "P (ws ! n) (drop (Suc n) ws @ [w])" by simp
  qed
  ultimately have "x # xs @ ws \<cong> {ws, zs, ?P'} \<longrightarrow> \<not> ?P' x (xs @ ws)" ..
  moreover have "length ws < Suc (length ws) \<longrightarrow> P ((ws @ [w]) ! length ws)
    (drop (Suc (length ws)) ws @ drop (Suc (length ws) - length ws) [w])"
   using B ..
  hence "P w []" by simp
  hence "x # xs @ ws \<cong> {ws, zs, ?P'}"
   using C by (rule Interleaves_suffix_one_fst_2)
  ultimately have "\<not> ?P' x (xs @ ws)" ..
  thus "\<not> P x (xs @ ws @ [w])" by simp
qed

lemma Interleaves_suffix_fst_2 [rule_format]:
  assumes A: "\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws)"
  shows "xs @ ws \<cong> {ys @ ws, zs, P} \<longrightarrow> xs \<cong> {ys, zs, \<lambda>v vs. P v (vs @ ws)}"
    (is "_ \<longrightarrow> _ \<cong> {_, _, ?P'}")
proof (induction xs arbitrary: ys zs, rule_tac [!] impI, simp_all)
  fix ys zs
  assume "ws \<cong> {ys @ ws, zs, P}"
  hence B: "length ws = length (ys @ ws) + length zs"
   by (rule Interleaves_length)
  have ys: "ys = []" by (cases ys, simp, insert B, simp)
  then have "zs = []" by (cases zs, simp, insert B, simp)
  with ys show "[] \<cong> {ys, zs, ?P'}" by simp
next
  fix x xs ys zs
  assume B: "\<And>ys zs. xs @ ws \<cong> {ys @ ws, zs, P} \<longrightarrow> xs \<cong> {ys, zs, ?P'}"
  assume "x # xs @ ws \<cong> {ys @ ws, zs, P}"
  thus "x # xs \<cong> {ys, zs, ?P'}"
  proof (cases zs, case_tac [!] ys, simp_all del: Interleaves.simps(1,3),
   (erule_tac [2] conjE)+)
    assume C: "x # xs @ ws \<cong> {ws, [], P}"
    have "length (x # xs @ ws) = length ws + length []"
     by (insert Interleaves_length [OF C], simp)
    thus False by simp
  next
    fix ys'
    have "xs @ ws \<cong> {ys' @ ws, [], P} \<longrightarrow> xs \<cong> {ys', [], ?P'}" using B .
    moreover assume "xs @ ws \<cong> {ys' @ ws, [], P}"
    ultimately show "xs \<cong> {ys', [], ?P'}" ..
  next
    fix z' zs'
    assume "x # xs @ ws \<cong> {ws, z' # zs', P}"
    thus "x # xs \<cong> {[], z' # zs', ?P'}"
    proof (cases "P x (xs @ ws)", simp_all)
      case True
      moreover assume "x # xs @ ws \<cong> {ws, z' # zs', P}"
      with A [rule_format] have "\<not> P x (xs @ ws)"
       by (rule Interleaves_suffix_aux)
      ultimately show False by contradiction
    next
      case False
      moreover assume "x # xs @ ws \<cong> {ws, z' # zs', P}"
      ultimately have "x = z' \<and> xs @ ws \<cong> {ws, zs', P}" by (cases ws, simp_all)
      moreover have "xs @ ws \<cong> {[] @ ws, zs', P} \<longrightarrow> xs \<cong> {[], zs', ?P'}"
       using B .
      ultimately show "x = z' \<and> xs \<cong> {[], zs', ?P'}" by simp
    qed
  next
    fix y' ys' z' zs'
    assume "x # xs @ ws \<cong> {y' # ys' @ ws, z' # zs', P}"
    thus "x # xs \<cong> {y' # ys', z' # zs', ?P'}"
    proof (cases "P x (xs @ ws)", simp_all, erule_tac [!] conjE)
      have "xs @ ws \<cong> {ys' @ ws, z' # zs', P} \<longrightarrow> xs \<cong> {ys', z' # zs', ?P'}"
       using B .
      moreover assume "xs @ ws \<cong> {ys' @ ws, z' # zs', P}"
      ultimately show "xs \<cong> {ys', z' # zs', ?P'}" ..
    next
      have "xs @ ws \<cong> {y' # ys' @ ws, zs', P} \<longrightarrow> xs \<cong> {y' # ys', zs', ?P'}"
       using B by simp
      moreover assume "xs @ ws \<cong> {y' # ys' @ ws, zs', P}"
      ultimately show "xs \<cong> {y' # ys', zs', ?P'}" ..
    qed
  qed
qed

lemma Interleaves_suffix_fst [rule_format]:
 "\<forall>n < length ws. P (ws ! n) (drop (Suc n) ws) \<Longrightarrow>
  xs \<cong> {ys, zs, \<lambda>v vs. P v (vs @ ws)} = xs @ ws \<cong> {ys @ ws, zs, P}"
proof (rule iffI, rule Interleaves_suffix_fst_1, simp_all)
qed (rule Interleaves_suffix_fst_2, simp)

lemma Interleaves_suffix_snd [rule_format]:
 "\<forall>n < length ws. \<not> P (ws ! n) (drop (Suc n) ws) \<Longrightarrow>
  xs \<cong> {ys, zs, \<lambda>v vs. P v (vs @ ws)} = xs @ ws \<cong> {ys, zs @ ws, P}"
by (subst (1 2) Interleaves_swap, rule Interleaves_suffix_fst, simp)

end
