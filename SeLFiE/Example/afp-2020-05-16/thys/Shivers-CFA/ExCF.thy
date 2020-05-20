section "Exact nonstandard semantics"

theory ExCF
  imports HOLCF HOLCFUtils CPSScheme Utils
begin

text \<open>
We now alter the standard semantics given in the previous section to calculate a control flow graph instead of the return value. At this point, we still ``run'' the program in full, so this is not yet the static analysis that we aim for. Instead, this is the reference for the correctness proof of the static analysis: If an edge is recorded here, we expect it to be found by the static analysis as well.
\<close>

text \<open>
In preparation of the correctness proof we change the type of the contour counters. Instead of plain natural numbers as in the previous sections we use lists of labels, remembering at each step which part of the program was just evaluated.

Note that for the exact semantics, this is information is not used in any way and it would have been possible to just use natural numbers again. This is reflected by the preorder instance for the contours which only look at the length of the list, but not the entries.
\<close>

definition "contour = (UNIV::label list set)"

typedef contour = contour
  unfolding contour_def by auto

definition initial_contour ("\<binit>")
  where "\<binit> = Abs_contour []"

definition nb 
  where "nb b c = Abs_contour (c # Rep_contour b)"

instantiation contour :: preorder
begin
definition le_contour_def: "b \<le> b' \<longleftrightarrow> length (Rep_contour b) \<le> length (Rep_contour b')"
definition less_contour_def: "b < b' \<longleftrightarrow> length (Rep_contour b) < length (Rep_contour b')"
instance proof
qed(auto simp add:le_contour_def less_contour_def Rep_contour_inverse Abs_contour_inverse contour_def)
end

text \<open>
Three simple lemmas helping Isabelle to automatically prove statements about contour numbers.
\<close>

lemma nb_le_less[iff]: "nb b c \<le> b' \<longleftrightarrow> b < b'"
  unfolding nb_def
  by (auto simp add:le_contour_def less_contour_def Rep_contour_inverse Abs_contour_inverse contour_def)

lemma nb_less[iff]: "b' < nb b c \<longleftrightarrow> b' \<le> b"
  unfolding nb_def
  by (auto simp add:le_contour_def less_contour_def Rep_contour_inverse Abs_contour_inverse contour_def)

declare less_imp_le[where 'a = contour, intro]


text \<open>
The other types used in our semantics functions have not changed.
\<close>

type_synonym benv = "label \<rightharpoonup> contour"
type_synonym closure = "lambda \<times> benv"

datatype d = DI int
           | DC closure
           | DP prim
           | Stop

type_synonym venv = "var \<times> contour \<rightharpoonup> d"

text \<open>
As we do not use the type system to distinguish procedural from non-procedural values, we define a predicate for that.
\<close>

primrec isProc 
  where "isProc (DI _) = False"
      | "isProc (DC _) = True"
      | "isProc (DP _) = True"
      | "isProc Stop   = True"

text \<open>
To please @{theory HOLCF}, we declare the discrete partial order for our types:
\<close>

instantiation contour :: discrete_cpo
begin
definition [simp]: "(x::contour) \<sqsubseteq> y \<longleftrightarrow> x = y"
instance by standard simp
end
instantiation d :: discrete_cpo begin
definition  [simp]: "(x::d) \<sqsubseteq> y \<longleftrightarrow> x = y"
instance by standard simp
end

instantiation call :: discrete_cpo begin
definition  [simp]: "(x::call) \<sqsubseteq> y \<longleftrightarrow> x = y"
instance by standard simp
end

text \<open>
The evaluation function for values has only changed slightly: To avoid worrying about incorrect programs, we return zero when a variable lookup fails. If the labels in the program given are correct, this will not happen. Shivers makes this explicit in Section 4.1.3 by restricting the function domains to the valid programs. This is omitted here.
\<close>


fun evalV :: "val \<Rightarrow> benv \<Rightarrow> venv \<Rightarrow> d" ("\<A>")
  where "\<A> (C _ i) \<beta> ve = DI i"
  |     "\<A> (P prim) \<beta> ve = DP prim"
  |     "\<A> (R _ var) \<beta> ve =
           (case \<beta> (binder var) of
              Some l \<Rightarrow> (case ve (var,l) of Some d \<Rightarrow> d | None \<Rightarrow> DI 0)
             | None \<Rightarrow> DI 0)"
  |     "\<A> (L lam) \<beta> ve = DC (lam, \<beta>)"


text \<open>
To be able to do case analysis on the custom datatypes \<open>lambda\<close>, \<open>d\<close>, \<open>call\<close> and \<open>prim\<close> inside a function defined with \<open>fixrec\<close>, we need continuity results for them. These are all of the same shape and proven by case analysis on the discriminator.
\<close>

lemma cont2cont_case_lambda [simp, cont2cont]:
  assumes "\<And>a b c. cont (\<lambda>x. f x a b c)"
  shows "cont (\<lambda>x. case_lambda (f x) l)"
using assms
by (cases l) auto

lemma cont2cont_case_d [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. f1 x y)"
     and  "\<And>y. cont (\<lambda>x. f2 x y)"
     and  "\<And>y. cont (\<lambda>x. f3 x y)"
    and   "cont (\<lambda>x. f4 x)"
  shows "cont (\<lambda>x. case_d (f1 x) (f2 x) (f3 x) (f4 x) d)"
using assms
by (cases d) auto

lemma cont2cont_case_call [simp, cont2cont]:
  assumes "\<And>a b c. cont (\<lambda>x. f1 x a b c)"
     and  "\<And>a b c. cont (\<lambda>x. f2 x a b c)"
  shows "cont (\<lambda>x. case_call (f1 x) (f2 x) c)"
using assms
by (cases c) auto

lemma cont2cont_case_prim [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. f1 x y)"
     and  "\<And>y z. cont (\<lambda>x. f2 x y z)"
  shows "cont (\<lambda>x. case_prim (f1 x) (f2 x) p)"
using assms
by (cases p) auto

text \<open>
Now, our answer domain is not any more the integers, but rather call caches. These are represented as sets containing tuples of call sites (given by their label) and binding environments to the called value. The argument types are unaltered.

In the functions \<open>\<F>\<close> and \<open>\<C>\<close>, upon every call, a new element is added to the resulting set. The \<open>STOP\<close> continuation now ignores its argument and retuns the empty set instead. This corresponds to Figure 4.2 and 4.3 in Shivers' dissertation.
\<close>

type_synonym ccache = "((label \<times> benv) \<times> d) set"
type_synonym ans = ccache

type_synonym fstate = "(d \<times> d list \<times> venv \<times> contour)"
type_synonym cstate = "(call \<times> benv \<times> venv \<times> contour)"


fixrec   evalF :: "fstate discr \<rightarrow> ans" ("\<F>")
     and evalC :: "cstate discr \<rightarrow> ans" ("\<C>")
  where "\<F>\<cdot>fstate = (case undiscr fstate of
             (DC (Lambda lab vs c, \<beta>), as, ve, b) \<Rightarrow>
               (if length vs = length as
                then let \<beta>' = \<beta> (lab \<mapsto> b);
                         ve' = map_upds ve (map (\<lambda>v.(v,b)) vs) as
                     in \<C>\<cdot>(Discr (c,\<beta>',ve',b))
                else \<bottom>)
            | (DP (Plus c),[DI a1, DI a2, cnt],ve,b) \<Rightarrow>
                (if isProc cnt
                 then let b' = nb b c;
                          \<beta>  = [c \<mapsto> b]
                      in \<F>\<cdot>(Discr (cnt,[DI (a1 + a2)],ve,b'))
                        \<union> {((c, \<beta>),cnt)}
                 else \<bottom>)
            | (DP (prim.If ct cf),[DI v, contt, contf],ve,b) \<Rightarrow>
                (if isProc contt \<and> isProc contf
                 then
                  (if v \<noteq> 0
                   then let b' = nb b ct;
                            \<beta> = [ct \<mapsto> b]
                        in (\<F>\<cdot>(Discr (contt,[],ve,b'))
                            \<union> {((ct, \<beta>),contt)})
                   else let b' = nb b cf;
                            \<beta> = [cf \<mapsto> b]
                        in (\<F>\<cdot>(Discr (contf,[],ve,b')))
                            \<union> {((cf, \<beta>),contf)})
                 else \<bottom>)
            | (Stop,[DI i],_,_) \<Rightarrow> {}
            | _ \<Rightarrow> \<bottom>
        )"
      | "\<C>\<cdot>cstate = (case undiscr cstate of
             (App lab f vs,\<beta>,ve,b) \<Rightarrow>
                 let f' = \<A> f \<beta> ve;
                     as = map (\<lambda>v. \<A> v \<beta> ve) vs;
                     b' = nb b lab
                  in if isProc f'
                     then \<F>\<cdot>(Discr (f',as,ve,b')) \<union> {((lab, \<beta>),f')}
                     else \<bottom>
            | (Let lab ls c',\<beta>,ve,b) \<Rightarrow>
                 let b' = nb b lab;
                     \<beta>' = \<beta> (lab \<mapsto> b');
                    ve' = ve ++ map_of (map (\<lambda>(v,l). ((v,b'), \<A> (L l) \<beta>' ve)) ls)
                 in \<C>\<cdot>(Discr (c',\<beta>',ve',b'))
        )"

text \<open>
In preparation of later proofs, we give the cases of the generated induction rule names and also create a large rule to deconstruct the an value of type \<open>fstate\<close> into the various cases that were used in the definition of \<open>\<F>\<close>.
\<close>

lemmas evalF_evalC_induct = evalF_evalC.induct[case_names Admissibility Bottom Next]

lemmas cl_cases = prod.exhaust[OF lambda.exhaust, of _ "\<lambda> a _ . a"]
lemmas ds_cases_plus = list.exhaust[
  OF _ d.exhaust, of _ _ "\<lambda>a _. a",
  OF _ list.exhaust, of _ _ "\<lambda>_ x _. x",
  OF _ _ d.exhaust, of _ _ "\<lambda>_ _ _ a _. a",
  OF _ _ list.exhaust,of _ _ "\<lambda>_ _ _ _ x _. x",
  OF _ _ _ list.exhaust,of _ _ "\<lambda>_ _ _ _ _ _ _ x. x"
  ]
lemmas ds_cases_if = list.exhaust[OF _ d.exhaust, of _ _ "\<lambda>a _. a",
  OF _ list.exhaust[OF _ list.exhaust[OF _ list.exhaust, of _ _ "\<lambda>_ x. x"], of _ _ "\<lambda>_ x. x"], of _ _ "\<lambda>_ x _. x"]
lemmas ds_cases_stop = list.exhaust[OF _ d.exhaust, of _ _ "\<lambda>a _. a",
  OF _ list.exhaust, of _ _ "\<lambda>_ x _. x"]
lemmas fstate_case = prod_cases4[OF d.exhaust, of _ "\<lambda>x _ _ _ . x",
  OF _ cl_cases prim.exhaust, of _ _ "\<lambda> _ _ _ _ a . a" "\<lambda> _ _ _ _ a. a",
  OF _ case_split ds_cases_plus ds_cases_if ds_cases_stop,
  of _ _ "\<lambda>_ as _ _ _ _ _ _ vs _ . length vs = length as" "\<lambda> _ ds _ _ _ _ . ds" "\<lambda> _ ds _ _ _ _ _. ds" "\<lambda> _ ds _ _. ds",
  case_names "x" "Closure" "x" "x"  "x" "x" "Plus" "x" "x" "x" "x" "x" "x" "x" "x"   "x" "x" "If_True" "If_False" "x" "x" "x" "x" "x" "Stop"  "x" "x" "x" "x" "x"]


text \<open>
The exact semantics of a program again uses \<open>\<F>\<close> with properly initialized arguments. For the first two examples, we see that the function works as expected.
\<close>

definition evalCPS :: "prog \<Rightarrow> ans" ("\<PR>")
  where "\<PR> l = (let ve = Map.empty;
                          \<beta> = Map.empty;
                          f = \<A> (L l) \<beta> ve
                      in  \<F>\<cdot>(Discr (f,[Stop],ve,\<binit>)))"

lemma correct_ex1: "\<PR> ex1 = {((2,[1 \<mapsto> \<binit>]), Stop)}"
unfolding evalCPS_def
by simp

lemma correct_ex2: "\<PR> ex2 = {((2, [1 \<mapsto> \<binit>]), DP (Plus 3)),
                                   ((3, [3 \<mapsto> nb \<binit> 2]),  Stop)}"
unfolding evalCPS_def
by simp


end
