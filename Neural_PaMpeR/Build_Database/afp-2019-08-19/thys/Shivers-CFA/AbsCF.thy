section "Abstract nonstandard semantics"

theory AbsCF
  imports HOLCF HOLCFUtils CPSScheme Utils SetMap
begin

default_sort type

text \<open>
After having defined the exact meaning of a control graph, we now alter the algorithm into a statically computable. We note that the contour pointer in the exact semantics is taken from an infinite set. This is unavoidable, as recursion depth is unbounded. But if this were not the case and the set were finite, the function would be calculable, having finite range and domain.

Therefore, we make the set of contour counter values finite and accept that this makes our result less exact, but calculable. We also do not work with values any more but only remember, for each variable, what possible lambdas can occur there. Because we do not have exact values any more, in a conditional expression, both branches are taken.

We want to leave the exact choice of the finite contour set open for now. Therefore, we define a type class capturing the relevant definitions and the fact that the set is finite. Isabelle expects type classes to be non-empty, so we show that the \<open>unit\<close> type is in this type class.
\<close>

class contour = finite +
  fixes nb_a :: "'a \<Rightarrow> label \<Rightarrow> 'a" ("\<anb>")
    and a_initial_contour :: 'a ("\<abinit>")

instantiation unit :: contour
begin
definition "\<anb> _ _ = ()"
definition "\<abinit> = ()"
instance by standard auto
end

text \<open>
Analogous to the previous section, we define types for binding environments, closures, procedures, semantic values (which are now sets of possible procedures) and variable environment. Their types are parametrized by the chosen set of abstract contours.

The abstract variable environment is a partial map to sets in Shivers' dissertation. As he does not need to distinguish between a key not in the map and a key mapped to the empty set, this presentation is redundant. Therefore, I encoded this as a function from keys to sets of values. The theory @{theory "Shivers-CFA.SetMap"} contains functions and lemmas to work with such maps, symbolized by an appended dot (e.g. \<open>{}.\<close>, \<open>\<union>.\<close>).
\<close>

type_synonym 'c a_benv = "label \<rightharpoonup> 'c" ("_ \<abenv>" [1000])
type_synonym 'c a_closure = "lambda \<times> 'c \<abenv>" ("_ \<aclosure>" [1000])

datatype 'c proc ("_ \<aproc>" [1000])
  = PC "'c \<aclosure>"
  | PP prim
  | AStop

type_synonym 'c a_d = "'c \<aproc> set" ("_ \<ad>" [1000])

type_synonym 'c a_venv = "var \<times> 'c \<Rightarrow> 'c \<ad>" ("_ \<avenv>" [1000])

text \<open>
The evaluation function now ignores constants and returns singletons for primitive operations and lambda expressions.
\<close>

fun evalV_a :: "val \<Rightarrow> 'c \<abenv> \<Rightarrow> 'c \<avenv> \<Rightarrow> 'c \<ad>" ("\<aA>")
  where "\<aA> (C _ i) \<beta> ve = {}"
  |     "\<aA> (P prim) \<beta> ve = {PP prim}"
  |     "\<aA> (R _ var) \<beta> ve =
           (case \<beta> (binder var) of
              Some l \<Rightarrow> ve (var,l)
            | None \<Rightarrow> {})"
  |     "\<aA> (L lam) \<beta> ve = {PC (lam, \<beta>)}"

text \<open>
The types of the calculated graph, the arguments to \<open>\<aF>\<close> and \<open>\<aC>\<close> resemble closely the types in the exact case, with each type replaced by its abstract counterpart.
\<close>

type_synonym 'c a_ccache = "((label \<times> 'c \<abenv>) \<times> 'c \<aproc>) set" ("_ \<accache>" [1000])
type_synonym 'c a_ans = "'c \<accache>" ("_ \<aans>" [1000])

type_synonym 'c a_fstate = "('c \<aproc> \<times> 'c \<ad> list \<times> 'c \<avenv> \<times> 'c)" ("_ \<afstate>" [1000])
type_synonym 'c a_cstate = "(call \<times> 'c \<abenv> \<times> 'c \<avenv> \<times> 'c)" ("_ \<acstate>" [1000])

text \<open>
And yet again, cont2cont results need to be shown for our custom data types.
\<close>

lemma cont2cont_case_lambda [simp, cont2cont]:
  assumes "\<And>a b c. cont (\<lambda>x. f x a b c)"
  shows "cont (\<lambda>x. case_lambda (f x) l)"
using assms
by (cases l) auto

lemma cont2cont_case_proc [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. f1 x y)"
     and  "\<And>y. cont (\<lambda>x. f2 x y)"
     and  "cont (\<lambda>x. f3 x)"
  shows "cont (\<lambda>x. case_proc (f1 x) (f2 x) (f3 x) d)"
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
We can now define the abstract nonstandard semantics, based on the equations in Figure 4.5 and 4.6 of Shivers' dissertation. In the \<open>AStop\<close> case, \<open>{}\<close> is returned, while for wrong arguments, \<open>\<bottom>\<close> is returned. Both actually represent the same value, the empty set, so this is just a aesthetic difference.
\<close>

fixrec   a_evalF :: "'c::contour \<afstate> discr \<rightarrow> 'c \<aans>" ("\<aF>")
     and a_evalC :: "'c::contour \<acstate> discr \<rightarrow> 'c \<aans>" ("\<aC>")
  where "\<aF>\<cdot>fstate = (case undiscr fstate of
             (PC (Lambda lab vs c, \<beta>), as, ve, b) \<Rightarrow>
               (if length vs = length as
                then let \<beta>' = \<beta> (lab \<mapsto> b);
                         ve' = ve \<union>. (\<Union>. (map (\<lambda>(v,a). {(v,b) := a}.) (zip vs as)))
                     in \<aC>\<cdot>(Discr (c,\<beta>',ve',b))
                else \<bottom>)
            | (PP (Plus c),[_,_,cnts],ve,b) \<Rightarrow>
                     let b' = \<anb> b c;
                         \<beta>  = [c \<mapsto> b]
                     in (\<Union>cnt\<in>cnts. \<aF>\<cdot>(Discr (cnt,[{}],ve,b')))
                        \<union>
                        {((c, \<beta>), cont) | cont . cont \<in> cnts}
            | (PP (prim.If ct cf),[_, cntts, cntfs],ve,b) \<Rightarrow>
                  ((   let b' = \<anb> b ct;
                            \<beta> = [ct \<mapsto> b]
                        in (\<Union>cnt\<in>cntts . \<aF>\<cdot>(Discr (cnt,[],ve,b')))
                           \<union>{((ct, \<beta>), cnt) | cnt . cnt \<in> cntts}
                   )\<union>(
                       let b' = \<anb> b cf;
                            \<beta> = [cf \<mapsto> b]
                        in (\<Union>cnt\<in>cntfs . \<aF>\<cdot>(Discr (cnt,[],ve,b')))
                           \<union>{((cf, \<beta>), cnt) | cnt . cnt \<in> cntfs}
                   ))
            | (AStop,[_],_,_) \<Rightarrow> {}
            | _ \<Rightarrow> \<bottom>
        )"
      | "\<aC>\<cdot>cstate = (case undiscr cstate of
             (App lab f vs,\<beta>,ve,b) \<Rightarrow>
                 let fs = \<aA> f \<beta> ve;
                     as = map (\<lambda>v. \<aA> v \<beta> ve) vs;
                     b' = \<anb> b lab
                  in (\<Union>f' \<in> fs. \<aF>\<cdot>(Discr (f',as,ve,b')))
                     \<union>{((lab, \<beta>),f') | f' . f'\<in> fs}
            | (Let lab ls c',\<beta>,ve,b) \<Rightarrow>
                 let b' = \<anb> b lab;
                     \<beta>' = \<beta> (lab \<mapsto> b');
                     ve' = ve \<union>. (\<Union>. (map (\<lambda>(v,l). {(v,b') := (\<aA> (L l) \<beta>' ve)}.) ls))
                 in \<aC>\<cdot>(Discr (c',\<beta>',ve',b'))
        )"

text \<open>
Again, we name the cases of the induction rule and build a nicer case analysis rule for arguments of type \<open>\<afstate>\<close>.
\<close>

lemmas a_evalF_evalC_induct = a_evalF_a_evalC.induct[case_names Admissibility Bottom Next]

fun a_evalF_cases
 where "a_evalF_cases (PC (Lambda lab vs c, \<beta>)) as ve b = undefined"
     | "a_evalF_cases (PP (Plus cp)) [a1, a2, cnt] ve b = undefined"
     | "a_evalF_cases (PP (prim.If cp1 cp2)) [v,cntt,cntf] ve b = undefined"
     | "a_evalF_cases AStop [v] ve b = undefined"

lemmas a_fstate_case_x = a_evalF_cases.cases[
  OF case_split, of _ "\<lambda>_ vs _ _ as _ _ . length vs = length as",
  case_names "Closure" "Closure_inv" "Plus" "If" "Stop"]

lemmas a_cl_cases = prod.exhaust[OF lambda.exhaust, of _ "\<lambda> a _ . a"]
lemmas a_ds_cases = list.exhaust[
  OF _ list.exhaust,  of _ _ "\<lambda>_ x. x",
  OF _ _ list.exhaust  ,of _ _ "\<lambda>_ _ _ x. x" , 
  OF _ _ _ list.exhaust,of _ _ "\<lambda>_ _ _ _ _ x. x"
  ] 
lemmas a_ds_cases_stop = list.exhaust[OF _ list.exhaust, of _ _ "\<lambda>_ x. x"]
lemmas a_fstate_case = prod_cases4[OF proc.exhaust, of _ "\<lambda>x _ _ _ . x",
  OF a_cl_cases prim.exhaust, of _ "\<lambda> _ _ _ _ a . a" _ "\<lambda> _ _ _ _ a. a",
  OF case_split a_ds_cases a_ds_cases a_ds_cases_stop,
  of _ "\<lambda>_ as _ _ _ _ _ _ vs _ . length vs = length as" _ "\<lambda> _ ds _ _ _ _ . ds" "\<lambda> _ ds _ _ _ _ _. ds" "\<lambda> _ ds _ _. ds"]

text \<open>
Not surprisingly, the abstract semantics of a whole program is defined using \<open>\<aF>\<close> with suitably initialized arguments. The function \<open>the_elem\<close> extracts a value from a singleton set. This works because we know that \<open>\<aA>\<close> returns such a set when given a lambda expression.
\<close>

definition evalCPS_a :: "prog \<Rightarrow> ('c::contour) \<aans>" ("\<aPR>")
  where "\<aPR> l = (let ve = {}.;
                          \<beta> = Map.empty;
                          f = \<aA> (L l) \<beta> ve
                      in  \<aF>\<cdot>(Discr (the_elem f,[{AStop}],ve,\<abinit>)))"

end
