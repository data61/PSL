section "Standard semantics"

theory Eval
  imports HOLCF HOLCFUtils CPSScheme
begin

text \<open>
We begin by giving the standard semantics for our language. Although this is not actually used to show any results, it is helpful to see that the later algorithms ``look similar'' to the evaluation code and the relation between calls done during evaluation and calls recorded by the control flow graph.
\<close>

text \<open>
We follow the definition in Figure 3.1 and 3.2 of Shivers' dissertation, with the clarifications from Section 4.1. As explained previously, our set of values encompasses just the integers, there is no separate value for \textit{false}. Also, values and procedures are not distinguished by the type system.

Due to recursion, one variable can have more than one currently valid binding, and due to closures all bindings can possibly be accessed. A simple call stack is therefore not sufficient. Instead we have a \textit{contour counter}, which is increased in each evaluation step. It can also be thought of as a time counter. The variable environment maps tuples of variables and contour counter to values, thus allowing a variable to have more than one active binding.  A contour environment lists the currently visible binding for each binding position and is preserved when a lambda expression is turned into a closure.
\<close>

type_synonym contour = nat
type_synonym benv = "label \<rightharpoonup> contour"
type_synonym closure = "lambda \<times> benv"

text \<open>
The set of semantic values consist of the integers, closures, primitive operations and a special value \<open>Stop\<close>. This is passed as an argument to the program and represents the terminal continuation. When this value occurs in the first position of a call, the program terminates.
\<close>

datatype d = DI int
           | DC closure
           | DP prim
           | Stop

type_synonym venv = "var \<times> contour \<rightharpoonup> d"

text \<open>
The function \<open>\<A>\<close> evaluates a syntactic value into a semantic datum. Constants and primitive operations are left untouched. Variable references are resolved in two stages: First the current binding contour is fetched from the binding environment \<open>\<beta>\<close>, then the stored value is fetched from the variable environment \<open>ve\<close>. A lambda expression is bundled with the current contour environment to form a closure.
\<close>

fun evalV :: "val \<Rightarrow> benv \<Rightarrow> venv \<Rightarrow> d" ("\<A>")
  where "\<A> (C _ i) \<beta> ve = DI i"
  |     "\<A> (P prim) \<beta> ve = DP prim"
  |     "\<A> (R _ var) \<beta> ve =
           (case \<beta> (binder var) of
              Some l \<Rightarrow> (case ve (var,l) of Some d \<Rightarrow> d))"
  |     "\<A> (L lam) \<beta> ve = DC (lam, \<beta>)"


text \<open>
The answer domain of our semantics is the set of integers, lifted to obtain an additional element denoting bottom. Shivers distinguishes runtime errors from non-termination. Here, both are represented by \<open>\<bottom>\<close>.
\<close>

type_synonym ans = "int lift"

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
As usual, the semantics of a functional language is given as a denotational semantics. To that end, two functions are defined here: \<open>\<F>\<close> applies a procedure to a list of arguments. Here closures are unwrapped, the primitive operations are implemented and the terminal continuation \<open>Stop\<close> is handled. \<open>\<C>\<close> evaluates a call expression, either by evaluating procedure and arguments and passing them to \<open>\<F>\<close>, or by adding the bindings of a \<open>Let\<close> expression to the environment.

Note how the contour counter is incremented before each call to \<open>\<F>\<close> or when a \<open>Let\<close> expression is evaluated.

With mutually recursive equations, such as those given here, the existence of a function satisfying these is not obvious. Therefore, the \<open>fixrec\<close> command from the @{theory HOLCF} package is used. This takes a set of equations and builds a functional from that. It mechanically proofs that this functional is continuous and thus a least fixed point exists. This is then used to define \<open>\<F>\<close> and \<open>\<C>\<close> and proof the equations given here. To use the @{theory HOLCF} setup, the continuous function arrow \<open>\<rightarrow>\<close> with application operator \<open>\<cdot>\<close> is used and our types are wrapped in \<open>discr\<close> and \<open>lift\<close> to indicate which partial order is to be used.
\<close>

type_synonym fstate = "(d \<times> d list \<times> venv \<times> contour)"
type_synonym cstate = "(call \<times> benv \<times> venv \<times> contour)"


fixrec   evalF :: "fstate discr \<rightarrow> ans" ("\<F>")
     and evalC :: "cstate discr \<rightarrow> ans" ("\<C>")
  where "evalF\<cdot>fstate = (case undiscr fstate of
             (DC (Lambda lab vs c, \<beta>), as, ve, b) \<Rightarrow>
               (if length vs = length as
                then let \<beta>' = \<beta> (lab \<mapsto> b);
                         ve' = map_upds ve (map (\<lambda>v.(v,b)) vs) as
                     in \<C>\<cdot>(Discr (c,\<beta>',ve',b))
                else \<bottom>)
            | (DP (Plus c),[DI a1, DI a2, cnt],ve,b) \<Rightarrow>
                     let b' = Suc b;
                         \<beta>  = [c \<mapsto> b]
                     in \<F>\<cdot>(Discr (cnt,[DI (a1 + a2)],ve,b'))
            | (DP (prim.If ct cf),[DI v, contt, contf],ve,b) \<Rightarrow>
                  (if v \<noteq> 0
                   then let b' = Suc b;
                            \<beta> = [ct \<mapsto> b]
                        in \<F>\<cdot>(Discr (contt,[],ve,b'))
                   else let b' = Suc b;
                            \<beta> = [cf \<mapsto> b]
                        in \<F>\<cdot>(Discr (contf,[],ve,b')))
            | (Stop,[DI i],_,_) \<Rightarrow> Def i
            | _ \<Rightarrow> \<bottom>
        )"
      | "\<C>\<cdot>cstate = (case undiscr cstate of
             (App lab f vs,\<beta>,ve,b) \<Rightarrow>
                 let f' = \<A> f \<beta> ve;
                     as = map (\<lambda>v. \<A> v \<beta> ve) vs;
                     b' = Suc b
                  in \<F>\<cdot>(Discr (f',as,ve,b'))
            | (Let lab ls c',\<beta>,ve,b) \<Rightarrow>
                 let b' = Suc b;
                     \<beta>' = \<beta> (lab \<mapsto> b');
                    ve' = ve ++ map_of (map (\<lambda>(v,l). ((v,b'), \<A> (L l) \<beta>' ve)) ls)
                 in \<C>\<cdot>(Discr (c',\<beta>',ve',b'))
        )"

text \<open>
To evaluate a full program, it is passed to \<open>\<F>\<close> with proper initializations of the other arguments. We test our semantics function against two example programs and observe that the expected value is returned. 
\<close>

definition evalCPS :: "prog \<Rightarrow> ans" ("\<PR>")
  where "\<PR> l = (let ve = Map.empty;
                          \<beta> = Map.empty;
                          f = \<A> (L l) \<beta> ve
                      in  \<F>\<cdot>(Discr (f,[Stop],ve,0)))"

lemma correct_ex1: "\<PR> ex1 = Def 0"
unfolding evalCPS_def
by simp

lemma correct_ex2: "\<PR> ex2 = Def 2"
unfolding evalCPS_def
by simp

(* (The third example takes long to finish, thus is it not ran by default.) 
lemma correct_ex3: "evalCPS ex3 = Def 55"
oops
unfolding evalCPS_def
by simp
*)

end
