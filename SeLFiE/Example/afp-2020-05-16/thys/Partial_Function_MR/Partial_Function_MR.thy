(* Author: Rene Thiemann, License: LGPL *)

theory Partial_Function_MR
imports Main
keywords "partial_function_mr" :: thy_decl
begin

subsection  \<open>Register the \isa{partial-function-mr} command\<close>
ML_file \<open>partial_function_mr.ML\<close>
              
subsection \<open>Register the "option"-monad\<close>

text \<open>Obviously, the map-function for the @{type option}-monad is @{term map_option}.\<close>

text \<open>First, derive the required identity lemma.\<close>

lemma option_map_id: "map_option (\<lambda> x. x) x = x" 
  by (cases x, auto)

text \<open>Second, register @{term map_option} as being monotone.\<close>
lemma option_map_mono[partial_function_mono]:
  assumes mf: "mono_option B"
  shows "mono_option (\<lambda>f. map_option h (B f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> 'b option" assume fg: "fun_ord option_ord f g"
  with mf
  have "option_ord (B f) (B g)" by (rule monotoneD[of _ _ _ f g])
  then show "option_ord (map_option h (B f)) (map_option h (B g))"
    unfolding flat_ord_def by auto    
qed

text \<open>And finally perform the registration. We need 
\begin{itemize}
\item a constructor for map: it takes a monadic term $mt$ of type \isa{mtT},
  a list of functions \isa{t-to-ss} with corresponding types in \isa{t-to-sTs},
  a resulting monadic type \isa{msT}, and it should return a monad term \isa{ms} of
  type \isa{msT} which
  is obtained by applying the functions on \isa{mt}. Although for the @{type option}-monad,
  the lengths of the lists will always be one, there might be more elements for monads having
  more than one type-parameter.
\item a function to perform type-construction for monads: it takes a list of fixed parameters
  and a list of flexible parameters and has to construct a monadic type out of these parameters.
  The user can freely choose which parameters should be fixed, and which are flexible.
  Only flexible parameters can be changes in the return type of each set of mutual recursive functions.
  Since in the @{type option}-monad we would like to be able to change the type-parameter, we ignore
  the fixed parameters here.
\item a function to deconstruct monadic types into fixed and flexible type arguments.
\item a compositionality theorem of the form @{term "map f (map g x) = map (f o g) x"} 
\item an identity theorem of the form @{term "map (\<lambda> x. x) m = m"} 
\end{itemize}
\<close>
declaration \<open>Partial_Function_MR.init 
  "option" 
  (fn (mt, t_to_ss, mtT, msT, t_to_sTs) =>
      list_comb (Const (@{const_name map_option}, t_to_sTs ---> mtT --> msT), t_to_ss) $ mt)
  (fn (_,argTs) => Type (@{type_name option}, argTs))
  (fn mT => ([],Term.dest_Type mT |> #2)) 
  @{thms option.map_comp} 
  @{thms option_map_id}
\<close>

subsection \<open>Register the "tailrec"-monad\<close>

text \<open>For the "tailrec"-monad (which is the identity monad) we take the identity
  function as map, there are no flexible parameters, and the monadic type itself is
  the (only) fixed argument. As a consequence, we can only define tail-recursive and 
  mutual recursive functions which share the same return type.\<close>

declaration \<open>Partial_Function_MR.init 
  "tailrec" 
  (fn (mt, t_to_ss, mtT, msT, t_to_sTs) => mt)
  (fn (commonT,_) => hd commonT)
  (fn mT => ([mT],[])) 
  [] 
  []
\<close>

end
