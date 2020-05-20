section \<open> UTP Expressions \<close>

theory utp_expr
imports
  utp_var
begin

subsection \<open> Expression type \<close>
  
purge_notation BNF_Def.convol ("\<langle>(_,/ _)\<rangle>")

text \<open> Before building the predicate model, we will build a model of expressions that generalise
  alphabetised predicates. Expressions are represented semantically as mapping from
  the alphabet @{typ "'\<alpha>"} to the expression's type @{typ "'a"}. This general model will allow us to unify
  all constructions under one type. The majority definitions in the file are given using
  the \emph{lifting} package~\cite{Huffman13}, which allows us to reuse much of the existing
  library of HOL functions. \<close>

typedef ('t, '\<alpha>) uexpr = "UNIV :: ('\<alpha> \<Rightarrow> 't) set" ..

setup_lifting type_definition_uexpr
    
notation Rep_uexpr ("\<lbrakk>_\<rbrakk>\<^sub>e")
notation Abs_uexpr ("mk\<^sub>e")

lemma uexpr_eq_iff:
  "e = f \<longleftrightarrow> (\<forall> b. \<lbrakk>e\<rbrakk>\<^sub>e b = \<lbrakk>f\<rbrakk>\<^sub>e b)"
  using Rep_uexpr_inject[of e f, THEN sym] by (auto)

text \<open> The term @{term "\<lbrakk>e\<rbrakk>\<^sub>e b"} effectively refers to the semantic interpretation of the expression
  under the state-space valuation (or variables binding) @{term b}. It can be used, in concert
  with the lifting package, to interpret UTP constructs to their HOL equivalents. We create some
  theorem sets to store such transfer theorems. \<close>
    
named_theorems uexpr_defs and ueval and lit_simps and lit_norm

subsection \<open> Core expression constructs \<close>
  
text \<open> A variable expression corresponds to the lens $get$ function associated with a variable. 
  Specifically, given a lens the expression always returns that portion of the state-space
  referred to by the lens. \<close>

lift_definition var :: "('t \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t, '\<alpha>) uexpr" is lens_get .

text \<open> A literal is simply a constant function expression, always returning the same value
  for any binding. \<close>

lift_definition lit :: "'t \<Rightarrow> ('t, '\<alpha>) uexpr" ("\<guillemotleft>_\<guillemotright>") is "\<lambda> v b. v" .

text \<open> We define lifting for unary, binary, ternary, and quaternary expression constructs, that 
  simply take a HOL function with correct number of arguments and apply it function to all possible 
  results of the expressions. \<close>

lift_definition uop :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr"
  is "\<lambda> f e b. f (e b)" .
lift_definition bop ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr"
  is "\<lambda> f u v b. f (u b) (v b)" .
lift_definition trop ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr \<Rightarrow> ('d, '\<alpha>) uexpr"
  is "\<lambda> f u v w b. f (u b) (v b) (w b)" .
lift_definition qtop ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow>
   ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr \<Rightarrow> ('d, '\<alpha>) uexpr \<Rightarrow>
   ('e, '\<alpha>) uexpr"
  is "\<lambda> f u v w x b. f (u b) (v b) (w b) (x b)" .

text \<open> We also define a UTP expression version of function ($\lambda$) abstraction, that takes
  a function producing an expression and produces an expression producing a function. \<close>

lift_definition ulambda :: "('a \<Rightarrow> ('b, '\<alpha>) uexpr) \<Rightarrow> ('a \<Rightarrow> 'b, '\<alpha>) uexpr"
is "\<lambda> f A x. f x A" .

text \<open> We set up syntax for the conditional. This is effectively an infix version of
  if-then-else where the condition is in the middle. \<close>

definition uIf :: "bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
[uexpr_defs]: "uIf = If"

abbreviation cond ::
  "('a,'\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr \<Rightarrow> ('a,'\<alpha>) uexpr \<Rightarrow> ('a,'\<alpha>) uexpr"
  ("(3_ \<triangleleft> _ \<triangleright>/ _)" [52,0,53] 52)
where "P \<triangleleft> b \<triangleright> Q \<equiv> trop uIf b P Q"

text \<open> UTP expression is equality is simply HOL equality lifted using the @{term bop} binary 
  expression constructor. \<close>
    
definition eq_upred :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infixl "=\<^sub>u" 50)
where [uexpr_defs]: "eq_upred x y = bop HOL.eq x y"

text \<open> A literal is the expression @{term "\<guillemotleft>v\<guillemotright>"}, where @{term v} is any HOL term. Actually, the
  literal construct is very versatile and also allows us to refer to HOL variables within UTP
  expressions, and has a variety of other uses. It can therefore also be considered as a kind
  of quotation mechanism. 

  We also set up syntax for UTP variable expressions. \<close>
  
syntax
  "_uuvar" :: "svar \<Rightarrow> logic" ("_")

translations
  "_uuvar x" == "CONST var x"
  
text \<open> Since we already have a parser for variables, we can directly reuse it and simply apply
  the @{term var} expression construct to lift the resulting variable to an expression. \<close>
  
subsection \<open> Type class instantiations \<close>

text \<open> Isabelle/HOL of course provides a large hierarchy of type classes that provide constructs
  such as numerals and the arithmetic operators. Fortunately we can directly make use of these
  for UTP expressions, and thus we now perform a long list of appropriate instantiations. We
  first lift the core arithemtic constants and operators using a mixture of literals, unary, and binary
  expression constructors. \<close>
  
instantiation uexpr :: (zero, type) zero
begin
  definition zero_uexpr_def [uexpr_defs]: "0 = lit 0"
instance ..
end

instantiation uexpr :: (one, type) one
begin
  definition one_uexpr_def [uexpr_defs]: "1 = lit 1"
instance ..

end

instantiation uexpr :: (plus, type) plus
begin
  definition plus_uexpr_def [uexpr_defs]: "u + v = bop (+) u v"
instance ..
end

instance uexpr :: (semigroup_add, type) semigroup_add
  by (intro_classes) (simp add: plus_uexpr_def zero_uexpr_def, transfer, simp add: add.assoc)+

text \<open> The following instantiation sets up numerals. This will allow us to have Isabelle number
  representations (i.e. 3,7,42,198 etc.) to UTP expressions directly. \<close>

instance uexpr :: (numeral, type) numeral
  by (intro_classes, simp add: plus_uexpr_def, transfer, simp add: add.assoc)
     
text \<open> We can also define the order relation on expressions. Now, unlike the previous group and ring 
  constructs, the order relations @{term "(\<le>)"} and @{term "(\<le>)"} return a @{type bool} type.
  This order is not therefore the lifted order which allows us to compare the valuation of two
  expressions, but rather the order on expressions themselves. Notably, this instantiation will
  later allow us to talk about predicate refinements and complete lattices. \<close>
     
instantiation uexpr :: (ord, type) ord
begin
  lift_definition less_eq_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> bool"
  is "\<lambda> P Q. (\<forall> A. P A \<le> Q A)" .
  definition less_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> bool"
  where [uexpr_defs]: "less_uexpr P Q = (P \<le> Q \<and> \<not> Q \<le> P)"
instance ..
end

text \<open> UTP expressions whose return type is a partial ordered type, are also partially ordered
  as the following instantiation demonstrates. \<close>
  
instance uexpr :: (order, type) order
proof
  fix x y z :: "('a, 'b) uexpr"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by (simp add: less_uexpr_def)
  show "x \<le> x" by (transfer, auto)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (transfer, blast intro:order.trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (transfer, rule ext, simp add: eq_iff)
qed

      
subsection \<open> Syntax translations \<close>

text \<open> The follows a large number of translations that lift HOL functions to UTP expressions
  using the various expression constructors defined above. Much of the time we try to keep
  the HOL syntax but add a "u" subscript. \<close>

text \<open> This operator allows us to get the characteristic set of a type. Essentially this is 
  @{term "UNIV"}, but it retains the type syntactically for pretty printing. \<close>

definition set_of :: "'a itself \<Rightarrow> 'a set" where
[uexpr_defs]: "set_of t = UNIV"
      
text \<open> We add new non-terminals for UTP tuples and maplets. \<close>
  
nonterminal utuple_args and umaplet and umaplets

syntax \<comment> \<open> Core expression constructs \<close>
  "_ucoerce"    :: "logic \<Rightarrow> type \<Rightarrow> logic" (infix ":\<^sub>u" 50)
  "_ulambda"    :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<lambda> _ \<bullet> _" [0, 10] 10)
  "_ulens_ovrd" :: "logic \<Rightarrow> logic \<Rightarrow> salpha \<Rightarrow> logic" ("_ \<oplus> _ on _" [85, 0, 86] 86)
  "_ulens_get"  :: "logic \<Rightarrow> svar \<Rightarrow> logic" ("_:_" [900,901] 901)
  "_umem"       :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<in>\<^sub>u" 50)

translations
  "\<lambda> x \<bullet> p" == "CONST ulambda (\<lambda> x. p)"
  "x :\<^sub>u 'a" == "x :: ('a, _) uexpr"
  "_ulens_ovrd f g a" => "CONST bop (CONST lens_override a) f g"
  "_ulens_ovrd f g a" <= "CONST bop (\<lambda>x y. CONST lens_override x1 y1 a) f g"
  "_ulens_get x y" == "CONST uop (CONST lens_get y) x"
  "x \<in>\<^sub>u A" == "CONST bop (\<in>) x A"

syntax \<comment> \<open> Tuples \<close>
  "_utuple"     :: "('a, '\<alpha>) uexpr \<Rightarrow> utuple_args \<Rightarrow> ('a * 'b, '\<alpha>) uexpr" ("(1'(_,/ _')\<^sub>u)")
  "_utuple_arg"  :: "('a, '\<alpha>) uexpr \<Rightarrow> utuple_args" ("_")
  "_utuple_args" :: "('a, '\<alpha>) uexpr => utuple_args \<Rightarrow> utuple_args"     ("_,/ _")
  "_uunit"      :: "('a, '\<alpha>) uexpr" ("'(')\<^sub>u")
  "_ufst"       :: "('a \<times> 'b, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<pi>\<^sub>1'(_')")
  "_usnd"       :: "('a \<times> 'b, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr" ("\<pi>\<^sub>2'(_')")

translations
  "()\<^sub>u"      == "\<guillemotleft>()\<guillemotright>"
  "(x, y)\<^sub>u"  == "CONST bop (CONST Pair) x y"
  "_utuple x (_utuple_args y z)" == "_utuple x (_utuple_arg (_utuple y z))"
  "\<pi>\<^sub>1(x)"    == "CONST uop CONST fst x"
  "\<pi>\<^sub>2(x)"    == "CONST uop CONST snd x"

syntax \<comment> \<open> Orders \<close>
  "_uless"      :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "<\<^sub>u" 50)
  "_uleq"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<le>\<^sub>u" 50)
  "_ugreat"     :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix ">\<^sub>u" 50)
  "_ugeq"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<ge>\<^sub>u" 50)

translations
  "x <\<^sub>u y"   == "CONST bop (<) x y"
  "x \<le>\<^sub>u y"   == "CONST bop (\<le>) x y"
  "x >\<^sub>u y"   => "y <\<^sub>u x"
  "x \<ge>\<^sub>u y"   => "y \<le>\<^sub>u x"

subsection \<open> Evaluation laws for expressions \<close>
  
text \<open> The following laws show how to evaluate the core expressions constructs in terms of which
  the above definitions are defined. Thus, using these theorems together, we can convert any UTP 
  expression into a pure HOL expression. All these theorems are marked as \emph{ueval} theorems
  which can be used for evaluation. \<close>
  
lemma lit_ueval [ueval]: "\<lbrakk>\<guillemotleft>x\<guillemotright>\<rbrakk>\<^sub>eb = x"
  by (transfer, simp)

lemma var_ueval [ueval]: "\<lbrakk>var x\<rbrakk>\<^sub>eb = get\<^bsub>x\<^esub> b"
  by (transfer, simp)

lemma uop_ueval [ueval]: "\<lbrakk>uop f x\<rbrakk>\<^sub>eb = f (\<lbrakk>x\<rbrakk>\<^sub>eb)"
  by (transfer, simp)

lemma bop_ueval [ueval]: "\<lbrakk>bop f x y\<rbrakk>\<^sub>eb = f (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb)"
  by (transfer, simp)

lemma trop_ueval [ueval]: "\<lbrakk>trop f x y z\<rbrakk>\<^sub>eb = f (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb) (\<lbrakk>z\<rbrakk>\<^sub>eb)"
  by (transfer, simp)

lemma qtop_ueval [ueval]: "\<lbrakk>qtop f x y z w\<rbrakk>\<^sub>eb = f (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb) (\<lbrakk>z\<rbrakk>\<^sub>eb) (\<lbrakk>w\<rbrakk>\<^sub>eb)"
  by (transfer, simp)

subsection \<open> Misc laws \<close>

text \<open> We also prove a few useful algebraic and expansion laws for expressions. \<close>
  
lemma uop_const [simp]: "uop id u = u"
  by (transfer, simp)

lemma bop_const_1 [simp]: "bop (\<lambda>x y. y) u v = v"
  by (transfer, simp)

lemma bop_const_2 [simp]: "bop (\<lambda>x y. x) u v = u"
  by (transfer, simp)

lemma uexpr_fst [simp]: "\<pi>\<^sub>1((e, f)\<^sub>u) = e"
  by (transfer, simp)

lemma uexpr_snd [simp]: "\<pi>\<^sub>2((e, f)\<^sub>u) = f"
  by (transfer, simp)

subsection \<open> Literalise tactics \<close>

text \<open> The following tactic converts literal HOL expressions to UTP expressions and vice-versa
        via a collection of simplification rules. The two tactics are called "literalise", which
        converts UTP to expressions to HOL expressions -- i.e. it pushes them into literals --
        and unliteralise that reverses this. We collect the equations in a theorem attribute
        called "lit\_simps". \<close>
        
lemma lit_fun_simps [lit_simps]:
  "\<guillemotleft>i x y z u\<guillemotright> = qtop i \<guillemotleft>x\<guillemotright> \<guillemotleft>y\<guillemotright> \<guillemotleft>z\<guillemotright> \<guillemotleft>u\<guillemotright>"
  "\<guillemotleft>h x y z\<guillemotright> = trop h \<guillemotleft>x\<guillemotright> \<guillemotleft>y\<guillemotright> \<guillemotleft>z\<guillemotright>"
  "\<guillemotleft>g x y\<guillemotright> = bop g \<guillemotleft>x\<guillemotright> \<guillemotleft>y\<guillemotright>"
  "\<guillemotleft>f x\<guillemotright> = uop f \<guillemotleft>x\<guillemotright>"
  by (transfer, simp)+

text \<open> The following two theorems also set up interpretation of numerals, meaning a UTP numeral
  can always be converted to a HOL numeral. \<close>
    
lemma numeral_uexpr_rep_eq [ueval]: "\<lbrakk>numeral x\<rbrakk>\<^sub>e b = numeral x"
  apply (induct x)
    apply (simp add: lit.rep_eq one_uexpr_def)
   apply (simp add: bop.rep_eq numeral_Bit0 plus_uexpr_def)
  apply (simp add: bop.rep_eq lit.rep_eq numeral_code(3) one_uexpr_def plus_uexpr_def)
  done

lemma numeral_uexpr_simp: "numeral x = \<guillemotleft>numeral x\<guillemotright>"
  by (simp add: uexpr_eq_iff numeral_uexpr_rep_eq lit.rep_eq)

lemma lit_zero [lit_simps]: "\<guillemotleft>0\<guillemotright> = 0" by (simp add:uexpr_defs)
lemma lit_one [lit_simps]: "\<guillemotleft>1\<guillemotright> = 1" by (simp add: uexpr_defs)
lemma lit_plus [lit_simps]: "\<guillemotleft>x + y\<guillemotright> = \<guillemotleft>x\<guillemotright> + \<guillemotleft>y\<guillemotright>" by (simp add: uexpr_defs, transfer, simp)
lemma lit_numeral [lit_simps]: "\<guillemotleft>numeral n\<guillemotright> = numeral n" by (simp add: numeral_uexpr_simp)

text \<open> In general unliteralising converts function applications to corresponding expression
  liftings. Since some operators, like + and *, have specific operators we also have to
  use @{thm uexpr_defs} in reverse to correctly interpret these. Moreover, numerals must be handled
  separately by first simplifying them and then converting them into UTP expression numerals;
  hence the following two simplification rules. \<close>

lemma lit_numeral_1: "uop numeral x = Abs_uexpr (\<lambda>b. numeral (\<lbrakk>x\<rbrakk>\<^sub>e b))"
  by (simp add: uop_def)

lemma lit_numeral_2: "Abs_uexpr (\<lambda> b. numeral v) = numeral v"
  by (metis lit.abs_eq lit_numeral)
  
method literalise = (unfold lit_simps[THEN sym])
method unliteralise = (unfold lit_simps uexpr_defs[THEN sym];
                     (unfold lit_numeral_1 ; (unfold uexpr_defs ueval); (unfold lit_numeral_2))?)+
                   
text \<open> The following tactic can be used to evaluate literal expressions. It first literalises UTP 
  expressions, that is pushes as many operators into literals as possible. Then it tries to simplify,
  and final unliteralises at the end. \<close>

method uexpr_simp uses simps = ((literalise)?, simp add: lit_norm simps, (unliteralise)?)

(* Example *)
  
lemma "(1::(int, '\<alpha>) uexpr) + \<guillemotleft>2\<guillemotright> = 4 \<longleftrightarrow> \<guillemotleft>3\<guillemotright> = 4"
  apply (literalise)
  apply (uexpr_simp) oops

end