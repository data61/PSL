theory SyntaxTweaks 
imports Main
begin

syntax (implnl output)
  "\<Longrightarrow>" :: "prop \<Rightarrow> prop \<Rightarrow> prop" ("_ //\<Longrightarrow> _" [0,1] 1)

notation (holimplnl output)
"implies" ("(2_ \<longrightarrow>// _)" [0,1] 1)
notation (holimplnl output)
"conj" ("_ \<and>/ _" [34,35]35)
  

syntax (letnl output)
  "_binds"      :: "[letbind, letbinds] => letbinds"     ("_;//_")
text \<open>Theorems as inference rules, usepackage mathpartir\<close>

syntax (eqindent output) "op =" ::"['a, 'a] => bool"               ( "(2_ =/ _)" [49,50]50)

(* LOGIC *)
syntax (latex output)
  If            :: "[bool, 'a, 'a] => 'a"
  ("(\<^latex>\<open>\\holkeyword{\<close>if\<^latex>\<open>}\<close>(_)/ \<^latex>\<open>\\holkeyword{\<close>then\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\\holkeyword{\<close>else\<^latex>\<open>}\<close> (_))" 10)

  "_Let"        :: "[letbinds, 'a] => 'a"
  ("(\<^latex>\<open>\\holkeyword{\<close>let\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\\holkeyword{\<close>in\<^latex>\<open>}\<close> (_))" 10)

  "_case_syntax":: "['a, cases_syn] => 'b"
  ("(\<^latex>\<open>\\holkeyword{\<close>case\<^latex>\<open>}\<close> _ \<^latex>\<open>\\holkeyword{\<close>of\<^latex>\<open>}\<close>/ _)" 10)

notation (Rule output)
  Pure.imp  ("\<^latex>\<open>\\mbox{}\\inferrule{\\mbox{\<close>_\<^latex>\<open>}}\<close>\<^latex>\<open>{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

syntax (Rule output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>\\mbox{}\\inferrule{\<close>_\<^latex>\<open>}\<close>\<^latex>\<open>{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" 
  ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\\\\\<close>/ _")

  "_asm" :: "prop \<Rightarrow> asms" ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close>")


notation (Axiom output)
  "Trueprop"  ("\<^latex>\<open>\\mbox{}\\inferrule{\\mbox{}}{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

syntax (IfThen output)
  "==>" :: "prop \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _/ \<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.")

  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _ /\<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.")

  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close> /\<^latex>\<open>{\\normalsize \\,\<close>and\<^latex>\<open>\\,}\<close>/ _")
  "_asm" :: "prop \<Rightarrow> asms" ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close>")

syntax (IfThenNoBox output)
  "==>" :: "prop \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _/ \<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.")
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _ /\<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>:\\,}\<close>/ _.")
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" ("_ /\<^latex>\<open>{\\normalsize \\,\<close>and\<^latex>\<open>\\,}\<close>/ _")
  "_asm" :: "prop \<Rightarrow> asms" ("_")


text \<open>power\<close>
syntax (latex output)
  power :: "['a::power, nat] => 'a"           ("_\<^bsup>_\<^esup>" [1000,0]80)

(* empty set *)
syntax (latex output)
  "_emptyset" :: "'a set"              ("\<emptyset>")
translations
  "_emptyset"      <= "{}"

text \<open>insert\<close>
translations 
(*
  "{x} \<union> A" <= "insert x A"
*)
  "{x,y}" <= "{x} \<union> {y}"
  "{x,y} \<union> A" <= "{x} \<union> ({y} \<union> A)"
  "{x}" <= "{x} \<union> {}"


syntax (latex output)
 Cons :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"    (infixr "\<cdot>" 65)

syntax (latex output)
 "Some" :: "'a \<Rightarrow> 'a option" ("(\<lfloor>_\<rfloor>)")
 "None" :: "'a option" ("\<bottom>")

text \<open>lesser indentation as default\<close>
syntax (latex output)
  "ALL "        :: "[idts, bool] => bool"                ("(2\<forall>_./ _)" [0, 10] 10)
  "EX "         :: "[idts, bool] => bool"                ("(2\<exists>_./ _)" [0, 10] 10)

text \<open>space around \<in>\<close>
syntax (latex output)
  "_Ball"       :: "pttrn => 'a set => bool => bool"      ("(3\<forall>_\<^latex>\<open>\\,\<close>\<in>_./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      ("(3\<exists>_\<^latex>\<open>\\,\<close>\<in>_./ _)" [0, 0, 10] 10)

text \<open>compact line breaking for some infix operators\<close>
term "HOL.conj"
notation (compact output)
"conj" ("_ \<and>/ _" [34,35]35)
notation (compact output)
"append" ("_ @/ _" [64,65]65)

text \<open>force a newline after definition equation\<close>
syntax (defnl output)
  "=="       :: "[prop, prop] => prop"                ("(2_ \<equiv>// _)" [1,2] 2) 
syntax (defeqnl output)
  "=="       :: "[prop, prop] => prop"                ("(2_ =// _)" [1,2] 2) 
syntax (eqnl output)
  "op ="       :: "['a, 'a] => bool"                     ("(2_ =// _)" [1,2] 2) 
syntax (latex output)
  "=="       :: "[prop, prop] => prop"                ("(2_ \<equiv>/ _)" [1,2] 2) 

text \<open>New-line after assumptions\<close>
syntax (asmnl output)
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" 
  ("_; // _")

text \<open>uncurry functions\<close>
syntax (uncurry output)
"_cargs" :: "'a \<Rightarrow> cargs \<Rightarrow> cargs" ("_, _")
"_applC" :: "[('b => 'a), cargs] => logic" ("(1_/(1'(_')))" [1000, 0] 1000)

text \<open>but keep curried notation for constructors\<close>
syntax (uncurry output)
"_cargs_curry":: "'a \<Rightarrow> cargs \<Rightarrow> cargs" ("_ _" [1000,1000] 1000)
"_applC_curry":: "[('b => 'a), cargs] => logic" ("(1_/ _)" [1000, 1000] 999)



text \<open>`dot'-selector notation for records\<close>
syntax (latex output)
"_rec_sel" :: "'r \<Rightarrow> id \<Rightarrow> 'a" ("_._" [1000,1000]1000)


ML \<open>
structure Latex =   (* FIXME eliminate clone of Latex.latex_markup (export it in Pure) *)
struct
  open Latex;

  fun latex_markup (s, props: Properties.T) =
    if s = Markup.commandN orelse s = Markup.keyword1N orelse s = Markup.keyword3N
    then ("\\isacommand{", "}")
    else if s = Markup.keyword2N
    then ("\\isakeyword{", "}")
    else Markup.no_output;
end;

fun latex_markup (s, props) =
  if s = Markup.boundN orelse s = Markup.freeN orelse s = Markup.varN orelse s = Markup.tfreeN orelse s = Markup.tvarN
  then ("\\" ^ s ^ "ify{", "}")
  else Latex.latex_markup (s, props);


val _ = Markup.add_mode Latex.latexN latex_markup;
\<close>


text \<open>invisible binder in case we want to force "bound"-markup\<close>
consts Bind:: "('a \<Rightarrow> 'b) \<Rightarrow> 'c" (binder "Bind " 10)
translations
  "f" <= "Bind x. f"


(* length *)
notation (latex output)
  length  ("|_|")

(* Optional values *)
notation (latex output)
  None ("\<bottom>")

notation (latex output)
  Some ("\<lfloor>_\<rfloor>")

(* nth *)
notation (latex output)
  nth  ("_\<^latex>\<open>\\ensuremath{_{[\<close>_\<^latex>\<open>]}}\<close>" [1000,0] 1000)

end
