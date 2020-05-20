theory IO
  imports
    Main
    "HOL-Library.Monad_Syntax"
begin

section\<open>IO Monad\<close>
text \<open>
  Inspired by Haskell.
  Definitions from \<^url>\<open>https://wiki.haskell.org/IO_inside\<close>
\<close>

subsection\<open>Real World\<close>
text \<open>
  We model the real world with a fake type.

  WARNING:
    Using low-level commands such as \<^theory_text>\<open>typedecl\<close> instead of high-level \<^theory_text>\<open>datatype\<close> is dangerous.
    We explicitly use a \<^theory_text>\<open>typedecl\<close> instead of a \<^theory_text>\<open>datatype\<close> because we never want to instantiate
    the world. We don't need a constructor, we just need the type.

  The following models an arbitrary type we cannot reason about.
  Don't reason about the complete world! Only write down some assumptions about parts of the world.
\<close>
typedecl real_world (\<open>\<^url>\<close>)

text\<open>
  For examples, see \<^file>\<open>HelloWorld_Proof.thy\<close>.
  In said theory, we model \<^verbatim>\<open>STDIN\<close> and \<^verbatim>\<open>STDOUT\<close> as parts of the world and describe how this part
  of the wold can be affected. We don't model the rest of the world. This allows us to reason about
  \<^verbatim>\<open>STDIN\<close> and \<^verbatim>\<open>STDOUT\<close> as part of the world, but nothing more.
\<close>


subsection\<open>IO Monad\<close>
text \<open>
  The set of all functions which take a \<^typ>\<open>\<^url>\<close> and return an \<^typ>\<open>'\<alpha>\<close> and a \<^typ>\<open>\<^url>\<close>.

  The rough idea of all IO functions is the following: You are given the world in its current state.
  You can do whatever you like to the world. You can produce some value of type \<^typ>\<open>'\<alpha>\<close> and you
  have to return the modified world.

  For example, the \<^verbatim>\<open>main\<close> function is Haskell does not produce a value, therefore, \<^verbatim>\<open>main\<close> in
  Haskell is of type \<^verbatim>\<open>IO ()\<close>. Another example in Haskell is \<^verbatim>\<open>getLine\<close>, which returns \<^verbatim>\<open>String\<close>.
  It's type in Haskell is \<^verbatim>\<open>IO String\<close>. All those functions may also modify the state of the world.
\<close>

typedef '\<alpha> io = "UNIV :: (\<^url> \<Rightarrow> '\<alpha> \<times> \<^url>) set"
proof -
  show "\<exists>x. x \<in> UNIV" by simp
qed

text \<open>
  Related Work:
  \<^emph>\<open>Programming TLS in Isabelle/HOL\<close> by Andreas Lochbihler and Marc Züst uses a partial function
  (\<open>\<rightharpoonup>\<close>).
  \<^theory_text>\<open>
    typedecl real_world
    typedef '\<alpha> io = "UNIV :: (\<^url> \<rightharpoonup> '\<alpha> \<times> \<^url>) set" by simp
  \<close>
  We use a total function. This implies the dangerous assumption that all IO functions are total
  (i.e., terminate).
\<close>

text \<open>
  The \<^theory_text>\<open>typedef\<close> above gives us some convenient definitions.
  Since the model of \<^typ>\<open>'\<alpha> io\<close> is just a mode, those definitions should not end up in generated
  code.
\<close>
term Abs_io \<comment> \<open>Takes a \<^typ>\<open>(\<^url> \<Rightarrow> '\<alpha> \<times> \<^url>)\<close> and abstracts it to an \<^typ>\<open>'\<alpha> io\<close>.\<close>
term Rep_io \<comment> \<open>Unpacks an \<^typ>\<open>'\<alpha> io\<close> to a \<^typ>\<open>(\<^url> \<Rightarrow> '\<alpha> \<times> \<^url>)\<close>\<close>


subsection\<open>Monad Operations\<close>
text\<open>
  Within an \<^typ>\<open>'\<alpha> io\<close> context, execute \<^term>\<open>action\<^sub>1\<close> and \<^term>\<open>action\<^sub>2\<close> sequentially.
  The world is passed through and potentially modified by each action.
\<close>
definition bind :: "'\<alpha> io \<Rightarrow> ('\<alpha> \<Rightarrow> '\<beta> io) \<Rightarrow> '\<beta> io" where [code del]:
  "bind action\<^sub>1 action\<^sub>2 = Abs_io (\<lambda>world\<^sub>0.
                                  let (a, world\<^sub>1) = (Rep_io action\<^sub>1) world\<^sub>0;
                                      (b, world\<^sub>2) = (Rep_io (action\<^sub>2 a)) world\<^sub>1
                                  in (b, world\<^sub>2))"

text \<open>
  In Haskell, the definition for \<^verbatim>\<open>bind\<close> (\<^verbatim>\<open>>>=\<close>) is:
  \<^verbatim>\<open>
    (>>=) :: IO a -> (a -> IO b) -> IO b
    (action1 >>= action2) world0 =
       let (a, world1) = action1 world0
           (b, world2) = action2 a world1
       in (b, world2)
  \<close>
\<close>

hide_const (open) bind
adhoc_overloading bind IO.bind

text \<open>Thanks to \<^theory_text>\<open>adhoc_overloading\<close>, we can use monad syntax.\<close>
lemma "bind (foo :: '\<alpha> io) (\<lambda>a. bar a) = foo \<bind> (\<lambda>a. bar a)"
  by simp


definition return :: "'\<alpha> \<Rightarrow> '\<alpha> io" where [code del]:
  "return a \<equiv> Abs_io (\<lambda>world. (a, world))"

hide_const (open) return

text \<open>
  In Haskell, the definition for \<^verbatim>\<open>return\<close> is::
  \<^verbatim>\<open>
    return :: a -> IO a
    return a world0  =  (a, world0)
  \<close>
\<close>


subsection\<open>Monad Laws\<close>
lemma left_id:
  fixes f :: "'\<alpha> \<Rightarrow> '\<beta> io" \<comment> \<open>Make sure we use our \<^const>\<open>IO.bind\<close>.\<close>
  shows "(IO.return a \<bind> f) = f a"
  by(simp add: return_def IO.bind_def Abs_io_inverse Rep_io_inverse)

lemma right_id:
  fixes m :: "'\<alpha> io" \<comment> \<open>Make sure we use our \<^const>\<open>IO.bind\<close>.\<close>
  shows "(m \<bind> IO.return) = m"
  by(simp add: return_def IO.bind_def Abs_io_inverse Rep_io_inverse)
    
lemma bind_assoc:
  fixes m :: "'\<alpha> io" \<comment> \<open>Make sure we use our \<^const>\<open>IO.bind\<close>.\<close>
  shows "((m \<bind> f) \<bind> g) = (m \<bind> (\<lambda>x. f x \<bind> g))"
  by(simp add: IO.bind_def Abs_io_inverse Abs_io_inject fun_eq_iff split: prod.splits)


subsection\<open>Code Generator Setup\<close>
text \<open>
  We don't expose our \<^const>\<open>IO.bind\<close> definition to code.
  We use the built-in definitions of the target language (e.g., Haskell, SML).
\<close>
code_printing constant IO.bind \<rightharpoonup> (Haskell) "_ >>= _"
                                  and (SML) "bind"
            | constant IO.return \<rightharpoonup> (Haskell) "return"
                                    and (SML) "(() => _)"

text\<open>SML does not come with a bind function. We just define it (hopefully correct).\<close>
code_printing code_module Bind \<rightharpoonup> (SML) \<open>
fun bind x f () = f (x ()) ();
\<close>
code_reserved SML bind return
  
text\<open>
  Make sure the code generator does not try to define \<^typ>\<open>'\<alpha> io\<close> by itself, but always uses
  the one of the target language.
  For Haskell, this is the fully qualified Prelude.IO.
  For SML, we wrap it in a nullary function.
\<close>
code_printing type_constructor io \<rightharpoonup> (Haskell) "Prelude.IO _"
                                     and (SML) "unit -> _"


text\<open>
In Isabelle, a \<^typ>\<open>string\<close> is just a type synonym for \<^typ>\<open>char list\<close>.
When translating a \<^typ>\<open>string\<close> to Haskell, Isabelle does not use Haskell's \<^verbatim>\<open>String\<close> or 
\<^verbatim>\<open>[Prelude.Char]\<close>. Instead, Isabelle serializes its own
  \<^verbatim>\<open>data Char = Char Bool Bool Bool Bool Bool Bool Bool Bool\<close>.
The resulting code will look just ugly.

To use the native strings of Haskell, we use the Isabelle type \<^typ>\<open>String.literal\<close>.
This gets translated to a Haskell \<^verbatim>\<open>String\<close>.

A string literal in Isabelle is created with \<^term>\<open>STR ''foo'' :: String.literal\<close>.
\<close>

text\<open>
  We define IO functions in Isabelle without implementation.
  For a proof in Isabelle, we will only describe their externally observable properties.
  For code generation, we map those functions to the corresponding function of the target language.

  Our assumption is that our description in Isabelle corresponds to the real behavior of those
  functions in the respective target language.

  We use \<^theory_text>\<open>axiomatization\<close> instead of \<^theory_text>\<open>consts\<close> to axiomatically define that those functions exist,
  but there is no implementation of them. This makes sure that we have to explicitly write down all
  our assumptions about their behavior. Currently, no assumptions (apart from their type) can be
  made about those functions.
\<close>
axiomatization
  println :: "String.literal \<Rightarrow> unit io" and
  getLine :: "String.literal io"

text \<open>A Haskell module named \<^verbatim>\<open>StdIO\<close> which just implements \<^verbatim>\<open>println\<close> and \<^verbatim>\<open>getLine\<close>.\<close>
code_printing code_module StdIO \<rightharpoonup> (Haskell) \<open>
module StdIO (println, getLine) where
import qualified Prelude (putStrLn, getLine)
println = Prelude.putStrLn
getLine = Prelude.getLine
\<close>                              and (SML) \<open>
(* Newline behavior in SML is odd.*)
fun println s () = TextIO.print (s ^ "\n");
fun getLine () = case (TextIO.inputLine TextIO.stdIn) of
                  SOME s => String.substring (s, 0, String.size s - 1)
                | NONE => raise Fail "getLine";
\<close>

code_reserved Haskell StdIO println getLine
code_reserved SML println print getLine TextIO

text\<open>
  When the code generator sees the functions \<^const>\<open>println\<close> or \<^const>\<open>getLine\<close>, we tell it to use
  our language-specific implementation.
  \<close>
code_printing constant println \<rightharpoonup> (Haskell) "StdIO.println"
                              and (SML) "println"
            | constant getLine \<rightharpoonup> (Haskell) "StdIO.getLine"
                              and (SML) "getLine"


text\<open>Monad syntax and \<^const>\<open>println\<close> examples.\<close>
lemma "bind (println (STR ''foo''))
            (\<lambda>_.  println (STR ''bar'')) =
       println (STR ''foo'') \<bind> (\<lambda>_. println (STR ''bar''))"
  by simp 
lemma "do { _ \<leftarrow> println (STR ''foo'');
            println (STR ''bar'')} =
      println (STR ''foo'') \<then> (println (STR ''bar''))"
  by simp



subsection\<open>Modelling Running an \<^typ>\<open>'\<alpha> io\<close> Function\<close>
text\<open>
  Apply some function \<^term>\<open>iofun :: '\<alpha> io\<close> to a specific world and return the new world
  (discarding the result of \<^term>\<open>iofun\<close>).
\<close>
definition exec :: "'\<alpha> io \<Rightarrow> \<^url> \<Rightarrow> \<^url>" where
  "exec iofun world = snd (Rep_io iofun world)"

text\<open>Similar, but only get the result.\<close>
definition eval :: "'\<alpha> io \<Rightarrow> \<^url> \<Rightarrow> '\<alpha>" where
  "eval iofun world = fst (Rep_io iofun world)"

text\<open>
  Essentially, \<^const>\<open>exec\<close> and \<^const>\<open>eval\<close> extract the payload \<^typ>\<open>'\<alpha>\<close> and \<^typ>\<open>\<^url>\<close>
  when executing an \<^typ>\<open>'\<alpha> io\<close>.
\<close>
lemma "Abs_io (\<lambda>world. (eval iofun world, exec iofun world)) = iofun"
  by(simp add: exec_def eval_def Rep_io_inverse)

lemma exec_Abs_io: "exec (Abs_io f) world = snd (f world)"
  by(simp add: exec_def Abs_io_inverse)


lemma exec_then:
    "exec (io\<^sub>1 \<then> io\<^sub>2) world = exec io\<^sub>2 (exec io\<^sub>1 world)"
  and eval_then:
    "eval (io\<^sub>1 \<then> io\<^sub>2) world = eval io\<^sub>2 (exec io\<^sub>1 world)"
  by (simp_all add: exec_def eval_def bind_def Abs_io_inverse split_beta)

lemma exec_bind:
    "exec (io\<^sub>1 \<bind> io\<^sub>2) world = exec (io\<^sub>2 (eval io\<^sub>1 world)) (exec io\<^sub>1 world)"
  and eval_bind:
    "eval (io\<^sub>1 \<bind> io\<^sub>2) world = eval (io\<^sub>2 (eval io\<^sub>1 world)) (exec io\<^sub>1 world)"
  by(simp_all add: exec_def eval_def bind_def Abs_io_inverse split_beta)

lemma exec_return:
    "exec (IO.return a) world = world"
  and
    "eval (IO.return a) world = a"
  by (simp_all add: exec_def eval_def Abs_io_inverse return_def)


end