theory RunningCodeFromIsabelle
  imports HelloWorld
begin

section\<open>Running the Generated Code inside Isabelle\<close>

(*Maintainer note: We invoke the generated code ON PURPOSE from bash to demonstrate how to use
  the generated code from outside Isabelle and make sure the code runs.*)


text\<open>
  Usually, one would use \<^theory_text>\<open>export_code\<close> to generate code. Here, we want to write the code to
  a temp directory and execute it right afterwards inside Isablle, so we invoke the code generator
  directly from Isabelle/ML.
\<close>

subsection\<open>Haskell\<close>

ML\<open>
val (files, _) =
  Code_Target.produce_code @{context} false [@{const_name main}] "Haskell" "Main" NONE []

val target = File.tmp_path (Path.basic ("export" ^ serial_string ()))

val ghc = getenv "ISABELLE_GHC";

val cmd =
  "cd " ^ Path.implode target ^ " && " ^
    Bash.string ghc ^ " Main.hs && " ^
    "(  echo 'Cyber Cat 42' | ./Main )";

Isabelle_System.mkdirs target;

app (fn ([file], content) =>
   let
     val path = Path.append target (Path.basic file)
   in
     File.write path content
   end) files;

val exitcode =
  if ghc <> "" then
    Isabelle_System.bash cmd
  else
    (writeln "not running Haskell, because $ISABELLE_GHC is not set."; 0);

if exitcode <> 0 then
  raise (Fail ("example Haskell code did not run as expected, " ^
                 "exit code was " ^ (Int.toString exitcode)))
else ()
\<close>


subsection\<open>SML\<close>

ML\<open>

val ([(_, content)], _) =
  Code_Target.produce_code @{context} false [@{const_name main}] "SML" "HelloWorld" NONE []

val target = File.tmp_path (Path.basic ("export" ^ serial_string ()))
val file = Path.append target (Path.basic "main.ML")

val cmd =
  "echo 'Super Goat 2000' | " ^
    "\"${POLYML_EXE?}\" --use " ^ Path.implode file ^
    " --eval 'HelloWorld.main ()'";

Isabelle_System.mkdirs target;
File.write file content;

val exitcode = Isabelle_System.bash cmd;

if exitcode <> 0 then
  raise (Fail ("example SML code did not run as expected, " ^
                 "exit code was " ^ (Int.toString exitcode)))
else ()
\<close>


end