theory HelloWorld
  imports IO
begin

section\<open>Hello, World!\<close>

text\<open>
  The idea of a \<^term>\<open>main :: unit io\<close> function is that, upon start of your program, you will be
  handed a value of type \<^typ>\<open>\<^url>\<close>. You can pass this world through your code and modify it.
  Be careful with the \<^typ>\<open>\<^url>\<close>, it's the only one we have.
\<close>


text\<open>The main function, defined in Isabelle. It should have the right type in Haskell.\<close>
definition main :: "unit io" where
  "main \<equiv> do {
               _ \<leftarrow> println (STR ''Hello World! What is your name?'');
               name \<leftarrow> getLine;
               println (STR ''Hello, '' + name + STR ''!'')
             }"


section\<open>Generating Code\<close>

text\<open>Checking that the generated code compiles.\<close>
export_code main checking Haskell? SML


ML_val\<open>Isabelle_System.bash "echo ${ISABELLE_TMP} > ${ISABELLE_TMP}/self"\<close>
text\<open>
During the build of this session, the code generated in the following subsections will be
written to
\<close>
text_raw\<open>\verbatiminput{${ISABELLE_TMP}/self}\<close>


subsection\<open>Haskell\<close>

export_code main in Haskell file "$ISABELLE_TMP/exported_hs"

text\<open>The generated helper module \<^file>\<open>$ISABELLE_TMP/exported_hs/StdIO.hs\<close> is shown below.\<close>
text_raw\<open>\verbatiminput{$ISABELLE_TMP/exported_hs/StdIO.hs}\<close>
 
text\<open>The generated main file \<^file>\<open>$ISABELLE_TMP/exported_hs/HelloWorld.hs\<close> is shown below.\<close>
text_raw\<open>\verbatiminput{$ISABELLE_TMP/exported_hs/HelloWorld.hs}\<close>


subsection\<open>SML\<close>

export_code main in SML file "$ISABELLE_TMP/exported.sml"

text\<open>The generated SML code in \<^file>\<open>$ISABELLE_TMP/exported.sml\<close> is shown below.\<close>
text_raw\<open>\verbatiminput{$ISABELLE_TMP/exported.sml}\<close>


end