section \<open>Build and test exported program with MLton\<close>

theory Complementation_Build
imports Complementation_Final
begin

external_file \<open>code/Autool.mlb\<close>
external_file \<open>code/Prelude.sml\<close>
external_file \<open>code/Autool.sml\<close>

compile_generated_files \<^marker>\<open>contributor Makarius\<close>
  \<open>code/Complementation.ML\<close> (in Complementation_Final)
  external_files
    \<open>code/Autool.mlb\<close>
    \<open>code/Prelude.sml\<close>
    \<open>code/Autool.sml\<close>
  export_files \<open>code/Complementation.sml\<close> and \<open>code/Autool\<close> (exe)
  where \<open>fn dir =>
    let
      val exec = Generated_Files.execute (Path.append dir (Path.basic "code"));
      val _ = exec \<open>Prepare\<close> "mv Complementation.ML Complementation.sml";
      val _ = exec \<open>Compilation\<close> (File.bash_path \<^path>\<open>$ISABELLE_MLTON\<close> ^
            " -profile time -default-type intinf Autool.mlb");
      val _ = exec \<open>Test\<close> "./Autool help";
    in () end\<close>

end