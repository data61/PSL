(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
License: LGPL
*)

section \<open>Generating Code for the Solver\<close>

theory Solver_Code
  imports Algorithm
begin

external_file \<open>src/Main.hs\<close>

export_code solve checking Haskell \<comment> \<open>test whether Haskell code generation works\<close>

export_code solve integer_of_nat nat_of_integer in Haskell module_name HLDE file_prefix generated

compile_generated_files \<^marker>\<open>contributor Makarius\<close>
  \<open>code/generated/HLDE.hs\<close>
  external_files \<open>Main.hs\<close> (in src)
  export_files \<open>hlde\<close> (exe)
  export_prefix \<open>code/generated\<close>
  where \<open>fn dir =>
    let
      val exec = Generated_Files.execute dir;
      val _ =
        exec \<open>Compilation\<close> ("mv code/generated/HLDE.hs . && " ^
          File.bash_path \<^path>\<open>$ISABELLE_GHC\<close> ^ " -o hlde Main.hs");

      val print_coeffs = enclose "[" "]" o commas o map string_of_int;
      fun print_hlde (xs, ys) =
        writeln (exec \<open>Test\<close> ("./hlde <<< '(" ^ print_coeffs xs ^ ", " ^ print_coeffs ys ^ ")'"));
    in print_hlde ([3, 5, 1], [2, 7]) end
\<close>

end
