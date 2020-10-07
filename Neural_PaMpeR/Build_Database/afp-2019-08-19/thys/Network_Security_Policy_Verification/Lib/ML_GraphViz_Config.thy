theory ML_GraphViz_Config
imports Main
begin

ML\<open>

signature GRAPHVIZ_PLATFORM_CONFIG =
sig
  val executable_dot: string;
  val executable_pdf_viewer: string;
end

structure Graphviz_Platform_Config: GRAPHVIZ_PLATFORM_CONFIG =
struct
  (*Change your system config here*)
  val (executable_dot: string, executable_pdf_viewer: string) = (
            case getenv "ISABELLE_PLATFORM_FAMILY" of
                  "linux" => ("dot", getenv "PDF_VIEWER") (*tested on ubuntu 14.04, graphviz 2.36*)
                 | "macos" => ("dot", getenv "PDF_VIEWER")
                 | "windows" => ("dot", getenv "PDF_VIEWER") (*tested with graphviz-2.38.msi, works, needed to add the bin directory to $PATH manually*)
                 | _ => raise Fail "$ISABELLE_PLATFORM_FAMILY: cannot determine operating system"
            );
  
  local
    fun check_executable e =
      if Isabelle_System.bash ("which "^e) = 0 then
        () (* `which` already printed the path *)
      else 
       warning ("Command not available or not in $PATH: "^e);
  in
    val _ = check_executable executable_pdf_viewer;
    val _ = check_executable executable_dot;
  end

end
\<close>

end
