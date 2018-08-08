(*  Title:      MiLkMaId/MiLkMaId_Util.thy
    Author:     Yutaka Nagashima, CIIRC, CTU

This file defines utility functions for MiLkMaId.
*)

theory MiLkMaId_Util
  imports Main
begin

(* To avoid concurrent write access to shared resources,
   We should output each line to a temporary file. Then, merge them using a bash script.
   We can combine these files with "cat * > all". *)

(* How to write a line to a new unique file? *)
ML{* fun get_new_path x = File.platform_path (Resources.master_directory @{theory}) ^ "/temp/" ^ serial_string x;
(* example *)
val message = "My line is this.\n";
Isabelle_System.bash ("echo -n '" ^ message ^ "' > " ^ (get_new_path ()));
*}

end