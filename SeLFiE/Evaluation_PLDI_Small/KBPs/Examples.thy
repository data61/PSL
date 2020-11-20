(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory Examples
imports
  MuddyChildren
  Robot
  "HOL-Library.AList_Mapping"
begin

(* Just verify that code generation works. *)

export_code
  "mc_ClockDFS"
  "mc_ClockAlg"
  "mc_SPRDFS"
  "mc_SPRAlg"

  "robot_ClockDFS"
  "robot_ClockAlg"
  "robot_SPRSingleDFS"
  "robot_SPRSingleAlg"
in Haskell (string_classes)

end
(*>*)
