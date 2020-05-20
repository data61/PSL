structure Propc : sig 
  datatype propc = CProp of string
                 | FProp of (string * IntInf.int);

  val propcToString : propc -> string;
end = struct
  open BoolProgs_LTL_Conv;

  fun propcToString (CProp s) = s 
    | propcToString (FProp (s, i)) = s ^ " " ^ IntInf.toString i
end;
