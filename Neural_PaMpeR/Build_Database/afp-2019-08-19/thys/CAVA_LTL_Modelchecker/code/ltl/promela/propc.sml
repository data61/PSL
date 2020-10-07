structure Propc : sig 
  datatype binOp = Eq | Le | LEq | Gr | GEq;

  datatype ident = Ident of string * IntInf.int option;

  datatype propc = CProp of ident
                 | BProp of binOp * ident * ident
                 | BExpProp of binOp * ident * IntInf.int;
  
  val propcToString : propc -> string;
end = struct
  open PromelaLTLConv;

  fun opToString Eq = "="
    | opToString Le = "<"
    | opToString LEq = "=<"
    | opToString Gr = ">"
    | opToString GEq = ">="

  fun identToString (Ident (name, NONE)) = name
    | identToString (Ident (name, SOME i)) = name ^ "[" ^ IntInf.toString i ^ "]"

  fun propcToString (CProp ident) = identToString ident
    | propcToString (BProp (bop,li,ri)) = 
        identToString li ^ " " ^ opToString bop ^ " " ^ identToString ri
    | propcToString (BExpProp (bop,li,re)) = 
        identToString li ^ " " ^ opToString bop ^ " " ^ IntInf.toString re
end;

