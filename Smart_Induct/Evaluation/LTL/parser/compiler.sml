signature PROP_LTL =
sig
  exception ParseError;
  val parse : int -> (int -> string) -> (string * int * int -> unit) -> string Ltl_Dt.ltlc;
end

functor Ltl (PLTL : PROP_LTL) : sig 
      val compile_from_file : string -> string Ltl_Dt.ltlc;
      val compile_from_string : string -> string Ltl_Dt.ltlc;
      val toString : string Ltl_Dt.ltlc -> string;
      exception LtlError of string;
end = struct

exception LtlError of string;

local
  open Ltl_Dt
in
  fun toString True_ltlc = "true"
    | toString False_ltlc = "false"
    | toString (Prop_ltlc p) = p
    | toString (Not_ltlc f) = "(" ^ "~ " ^ toString f ^ ")"
    | toString (And_ltlc (fl,fr)) = "(" ^ (toString fl) ^ " & " ^ (toString fr) ^ ")"
    | toString (Or_ltlc (fl,fr)) = "(" ^ (toString fl) ^ " | " ^ (toString fr) ^ ")"
    | toString (Implies_ltlc (fl,fr)) = "(" ^ (toString fl) ^ " --> " ^ (toString fr) ^ ")"
    | toString (Next_ltlc f) = "(" ^ "X " ^ toString f ^ ")"
    | toString (Final_ltlc f) = "(" ^ "F " ^ toString f ^ ")"
    | toString (Global_ltlc f) = "(" ^ "G " ^ toString f ^ ")"
    | toString (Until_ltlc (fl,fr)) = "(" ^ (toString fl) ^ " U " ^ (toString fr) ^ ")"
    | toString (Release_ltlc (fl,fr)) = "(" ^ (toString fl) ^ " R " ^ (toString fr) ^ ")"
    | toString (WeakUntil_ltlc (fl,fr)) = "(" ^ (toString fl) ^ " W " ^ (toString fr) ^ ")"
    | toString (StrongRelease_ltlc (fl,fr)) = "(" ^ (toString fl) ^ " M " ^ (toString fr) ^ ")";
end

fun compile grab =
  let 
    val maxLookAhead = 0 (* no error correction *)
    fun printError (msg,pos,_) = 
      let val posS = if pos = ~1 then "" else "(Pos "^Int.toString pos^") "
      in
        print (posS^msg^"\n")
      end
  in
    PLTL.parse maxLookAhead grab printError
    handle PLTL.ParseError => raise LtlError "Parsing error"
  end

fun compile_from_string str =
  let
    val substr = ref (Substring.full str)
    fun grab n = 
      if Substring.size (!substr) < n then
        let val s = !substr
        in
          substr := Substring.full "";
          Substring.string s
        end
      else
        let val (sl, sr) = Substring.splitAt(!substr, n)
        in
          substr := sr;
          Substring.string sl
        end
  in
    compile grab
  end

fun compile_from_file fileName =
  let 
    val inStream = TextIO.openIn fileName
    fun grab n =
      if TextIO.endOfStream inStream then ""
      else TextIO.inputN (inStream,n)
    val tree = compile grab
  in 
    TextIO.closeIn inStream;
    tree
  end
end;
