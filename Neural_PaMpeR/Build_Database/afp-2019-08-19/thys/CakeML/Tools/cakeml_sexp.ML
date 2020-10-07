(*  Title:      CakeML/Tools/cakeml_sexp.ML
    Author:     Johannes Åman Pohjola

Printing of CakeML ASTs as S-expressions, for interfacing with
the bootstrapped CakeML compiler.

Originally developed for HOL4 by Nicholas Coughlin, ported to
Isabelle/ML by Johannes Åman Pohjola.
*)

signature CAKEML_SEXP =
sig
  val print_prog_buf: (string -> unit) -> term -> unit
  val print_prog: term -> string
end;

structure CakeML_Sexp : CAKEML_SEXP =
struct

val IntLit_tm = @{const "IntLit"}
val CharLit_tm = @{const "Char"}
val Word8_tm = @{const "Word8"}
val Word64_tm = @{const "Word64"}
val W8_tm = @{const "W8"}
val W64_tm = @{const "W64"}
val Shift_tm = @{term "Shift"}
val WordToInt_tm = @{term "WordToInt"}
val WordFromInt_tm = @{term "WordToInt"}
val FFI_tm = @{term "FFI"}
val Pvar_tm = @{term "Pvar"}
val Pany_tm = @{term "Pany"}
val Lit_tm = @{const "Lit"}
val Plit_tm = @{term "Plit"}
val App_tm = @{const "App"}

fun same_name (Const (c,_),Const (c',_)) = c = c'
  | same_name (a,b) = a = b

datatype exp = exp_tuple of exp list | exp_list of exp list | exp_str of string;

fun escape_wrap c = "\"" ^ c ^ "\""
fun escape_char c =
  let
    val to_hex = (StringCvt.padLeft #"0" 2) o (Int.fmt StringCvt.HEX) o Char.ord
  in
    if c = #"\\" then "\\\\\\\\"
    else if c = #"\"" then "\\\""
    else if Char.isPrint c then Char.toString c
    else "\\\\" ^ (to_hex c)
  end

val fromHOLchar =
  escape_wrap o String.translate escape_char o chr o HOLogic.dest_char;
val fromHOLstring =
  escape_wrap o (String.translate escape_char) o HOLogic.dest_string;
val fromHOLnum = Int.toString o snd o HOLogic.dest_number;

fun char_to_exp c = exp_list [exp_str "char", exp_str (fromHOLchar c)]
val string_to_exp = exp_str o fromHOLstring;
val num_to_exp = exp_str o fromHOLnum;

fun word_to_exp lit_name w =
    exp_list [exp_str lit_name, num_to_exp w]

fun int_to_exp i =
  let
    val n = (snd o HOLogic.dest_number) i
  in
    if n < 0
      then exp_list [exp_str "-", exp_str(Int.toString(abs n))]
      else num_to_exp i
  end

fun dest_loc(Const (@{const_name make_locn}, _) $ l1 $ l2 $ l3) =
  (HOLogic.dest_number l1 |> snd,
   HOLogic.dest_number l2 |> snd,
   HOLogic.dest_number l3 |> snd)
  | dest_loc _ = raise Domain

fun dest_locs (Const (@{const_name Pair}, _) $ loc1 $ loc2) =
 let val (r1,c1,o1) = dest_loc loc1
     val (r2,c2,o2) = dest_loc loc2
 in
   [r1,c1,o1,r2,c2,o2]
 end
  | dest_locs t = raise TERM ("locs", [t])

fun locs_to_exp l =
  exp_list [exp_str ((String.concatWith " " o map Int.toString) l)]

fun lit_to_exp t =
  let
    val (x, xs) = strip_comb t
    val h = hd xs
  in
    if (curry same_name) x IntLit_tm then int_to_exp h
    else if (curry same_name) x CharLit_tm then char_to_exp h
    else if (curry same_name) x Word8_tm then word_to_exp "word8" h
    else if (curry same_name) x Word64_tm then word_to_exp "word64" h
    else string_to_exp h
  end

fun op_to_exp arg =
  let
    val underscore_filter =
      String.implode o filter (fn n => n <> #"_") o String.explode
    val to_string = #1 o dest_Const
    fun filtered_string t =
      if same_name(W8_tm,t) then
        "8"
      else if same_name(W64_tm,t) then
        "64"
      else underscore_filter(Long_Name.base_name(to_string t))
    fun wordInt xs s = exp_str ((hd (map to_string xs)) ^ s)
    fun ffi xs = exp_tuple [exp_str "FFI", string_to_exp (hd xs)]
    fun shift xs =
      let
        val consts = List.take (xs, 2)
        val str = "Shift" ^ String.concat (map filtered_string consts)
      in
        exp_tuple [exp_str str, num_to_exp (List.last xs)]
      end
    val (x, xs) = strip_comb arg
  in
    if (curry same_name) x Shift_tm then shift xs
    else if (curry same_name) x WordToInt_tm then wordInt xs "toInt"
    else if (curry same_name) x WordFromInt_tm then wordInt xs "fromInt"
    else if (curry same_name) x FFI_tm then ffi xs
    else exp_str (String.concat (map filtered_string (x::xs)))
  end

val cons = @{term "Cons"};
val comma = @{term "Pair"};
val nil_l = @{term "[]"}
fun ast_to_exp term =
  let 
    val list_to_exp = map ast_to_exp
    fun app_to_exp const args =
      let
        val exp = (exp_str o Long_Name.base_name o #1 o dest_Const) const
        val op_exp = op_to_exp (hd args)
        val args_exp = list_to_exp (tl args)
      in
        exp_list (exp::op_exp::args_exp)
      end
    fun upc "Some" = "SOME"
      | upc "None" = "NONE"
      | upc s = s
    fun generic_to_exp const args =
      let
        val exp = (exp_str o upc o Long_Name.base_name o #1 o dest_Const) const
        val args_exp = list_to_exp args
      in 
        case args of [] => exp
                   | _ => exp_list (exp::args_exp)
      end
    fun cons_to_exp term =
      if can HOLogic.dest_string term
        then string_to_exp term
        else (exp_list o list_to_exp o HOLogic.dest_list) term
    val tuple_to_exp =
      exp_tuple o list_to_exp o HOLogic.strip_tuple
    val (x, xs) = strip_comb term
  in
    if (curry same_name) x Pvar_tm then ast_to_exp (hd xs)
    else if (curry same_name) x Pany_tm then exp_list [exp_str "Pany"]
    else if (curry same_name) x Lit_tm then
      exp_list [exp_str "Lit", lit_to_exp (hd xs)]
    else if (curry same_name) x Plit_tm then
      exp_list [exp_str "Plit", lit_to_exp (hd xs)]
    else if can dest_locs term then (locs_to_exp o dest_locs) term
    else if (curry same_name) x nil_l then exp_list []
    else if (curry same_name) x cons then cons_to_exp term
    else if (curry same_name) x comma then tuple_to_exp term
    else if (curry same_name) x App_tm then app_to_exp x xs
    else generic_to_exp x xs
  end

fun exp_to_string e =
  let
    val list_to_string =
      (String.concatWith " ") o (map exp_to_string)
    fun tuple_to_string t =
      case t of [] => ""
              | [x, exp_list l] => (exp_to_string x) ^ " " ^ (list_to_string l)
              | [x, y] => (exp_to_string x) ^ " . " ^ (exp_to_string y)
              | x::xs => (exp_to_string x) ^ " " ^ (tuple_to_string xs)
  in
    case e of exp_str s => s
            | exp_tuple l => "(" ^ (tuple_to_string l) ^ ")"
            | exp_list [] => "nil"
            | exp_list l => "(" ^ (list_to_string l) ^ ")"
  end

fun print_prog_buf pf prog =
  let
    val out = pf o exp_to_string o ast_to_exp
    fun step pl =
      case pl of [] => ()
               | [x] => out x
               | x::xs => (out x; pf " "; step xs)
    val _ = pf "("
    val pl = HOLogic.dest_list prog
    val _ = step pl
  in
    pf ")"
  end

fun print_prog prog =
  let
    val buf = Unsynchronized.ref Buffer.empty
    fun pf s = Unsynchronized.change buf (Buffer.add s)
    val _ = print_prog_buf pf prog
  in
    Buffer.content (!buf)
  end

end