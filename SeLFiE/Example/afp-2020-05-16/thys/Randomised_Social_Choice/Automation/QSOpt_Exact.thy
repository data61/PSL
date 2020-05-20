theory QSOpt_Exact
imports Complex_Main
begin

(*ML_file "rat.ML"*)

ML \<open>

signature RAT_UTILS =
sig
  val rat_to_string : Rat.rat -> string
  val pretty_rat : Rat.rat -> string
  val string_to_rat : string -> Rat.rat option
  val mk_rat_number : typ -> Rat.rat -> term
  val dest_rat_number : term -> Rat.rat
end

structure Rat_Utils : RAT_UTILS =
struct

fun rat_to_string r =
  case Rat.dest r of
    (a, 1) => Int.toString a
  | (a, b) => (if a < 0 then "~ " else "") ^ Int.toString (abs a) ^ " / " ^ Int.toString b

fun pretty_rat r =
  case Rat.dest r of
    (a, 1) => (if a < 0 then "-" else "") ^ Int.toString a
  | (a, b) => (if a < 0 then "- " else "") ^ Int.toString (abs a) ^ " / " ^ Int.toString b

fun string_to_rat s =
  let
    val (s1, s2') = s |> Substring.full |> Substring.splitl (fn x => x <> #"/") 
    val (s1, s2) = (s1, s2') |> apsnd (Substring.triml 1) |> apply2 Substring.string
  in
    if Substring.isEmpty s2' then
      Option.map Rat.of_int (Int.fromString s1)
    else
      Option.mapPartial (fn x => Option.map (fn y => Rat.make (x, y)) 
        (Int.fromString s2)) (Int.fromString s1)
  end

fun dest_num x = 
  case x of 
    Const (@{const_name "Code_Numeral.int_of_integer"}, _) $ x => dest_num x
  | _ => HOLogic.dest_number x

fun dest_rat_number t =
  case t of 
    (Const (@{const_name "Rings.divide_class.divide"},_)) $ a $ b
      => Rat.make (snd (dest_num a), snd (dest_num b))
  | (Const (@{const_name "Groups.uminus_class.uminus"},_)) $ a 
      => ~ (dest_rat_number a)
  | (Const (@{const_name "Rat.field_char_0_class.of_rat"},_)) $ a => dest_rat_number a
  |  (Const (@{const_name "Rat.Frct"}, _) $ (Const (@{const_name "Product_Type.Pair"}, _) $ a $ b))
      => Rat.make (snd (dest_num a), snd (dest_num b))
  | _ => Rat.of_int (snd (dest_num t));

fun mk_rat_number ty r =
  case Rat.dest r of
    (a, 1) => HOLogic.mk_number ty a
  | (a, b) => 
      Const (@{const_name Rings.divide_class.divide}, ty --> ty --> ty) $ 
        HOLogic.mk_number ty a $ HOLogic.mk_number ty b

end

\<close>

ML \<open>

signature LP_PARAMS =
sig

type T
val print : T -> string
val read : string -> T option
val compare : (T * T) -> General.order
val negate : T -> T
val from_int : int -> T

end;

signature LINEAR_PROGRAM_COMMON =
sig
  exception QSOpt_Parse
  datatype 'a infty = Finite of 'a | Pos_Infty | Neg_Infty;
  datatype comparison = LEQ | EQ | GEQ
  datatype optimization_mode = MAXIMIZE | MINIMIZE
  datatype 'a result = Optimal of 'a * (string * 'a) list | Unbounded | Infeasible | Unknown
  type var = string
  type 'a bound = 'a infty * var * 'a infty
  type 'a linterm = ('a * var) list
  type 'a constraint = 'a linterm * comparison * 'a
  type 'a prog = optimization_mode * 'a linterm * 'a constraint list * 'a bound list
  
  val is_finite : 'a infty -> bool
  val map_infty : ('a -> 'b) -> 'a infty -> 'b infty

  val print_infty : ('a -> string) -> 'a infty -> string
  val print_comparison : comparison -> string
  val print_optimization_mode : optimization_mode -> string
  
  val gen_print_bound : ('a -> string) -> 'a bound -> string
  val gen_print_linterm :
    (('a * 'a -> General.order) * (int -> 'a) * ('a -> string) * ('a -> 'a)) -> 
    'a linterm -> string
  val gen_print_constraint :
    (('a * 'a -> General.order) * (int -> 'a) * ('a -> string) * ('a -> 'a)) -> 
    'a constraint -> string
  val gen_print_program :
    (('a * 'a -> General.order) * (int -> 'a) * ('a -> string) * ('a -> 'a)) -> 
    'a prog -> string
  val gen_read_result : (string -> 'a option) -> string -> 'a result

end;

signature LINEAR_PROGRAM =
sig
include LINEAR_PROGRAM_COMMON
type T

val print_bound : T bound -> string
val print_linterm : T linterm -> string
val print_constraint : T constraint -> string
val print_program : T prog -> string

val save_program : string -> T prog -> unit
val solve_program : T prog -> T result
val read_result : string -> T result
val read_result_file : string -> T result

end;


structure Linear_Program_Common : LINEAR_PROGRAM_COMMON =
struct

exception QSOpt_Parse
datatype 'a infty = Finite of 'a | Pos_Infty | Neg_Infty;
datatype comparison = LEQ | EQ | GEQ
datatype optimization_mode = MAXIMIZE | MINIMIZE
datatype 'a result = Optimal of 'a * (string * 'a) list | Unbounded | Infeasible | Unknown
type var = string

type 'a bound = 'a infty * var * 'a infty
type 'a linterm = ('a * var) list
type 'a constraint = 'a linterm * comparison * 'a
type 'a prog = optimization_mode * 'a linterm * 'a constraint list * 'a bound list

fun is_finite (Finite _) = true
  | is_finite _ = false

fun map_infty f (Finite x) = Finite (f x)
  | map_infty _ Pos_Infty = Pos_Infty
  | map_infty _ Neg_Infty = Neg_Infty

fun print_infty _ Neg_Infty = "-INF"
  | print_infty _ Pos_Infty = "INF"
  | print_infty f (Finite x) = f x

fun print_comparison LEQ = "<="
  | print_comparison EQ = "="
  | print_comparison GEQ = ">="

fun print_optimization_mode MINIMIZE = "MINIMIZE"
  | print_optimization_mode MAXIMIZE = "MAXIMIZE"

fun gen_print_bound _ (Neg_Infty, v, Pos_Infty) = v ^ " free"
  | gen_print_bound f (Neg_Infty, v, u) = v ^ " <= " ^ print_infty f u
  | gen_print_bound f (l, v, Pos_Infty) =  print_infty f l ^ " <= " ^ v
  | gen_print_bound f (l, v, u) = print_infty f l ^ " <= " ^ v ^ " <= " ^ print_infty f u

fun gen_print_summand (cmp, from_int, print, negate) first c v =
  let
    val neg = (cmp (c, from_int 0) = LESS)
    fun eq x = (cmp (c, x) = EQUAL)
    val one = eq (from_int 1)
    val mone = eq (from_int (~1))
    val c' =
      if first andalso one then ""
      else if first andalso mone then "- "
      else if first then print c ^ " "
      else if mone then " - "
      else if one then " + "
      else if neg then " - " ^ print (negate c) ^ " "
      else " + " ^ print c ^ " "
  in
    c' ^ v
  end

fun gen_print_linterm ops t =
  let
    val n = length t
    val print_summand = gen_print_summand ops
    fun go (c, v) (i, acc) = (i+1, print_summand (i = n) c v ^ acc)
  in
    snd (fold go (rev t) (1, ""))
  end

fun gen_print_constraint (ops as (_, _, print, _)) (lhs, cmp, rhs) = 
   gen_print_linterm ops lhs ^ " " ^ print_comparison cmp ^ " " ^ print rhs

fun gen_print_program (ops as (_, _, print, _)) (mode, obj, constrs, bnds) =
  let
    val padding = replicate_string 4 " "
    fun mk_block s f xs = (s :: map (prefix padding o f) xs)
    fun mk_block' s f xs = if null xs then [] else mk_block s f xs
    val lines =
      mk_block (print_optimization_mode mode) (gen_print_linterm ops) [obj] @
      mk_block' "ST" (gen_print_constraint ops) constrs @
      mk_block' "BOUNDS" (gen_print_bound print) bnds @ ["END", ""]
  in
    cat_lines lines
  end



exception QSOpt_Parse

fun read_status x =
  if String.isPrefix "status " x andalso not (String.isPrefix "status =" x) then
    let
      val statuses = ["OPTIMAL", "INFEASIBLE", "UNBOUNDED"]
    in
      case find_first (fn s => String.isPrefix ("status " ^ s) x) statuses of
        NONE => SOME "UNKNOWN"
      | SOME y => SOME y
    end
  else
    NONE

fun apply _ _ [] = NONE
  | apply abort f (x :: xs) =
      if abort x then
        NONE 
      else case f x of
        NONE => apply abort f xs
      | SOME y => SOME (y, xs)

fun apply_repeat abort (f : string -> 'a option) : string list -> 'a list * string list =
  let
    fun go acc xs =
      case apply abort f xs of
        NONE => (rev acc, xs)
      | SOME (y,xs) => go (y :: acc) xs
  in
    go []
  end

fun the_apply f xs = 
  case apply (K false) f xs of
    NONE => raise QSOpt_Parse
  | SOME y => y

fun apply_unit p xs =
  case apply (not o p) (K (SOME ())) xs of
    NONE => raise QSOpt_Parse
  | SOME (_, xs) => xs

fun gen_read_value read x =
  let
    val x = unprefix "Value = " x
  in
    read x
  end
    handle Fail _ => NONE

val trim =
  let
    fun chop [] = []
      | chop (l as (x::xs)) = if Char.isSpace x then chop xs else l
  in
    String.implode o chop o rev o chop o rev o String.explode
  end

fun gen_read_assignment read x : (string * 'a) option =
  x |> try (
    Substring.full 
    #> Substring.splitl (fn x => x <> #"=") 
    #> apply2 Substring.string 
    #> apsnd (unprefix "=")
    #> apply2 trim)
  |> Option.mapPartial (fn (x,y) => Option.map (fn y => (x, y)) (read y))

fun gen_read_result read s = 
  let
    val s = s |> split_lines |> map trim
    val (status, s) = the_apply read_status s
    val (result, _) =
      if status = "OPTIMAL" then
        let
          val (value, s) = the_apply (gen_read_value read) s
          val s = apply_unit (fn x => x = "VARS:") s
          val (vars, s) = apply_repeat (String.isSuffix ":") (gen_read_assignment read) s
        in
          (Optimal (value, vars), s)
        end
      else if status = "INFEASIBLE" then
        (Infeasible, s)
      else if status = "UNBOUNDED" then
        (Unbounded, s)
      else
        (Unknown, s)
  in
    result
  end


end;

functor Linear_Program(LP_Params : LP_PARAMS) : LINEAR_PROGRAM =
struct

open Linear_Program_Common;

local
  open LP_Params;
  val ops = (compare, from_int, print, negate)
in
  type T = T
  val print_bound = gen_print_bound print
  val print_linterm = gen_print_linterm ops
  val print_constraint = gen_print_constraint ops
  val print_program = gen_print_program ops
  end

  fun save_program filename prog =
    let
      val output = print_program prog
      val f = TextIO.openOut filename
      val _ = TextIO.output (f, output)
      val _ = TextIO.closeOut f
    in
      ()
    end


fun wrap s = "\""^s^"\"";

val read_result = gen_read_result LP_Params.read

fun read_result_file filename =
  let
    val f = TextIO.openIn filename
    val s = TextIO.input f
    val _ = TextIO.closeIn f
  in
    read_result s
  end

fun solve_program prog =
    let
    val name = string_of_int (Time.toMicroseconds (Time.now ()))
    val lpname = Path.implode (Path.expand (Isabelle_System.create_tmp_path name ".lp"))
    val resultname = Path.implode (Path.expand (Isabelle_System.create_tmp_path name ".sol"))
    val _ = save_program lpname prog
    val esolver_path = getenv "QSOPT_EXACT_PATH"
    val esolver = if esolver_path = "" then "esolver" else esolver_path
    val command =  wrap esolver ^ " -O " ^ wrap resultname ^ " " ^ wrap lpname
    val {err = err, rc = rc, ...} = Bash.process command
    in
      if rc <> 0 then
        raise Fail ("QSopt_exact returned with an error (return code " ^ 
          Int.toString rc ^ "):\n" ^ err)
      else
        let
            val result = read_result_file resultname
            val _ = OS.FileSys.remove lpname
            val _ = OS.FileSys.remove resultname
        in
            result
        end
    end

end

structure Rat_Linear_Program = Linear_Program(
struct

type T = Rat.rat

val print = Rat_Utils.rat_to_string
val read = Rat_Utils.string_to_rat
val compare = Rat.ord
val from_int = Rat.of_int
val negate = Rat.neg

end)

\<close>


(*
ML_val \<open>
  open Rat_Linear_Program;

  val mode = MAXIMIZE
  val goal = map (apfst Rat.from_int) [(~1, "r1"), (1, "r2")]
  fun mk_constr xs cmp rhs = (map (apfst Rat.from_int) xs, cmp, Rat.from_int rhs)
  fun mk_bnd (l, x, u) = (map_infty Rat.from_int l, x, map_infty Rat.from_int u)
  val mk_bnds = map mk_bnd
  val constr1 = mk_constr [(1, "x"), (~1, "y")] EQ 42
  val bnds = mk_bnds [(Finite (~2), "x", Pos_Infty), (Finite 0, "y", Finite 1)]
  val prog = (mode, goal, [constr1], bnds)
  val _ = writeln (print_program prog)
  val _ = save_program "/tmp/foo.lp" prog
\<close> *)

end
