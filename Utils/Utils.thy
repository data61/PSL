(* This file provides utility functions that are not specific to Isabelle/HOL. *)
theory Utils
imports Main
begin

ML{* signature UTILS =
sig
  val flip           : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c;
  val delay          : ('a -> 'b) * 'a -> 'b;
  val map_arg        : 'a -> ('a -> 'b) list -> 'b list;
  (* map_pair and pair_to_list are useful only if the pair consists of the same type.*)
  val map_pair       : ('a -> 'b) -> 'a * 'a -> 'b * 'b;
  val pair_to_list   : 'a * 'a -> 'a list;
  val list_to_pair   : 'a list -> 'a * 'a;
  val init           : 'a list -> 'a list;
  val intersperse    : 'a -> 'a list -> 'a list;
  val is_in_paren    : string -> bool;
  val ??             : ('a -> bool) * ('a -> 'a) -> 'a -> 'a;
  val rm_parentheses_with_contents_in_the_end : string -> string;
  val rm_parentheses : string -> string;
  val remove__s      : string -> string;
  val push_to_front  : string -> string list -> string list;
  val the'           : string -> 'a option -> 'a;
  val prefix_if_nonempty : string -> string list -> string list;
  val debug          : bool; (* flag for debugging.*)
end;
*}

ML{* structure Utils:UTILS =
struct
  fun flip f x y = f y x;

  infix delay;
  fun (f delay x) =  f x;

  (* map_arg maps a parameter to a list of functions*)
  fun map_arg _      []           = []
   |  map_arg param (func::funcs) = func param :: map_arg param funcs;

  fun map_pair func (a, b) = (func a, func b);

  fun pair_to_list (x, y) = [x, y];

  fun list_to_pair [a,b] = (a,b)
   |  list_to_pair _ = error "list_to_pair failed. The length of lsit is not two.";

  fun init [] = error "init failed. empty list"
   |  init xs = take (length xs - 1) xs;

  fun intersperse _   []      = []
   |  intersperse _   (x::[]) = [x]
   |  intersperse int (x::xs) = x::int::intersperse int xs

  fun is_in_paren str = String.isPrefix "(" str;

  fun rm_parentheses_with_contents_in_the_end str =
    let
      val tokens = Symbol.explode str;
      val parser = Scan.repeat (Scan.unless ($$ "(" ) (Scan.one Symbol.not_eof));
      val result = Scan.finite Symbol.stopper parser tokens |> fst |> String.concat;
    in
      result
    end;

  infix ??;
  fun ass ?? f = fn x => if ass x  then f x else x;

  fun rm_parentheses str = (is_in_paren ?? unenclose) str;

  fun remove__s name =
    let
      val suffix_is__ = String.isSuffix "_" name;
      val remove_     = unsuffix "_";
      val wo__s       = (suffix_is__ ? (remove__s o remove_)) name
    in
      wo__s
    end;

  fun push_to_front key things = 
    filter     (String.isSubstring key) things @
    filter_out (String.isSubstring key) things;

  fun the' (mssg:string)  NONE        = error mssg
   |  the' (_   :string) (SOME thing) = thing

  fun prefix_if_nonempty _        [] = []
   |  prefix_if_nonempty prefixed xs = prefixed :: xs : string list;

  val debug = false;
end;
*}

end