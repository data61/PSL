(* Monadic Parser Combinators described by Graham Hutton and Erik Meijer in 1996. *)
(* Note that the type string is not a type synonym of "char list" in ML.          *)
theory Parser_Combinator
imports Main
begin

ML{* signature PARSER_COMBINATOR =
sig
  type 'a parser = string -> ('a * string) Seq.seq;
  val result : 'a -> 'a parser;
  val zero   : 'a parser;
  val bind   : 'a parser -> ('a -> 'b parser) -> 'b parser;
  val >>=    : 'a parser * ('a -> 'b parser) -> 'b parser;
(*  val update : (string -> string) -> string -> (string * string) list;*)
  val item   : char parser;
  val sat    : (char -> bool) -> char parser;
  val char   : char -> char parser;
  val digit  : char parser;
  val lower  : char parser;
  val upper  : char parser;
  val plus   : ('a parser * 'a parser) -> 'a parser;
  (* _ is considered as a letter following the Isabelle convention.*)
  val letter : char parser;
  val alphanum : char parser;
  val word   : string parser;
  val string : string -> string parser;
  val many   : 'a parser -> 'a Seq.seq parser;
  val ident  : string parser;
  val many1  : 'a parser -> 'a Seq.seq parser;
  val nat    : int parser;
  val int    : int parser;
  val sepby1 : 'a parser * 'b parser -> 'a Seq.seq parser;
  val bracket: 'a parser -> 'b parser -> 'c parser -> 'b parser;
  val ints   : int Seq.seq parser;
  val sepby  : 'a parser * 'b parser -> 'a Seq.seq parser;
  
  val first  : 'a parser -> 'a parser;
  val +++    : 'a parser * 'a parser -> 'a parser;
  val spaces : unit parser;
  val comment: unit parser;
  val junk   : unit parser;
  val parse  : 'a parser -> 'a parser;
  val token  : 'a parser -> 'a parser;
end;
*}

ML{* structure Parser_Combinator : PARSER_COMBINATOR =
struct
  type 'a parser            = string -> ('a * string) Seq.seq;
  fun result v              = fn inp => Seq.single (v, inp);
  val zero                  = fn _   => Seq.empty;
  fun bbind xs func         = Seq.flat (Seq.map func xs);
  fun bind p f (inp:string) =  bbind (p inp) (fn (result1, state1) => f result1 state1);
(*  fun update (f:string -> string) = fn s => [(s, f s)];*)
  fun item (inp:string)     = case String.explode inp of
      []      => Seq.empty
    | (x::xs) => Seq.single (x, String.implode xs);
  fun sat p    = bind item (fn x => if p x then result x else zero);
  fun char x   = sat (fn y => x = y);
  val digit    = sat Char.isDigit;
  val lower    = sat Char.isLower;
  val upper    = sat Char.isUpper;
  infix plus;
  fun p plus q = fn inp => Seq.append (p inp) (q inp);
  val letter   = sat (fn cha => Char.isAlpha cha orelse #"_" = cha);
  val alphanum = letter plus digit;
  infix >>=;
  fun m >>= f = bind m f;
  fun word' _ = 
    let
      val neWord = letter   >>= (fn x =>
                   word' () >>= (fn xs =>
                   result (Char.toString x ^ xs)))
    in
      neWord plus result ""
   end : string parser ;
  val word       = word' () plus result "";
  fun string' [] = result ""
   |  string' (x::xs) = char x     >>= (fn _ =>
                        string' xs >>= (fn _ =>
                        (x::xs) |> String.implode |> result));
  fun string xs = xs |> String.explode |> string';
  val succ_many = (fn inp => Seq.single (Seq.empty, inp)) : 'a Seq.seq parser;
  fun many p    = p >>= (fn x => many p >>= (fn xs => result (Seq.cons x xs))) plus succ_many;
  val ident     = lower >>= (fn x => 
                  many alphanum >>= (fn xs => 
                  result (Seq.cons x xs |> Seq.list_of |> String.implode)));
  fun many1 p   = p >>= (fn x => many p >>= (fn xs => result (Seq.cons x xs)));
  fun eval xs   = Int.fromString xs |> the;
  val nat       = many1 digit >>= (fn xs => xs |> Seq.list_of |> String.implode |> eval |> result);
  val int       =
    let
      val id  = fn inp => Seq.single (I, inp);
      val ope = (char #"-" >>= (fn _ => result ~)) plus id;
    in
      ope >>= (fn f => (nat >>= (fn n => f n |> result)))
    end;
  infix sepby1;
  fun p sepby1 sep = p >>= (fn x => 
                    (many (sep >>= (fn _ => p >>= (fn y => result y)))) >>= (fn xs => 
                    result (Seq.cons x xs)));
  fun bracket openp p closep = openp  >>= (fn _ =>
                               p      >>= (fn x =>
                               closep >>= (fn _ =>
                               result x)));
  val ints = bracket (char #"[") (int sepby1 char #",") (char #"]");
  infix sepby;
  fun p sepby sep = (p sepby1 sep) plus succ_many;

  fun first p inp = case Seq.pull (p inp) of
    NONE        => Seq.empty
  | SOME (x, _) => Seq.single x;
  infix +++;
  fun p +++ q = first (p plus q);
  val spaces  = many1 (sat Char.isSpace) >>= K (result ());
  val comment = string "(*" >>= (K (
                many (sat (fn x => Char.toCString x = ")" |> not)))) 
    >>= K (string ")")
    >>= K (result ());
  (*bracket (string "(*") (result ()) (string "*)");*)
  val junk    = many (spaces +++ comment) >>= K (result ());
  fun parse p = junk >>= K p >>= result;
  fun token p = p    >>= (fn v =>
                junk >>= (K (
                result v)));
end;
*}

end