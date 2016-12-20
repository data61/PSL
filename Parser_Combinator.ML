(*  Title:      Parser_Combinator.ML
    Author:     Yutaka Nagashima, Data61, CSIRO

Monadic Parser Combinators described by Graham Hutton and Erik Meijer in 1996.
Note that the smallest textual unit in Isabelle is Symbol.symbol.
*)

(*** PARSER_COMBINATOR: monadic parser combinators ***)
signature PARSER_COMBINATOR =
sig
  type symbols = Symbol.symbol list;
  type 'a parser = symbols -> ('a * symbols) Seq.seq;
  val result : 'a -> 'a parser;
  val zero   : 'a parser;
  val bind   : 'a parser -> ('a -> 'b parser) -> 'b parser;
  val >>=    : 'a parser * ('a -> 'b parser) -> 'b parser;
  val item   : Symbol.symbol parser;
  val sat    : (Symbol.symbol -> bool) -> Symbol.symbol parser;
  val symbol : Symbol.symbol -> Symbol.symbol parser;
  val digit  : Symbol.symbol parser;
  val lower  : Symbol.symbol parser;
  val upper  : Symbol.symbol parser;
  val plus   : ('a parser * 'a parser) -> 'a parser;
  (*_ is considered as a letter following the Isabelle convention.*)
  val letter : Symbol.symbol parser;
  val alphanum : Symbol.symbol parser;
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

(*** Parser_Combinator: monadic parser combinators ***)
structure Parser_Combinator : PARSER_COMBINATOR =
struct
  type symbols              = Symbol.symbol list;
  type 'a parser            = symbols -> ('a * symbols) Seq.seq;
  fun result v              = fn inp => Seq.single (v, inp);
  val zero                  = fn _   => Seq.empty;
  fun bbind xs func         = Seq.flat (Seq.map func xs);
  fun bind p f inp          =  bbind (p inp) (fn (result1, state1) => f result1 state1);
  fun item (inp:symbols)     = case inp of
      []      => Seq.empty
    | (x::xs) => Seq.single (x, xs:symbols);
  fun sat p    = bind item (fn x => if p x then result x else zero);
  fun symbol x = sat (fn y => x = y);
  val digit    = sat Symbol.is_digit;
  val lower    = sat Symbol.is_ascii_lower;
  val upper    = sat Symbol.is_ascii_upper;
  infix plus;
  fun p plus q = fn inp => Seq.append (p inp) (q inp);
  val letter   = sat (fn sym => Symbol.is_ascii_letter sym orelse Symbol.is_ascii_quasi sym);
  val alphanum = letter plus digit;
  infix >>=;
  fun m >>= f = bind m f;
  fun word' _ =
    let
      (*Unlike Hutton and Meijer, I think numerals constitute a word.*)
      val neWord = alphanum >>= (fn x =>
                   word' () >>= (fn xs =>
                   result (x ^ xs)))
    in
      neWord plus result ""
   end : string parser;
  val word       = word' () plus result "";
  fun string' [] = result ""
   |  string' (x::xs) = symbol x   >>= (fn _ =>
                        string' xs >>= (fn _ =>
                        (x::xs) |> String.concat |> result));
  fun string xs = xs |> Symbol.explode |> string';
  val succ_many = (fn inp => Seq.single (Seq.empty, inp)) : 'a Seq.seq parser;
  fun many p    = p >>= (fn x => many p >>= (fn xs => result (Seq.cons x xs))) plus succ_many;
  val ident     = lower >>= (fn x =>
                  many alphanum >>= (fn xs =>
                  result (Seq.cons x xs |> Seq.list_of |> String.concat)));
  fun many1 p   = p >>= (fn x => many p >>= (fn xs => result (Seq.cons x xs)));
  fun eval xs   = Int.fromString xs |> the;
  val nat       = many1 digit >>= (fn xs => xs |> Seq.list_of |> String.concat |> eval |> result);
  val int       =
    let
      val id  = fn inp => Seq.single (I, inp);
      val ope = symbol "-" >>= (fn _ => result ~) plus id;
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
  val ints = bracket (symbol "[") (int sepby1 symbol ",") (symbol "]");
  infix sepby;
  fun p sepby sep = (p sepby1 sep) plus succ_many;

  fun first p inp = case Seq.pull (p inp) of
    NONE        => Seq.empty
  | SOME (x, _) => Seq.single x;
  infix +++;
  fun p +++ q = first (p plus q);
  val spaces  = many1 (sat Symbol.is_space) >>= K (result ());
  val comment = string "(*" >>= (K (
                many (sat (fn x => x = ")" |> not))))
    >>= K (string ")")
    >>= K (result ());
  (*bracket (string "(*") (result ()) (string "*)");*)
  val junk    = many (spaces +++ comment) >>= K (result ());
  fun parse p = junk >>= K p >>= result;
  fun token p = p    >>= (fn v =>
                junk >>= (K (
                result v)));
end;