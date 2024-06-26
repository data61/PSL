(*  Title:      src/Parser_Combinator.ML
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
  val real   : real parser;
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

  (* These two methods riginally resided in Isar_Interface.ML, but migrated to Parser_Combinator.ML
   * because the SeLFiE interpreter uses them but the interpreter cannot define PSL keywords multiple times.*)
  val string_parser_to_token_parser: 'a parser -> 'a Token.parser;
  val parser_to_trans_trans_parser: 'a parser -> ('a -> Toplevel.transition -> Toplevel.transition) -> (Toplevel.transition -> Toplevel.transition) Token.parser;
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
  val spaces  = many1 (sat Symbol.is_ascii_blank) >>= K (result ());
  val comment = string "(*" >>= (K (
                many (sat (fn x => x = ")" |> not))))
    >>= K (string ")")
    >>= K (result ());
  (*bracket (string "(*") (result ()) (string "*)");*)
  fun first p inp = case Seq.pull (p inp) of
    NONE        => Seq.empty
  | SOME (x, _) => Seq.single x;
  infix +++;
  fun p +++ q = first (p plus q);
  val junk    = many (spaces +++ comment) >>= K (result ());
  fun parse p = junk >>= K p >>= result;
  fun token p = p    >>= (fn v =>
                junk >>= (K (
                result v)));
  fun eval xs   = Int.fromString xs |> the;
  val nat       = many1 digit >>= (fn xs => xs |> Seq.list_of |> String.concat |> eval |> result);
  val int       =
    let
      val id  = fn inp => Seq.single (I, inp);
      val ope = symbol "-" >>= (fn _ => result ~) plus id;
    in
      token (ope >>= (fn f => (
             nat >>= (fn n =>
             f n |> result))))
    end;

  val digit_or_period = sat (fn symb => Symbol.is_digit symb orelse equal "." symb);
  (*FIXME: digit_or_period is not good enough to parse real: think about "-0.0  .something*)
  val positive_real   = many1 digit_or_period >>= (fn xs => xs |> Seq.list_of |> String.concat |> Real.fromString |> the |> result);
  val real =
    let
      val id  = fn inp => Seq.single (I, inp);
      val ope = (symbol "-" plus symbol "~") >>= (fn _ => result ((op ~):real -> real)) plus id;
    in
      token ope >>= (fn f =>
      token positive_real >>= (fn pr =>
      f pr |> result))
    end;

  infix sepby1;
  fun p sepby1 sep = p >>= (fn x =>
                    (many (sep >>= (fn _ => p >>= (fn y => result y)))) >>= (fn xs => 
                    result (Seq.cons x xs)));
  fun bracket openp p closep = token openp  >>= (fn _ =>
                               token p      >>= (fn x =>
                               token closep >>= (fn _ =>
                               result x)));
  val ints = bracket (symbol "[" |> token) (int sepby1 symbol "," |> token) (symbol "]" |> token);

  infix sepby;
  fun p sepby sep = (p sepby1 sep) plus succ_many;

  type trans_trans = Toplevel.transition -> Toplevel.transition;

  local

  fun tokens_to_string tokens = tokens |> map Token.unparse |> String.concatWith " ";

  in

  fun string_parser_to_token_parser (symbols_parser:'a parser) = (fn (tokens:Token.T list) =>
    tokens
    |> tokens_to_string
    |> Symbol.explode
    |> symbols_parser
    |> Seq.hd
    (*This function assumes that the string_parser consumes the entire string.*)
    |> apsnd (K ([]))) : 'a Token.parser;

  fun parser_to_trans_trans_parser (inv_p : 'a parser) (get_trans_trans : 'a -> trans_trans) =
    string_parser_to_token_parser (inv_p >>= (result o get_trans_trans)) : trans_trans Token.parser;

  end;
end;