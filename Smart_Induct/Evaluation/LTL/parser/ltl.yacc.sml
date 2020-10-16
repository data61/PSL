functor LtlLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : Ltl_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct
(*#line 1.2 "ltl.yacc"*)open Ltl_Dt

(*#line 13.1 "ltl.yacc.sml"*)
end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\011\000\006\000\010\000\007\000\009\000\008\000\008\000\
\\009\000\007\000\010\000\006\000\015\000\005\000\017\000\004\000\000\000\
\\001\000\002\000\019\000\003\000\018\000\004\000\017\000\005\000\016\000\
\\011\000\015\000\012\000\014\000\013\000\013\000\014\000\012\000\
\\016\000\033\000\000\000\
\\001\000\018\000\000\000\000\000\
\\035\000\002\000\019\000\003\000\018\000\004\000\017\000\005\000\016\000\
\\011\000\015\000\012\000\014\000\013\000\013\000\014\000\012\000\000\000\
\\036\000\000\000\
\\037\000\000\000\
\\038\000\000\000\
\\039\000\000\000\
\\040\000\000\000\
\\041\000\000\000\
\\042\000\000\000\
\\043\000\011\000\015\000\012\000\014\000\013\000\013\000\014\000\012\000\000\000\
\\044\000\011\000\015\000\012\000\014\000\013\000\013\000\014\000\012\000\000\000\
\\045\000\002\000\019\000\003\000\018\000\011\000\015\000\012\000\014\000\
\\013\000\013\000\014\000\012\000\000\000\
\\046\000\002\000\019\000\003\000\018\000\004\000\017\000\011\000\015\000\
\\012\000\014\000\013\000\013\000\014\000\012\000\000\000\
\\047\000\013\000\013\000\014\000\012\000\000\000\
\\048\000\013\000\013\000\014\000\012\000\000\000\
\\049\000\000\000\
\\050\000\000\000\
\\051\000\000\000\
\"
val actionRowNumbers =
"\000\000\003\000\004\000\000\000\
\\000\000\000\000\000\000\006\000\
\\005\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\
\\000\000\000\000\001\000\010\000\
\\009\000\008\000\007\000\018\000\
\\017\000\016\000\015\000\014\000\
\\013\000\012\000\011\000\019\000\
\\002\000"
val gotoT =
"\
\\001\000\032\000\002\000\001\000\000\000\
\\000\000\
\\000\000\
\\002\000\018\000\000\000\
\\002\000\019\000\000\000\
\\002\000\020\000\000\000\
\\002\000\021\000\000\000\
\\000\000\
\\000\000\
\\002\000\022\000\000\000\
\\002\000\023\000\000\000\
\\002\000\024\000\000\000\
\\002\000\025\000\000\000\
\\002\000\026\000\000\000\
\\002\000\027\000\000\000\
\\002\000\028\000\000\000\
\\002\000\029\000\000\000\
\\002\000\030\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 33
val numrules = 17
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle General.Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(List.map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit | IDENT of  (string) | formula of  (string ltlc) | input of  (string ltlc)
end
type svalue = MlyValue.svalue
type result = string ltlc
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 17) => true | _ => false
val showTerminal =
fn (T 0) => "NOT"
  | (T 1) => "OR"
  | (T 2) => "AND"
  | (T 3) => "IMPL"
  | (T 4) => "IFF"
  | (T 5) => "TRUE"
  | (T 6) => "FALSE"
  | (T 7) => "NEXT"
  | (T 8) => "FINAL"
  | (T 9) => "GLOBAL"
  | (T 10) => "UNTIL"
  | (T 11) => "RELEASE"
  | (T 12) => "WEAKUNTIL"
  | (T 13) => "STRONGRELEASE"
  | (T 14) => "LPAREN"
  | (T 15) => "RPAREN"
  | (T 16) => "IDENT"
  | (T 17) => "EOF"
  | (T 18) => "BAD_CHAR"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 18) $$ (T 17) $$ (T 15) $$ (T 14) $$ (T 13) $$ (T 12) $$ (T 11) $$ (T 10) $$ (T 9) $$ (T 8) $$ (T 7) $$ (T 6) $$ (T 5) $$ (T 4) $$ (T 3) $$ (T 2) $$ (T 1) $$ (T 0)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.formula formula, formula1left, formula1right)) :: rest671)) => let val  result = MlyValue.input ((*#line 38.17 "ltl.yacc"*)formula(*#line 207.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 0, ( result, formula1left, formula1right), rest671)
end
|  ( 1, ( ( _, ( MlyValue.IDENT IDENT, IDENT1left, IDENT1right)) :: rest671)) => let val  result = MlyValue.formula ((*#line 40.41 "ltl.yacc"*)Prop_ltlc IDENT(*#line 211.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, IDENT1left, IDENT1right), rest671)
end
|  ( 2, ( ( _, ( _, TRUE1left, TRUE1right)) :: rest671)) => let val  result = MlyValue.formula ((*#line 41.41 "ltl.yacc"*)True_ltlc(*#line 215.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, TRUE1left, TRUE1right), rest671)
end
|  ( 3, ( ( _, ( _, FALSE1left, FALSE1right)) :: rest671)) => let val  result = MlyValue.formula ((*#line 42.41 "ltl.yacc"*)False_ltlc(*#line 219.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, FALSE1left, FALSE1right), rest671)
end
|  ( 4, ( ( _, ( MlyValue.formula formula, _, formula1right)) :: ( _, ( _, NOT1left, _)) :: rest671)) => let val  result = MlyValue.formula ((*#line 43.41 "ltl.yacc"*)Not_ltlc formula(*#line 223.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, NOT1left, formula1right), rest671)
end
|  ( 5, ( ( _, ( MlyValue.formula formula, _, formula1right)) :: ( _, ( _, NEXT1left, _)) :: rest671)) => let val  result = MlyValue.formula ((*#line 44.41 "ltl.yacc"*)Next_ltlc formula(*#line 227.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, NEXT1left, formula1right), rest671)
end
|  ( 6, ( ( _, ( MlyValue.formula formula, _, formula1right)) :: ( _, ( _, FINAL1left, _)) :: rest671)) => let val  result = MlyValue.formula ((*#line 45.41 "ltl.yacc"*)Final_ltlc formula(*#line 231.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, FINAL1left, formula1right), rest671)
end
|  ( 7, ( ( _, ( MlyValue.formula formula, _, formula1right)) :: ( _, ( _, GLOBAL1left, _)) :: rest671)) => let val  result = MlyValue.formula ((*#line 46.41 "ltl.yacc"*)Global_ltlc formula(*#line 235.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, GLOBAL1left, formula1right), rest671)
end
|  ( 8, ( ( _, ( MlyValue.formula formula2, _, formula2right)) :: _ :: ( _, ( MlyValue.formula formula1, formula1left, _)) :: rest671)) => let val  result = MlyValue.formula ((*#line 47.41 "ltl.yacc"*)Or_ltlc (formula1, formula2)(*#line 239.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, formula1left, formula2right), rest671)
end
|  ( 9, ( ( _, ( MlyValue.formula formula2, _, formula2right)) :: _ :: ( _, ( MlyValue.formula formula1, formula1left, _)) :: rest671)) => let val  result = MlyValue.formula ((*#line 48.41 "ltl.yacc"*)And_ltlc (formula1, formula2)(*#line 243.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, formula1left, formula2right), rest671)
end
|  ( 10, ( ( _, ( MlyValue.formula formula2, _, formula2right)) :: _ :: ( _, ( MlyValue.formula formula1, formula1left, _)) :: rest671)) => let val  result = MlyValue.formula ((*#line 49.41 "ltl.yacc"*)Implies_ltlc (formula1, formula2)(*#line 247.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, formula1left, formula2right), rest671)
end
|  ( 11, ( ( _, ( MlyValue.formula formula2, _, formula2right)) :: _ :: ( _, ( MlyValue.formula formula1, formula1left, _)) :: rest671)) => let val  result = MlyValue.formula ((*#line 50.41 "ltl.yacc"*)iff_ltlc formula1 formula2(*#line 251.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, formula1left, formula2right), rest671)
end
|  ( 12, ( ( _, ( MlyValue.formula formula2, _, formula2right)) :: _ :: ( _, ( MlyValue.formula formula1, formula1left, _)) :: rest671)) => let val  result = MlyValue.formula ((*#line 51.41 "ltl.yacc"*)Until_ltlc (formula1, formula2)(*#line 255.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, formula1left, formula2right), rest671)
end
|  ( 13, ( ( _, ( MlyValue.formula formula2, _, formula2right)) :: _ :: ( _, ( MlyValue.formula formula1, formula1left, _)) :: rest671)) => let val  result = MlyValue.formula ((*#line 52.41 "ltl.yacc"*)Release_ltlc (formula1, formula2)(*#line 259.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, formula1left, formula2right), rest671)
end
|  ( 14, ( ( _, ( MlyValue.formula formula2, _, formula2right)) :: _ :: ( _, ( MlyValue.formula formula1, formula1left, _)) :: rest671)) => let val  result = MlyValue.formula ((*#line 53.41 "ltl.yacc"*)WeakUntil_ltlc (formula1, formula2)(*#line 263.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, formula1left, formula2right), rest671)
end
|  ( 15, ( ( _, ( MlyValue.formula formula2, _, formula2right)) :: _ :: ( _, ( MlyValue.formula formula1, formula1left, _)) :: rest671)) => let val  result = MlyValue.formula ((*#line 54.41 "ltl.yacc"*)StrongRelease_ltlc (formula1, formula2)(*#line 267.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, formula1left, formula2right), rest671)
end
|  ( 16, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.formula formula, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result = MlyValue.formula ((*#line 55.41 "ltl.yacc"*)formula(*#line 271.1 "ltl.yacc.sml"*)
)
 in ( LrTable.NT 1, ( result, LPAREN1left, RPAREN1right), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.input x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : Ltl_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun NOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(ParserData.MlyValue.VOID,p1,p2))
fun OR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(ParserData.MlyValue.VOID,p1,p2))
fun AND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(ParserData.MlyValue.VOID,p1,p2))
fun IMPL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(ParserData.MlyValue.VOID,p1,p2))
fun IFF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(ParserData.MlyValue.VOID,p1,p2))
fun TRUE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(ParserData.MlyValue.VOID,p1,p2))
fun FALSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(ParserData.MlyValue.VOID,p1,p2))
fun NEXT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(ParserData.MlyValue.VOID,p1,p2))
fun FINAL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(ParserData.MlyValue.VOID,p1,p2))
fun GLOBAL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(ParserData.MlyValue.VOID,p1,p2))
fun UNTIL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(ParserData.MlyValue.VOID,p1,p2))
fun RELEASE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(ParserData.MlyValue.VOID,p1,p2))
fun WEAKUNTIL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(ParserData.MlyValue.VOID,p1,p2))
fun STRONGRELEASE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(ParserData.MlyValue.VOID,p1,p2))
fun IDENT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(ParserData.MlyValue.IDENT i,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(ParserData.MlyValue.VOID,p1,p2))
fun BAD_CHAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(ParserData.MlyValue.VOID,p1,p2))
end
end
