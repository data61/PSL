(* Modified by Frédéric Tuong
 * Isabelle/C
 * (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *)
(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)

(* functor Join creates a user parser by putting together a Lexer structure,
   an LrValues structure, and a polymorphic parser structure.  Note that
   the Lexer and LrValues structure must share the type pos (i.e. the type
   of line numbers), the type svalues for semantic values, and the type
   of tokens.
*)

functor Join2 (structure Lex : LEXER
               structure ParserData: PARSER_DATA2
               structure LrParser : LR_PARSER2
               sharing ParserData.LALR_Table = LrParser.LALR_Table
               sharing ParserData.Token = LrParser.Token
               sharing type Lex.LALR_Lex_Instance.svalue = ParserData.svalue
               sharing type Lex.LALR_Lex_Instance.pos = ParserData.pos
               sharing type Lex.LALR_Lex_Instance.token = ParserData.Token.token)
                 : PARSER2 =
struct
    structure Token = ParserData.Token
    structure Stream = LrParser.Stream

    exception ParseError = LrParser.ParseError

    type arg = ParserData.arg
    type pos = ParserData.pos
    type result = ParserData.result
    type svalue = ParserData.svalue
    val makeLexer = LrParser.Stream.streamify o Lex.makeLexer
    val parse = fn (lookahead,lexer,error,arg) =>
        (fn (a,b) => (ParserData.Actions.extract a,b))
     (LrParser.parse {table = ParserData.table,
                lexer=lexer,
                lookahead=lookahead,
                saction = ParserData.Actions.actions,
                arg=arg,
                void= ParserData.Actions.void,
                ec = {is_keyword = ParserData.EC.is_keyword,
                      noShift = ParserData.EC.noShift,
                      preferred_change = ParserData.EC.preferred_change,
                      errtermvalue = ParserData.EC.errtermvalue,
                      error=error,
                      showTerminal = ParserData.EC.showTerminal,
                      terms = ParserData.EC.terms}}
      )
     val sameToken = Token.sameToken
end

(* functor JoinWithArg creates a variant of the parser structure produced
   above.  In this case, the makeLexer take an additional argument before
   yielding a value of type unit -> (svalue,pos) token
 *)

functor LALR_Parser_Join(structure Lex : ARG_LEXER1
             structure ParserData: PARSER_DATA1
             structure LrParser : LR_PARSER1
             sharing ParserData.LALR_Table = LrParser.LALR_Table
             sharing ParserData.Token = LrParser.Token
             sharing type Lex.LALR_Lex_Instance.arg = ParserData.arg
             sharing type Lex.LALR_Lex_Instance.svalue0 = ParserData.svalue0
             sharing type Lex.LALR_Lex_Instance.pos = ParserData.pos
             sharing type Lex.LALR_Lex_Instance.token = ParserData.Token.token
             sharing type Lex.LALR_Lex_Instance.state = ParserData.Token.LALR_Table.state)
                 : ARG_PARSER1 =
struct
    structure Token = ParserData.Token
    structure Stream = LrParser.Stream

    type arg = ParserData.arg
    type pos = ParserData.pos
    type svalue0 = ParserData.svalue0
    type svalue = arg -> svalue0 * arg

    type stack = (Token.LALR_Table.state, svalue0, pos) C_Env.stack'

    type ('arg1, 'arg2) lexer = ((svalue, pos) Token.token, stack * 'arg1) Stream.stream * 'arg2

    val makeLexer = LrParser.Stream.streamify Lex.makeLexer

    val parse = fn (lookahead, error, void_position, start, accept, reduce_init, reduce_get) =>
      LrParser.parse {table = ParserData.table,
                      lookahead = lookahead,
                      saction = ParserData.Actions.actions,
                      void = ParserData.Actions.void,
                      void_position = void_position,
                      start = start,
                      accept = accept,
                      reduce_init = reduce_init,
                      reduce_get = reduce_get,
                      ec = {is_keyword = ParserData.EC.is_keyword,
                            noShift = ParserData.EC.noShift,
                            preferred_change = ParserData.EC.preferred_change,
                            errtermvalue = ParserData.EC.errtermvalue,
                            error=error,
                            showTerminal = ParserData.EC.showTerminal,
                            terms = ParserData.EC.terms}}

    val sameToken = Token.sameToken
end

functor JoinWithArg2(structure Lex : ARG_LEXER2
             structure ParserData: PARSER_DATA2
             structure LrParser : LR_PARSER2
             sharing ParserData.LALR_Table = LrParser.LALR_Table
             sharing ParserData.Token = LrParser.Token
             sharing type Lex.LALR_Lex_Instance.arg = ParserData.arg
             sharing type Lex.LALR_Lex_Instance.svalue = ParserData.svalue
             sharing type Lex.LALR_Lex_Instance.pos = ParserData.pos
             sharing type Lex.LALR_Lex_Instance.token = ParserData.Token.token)
                 : ARG_PARSER2  =
struct
    structure Token = ParserData.Token
    structure Stream = LrParser.Stream

    exception ParseError = LrParser.ParseError

    type arg = ParserData.arg
    type pos = ParserData.pos
    type result = ParserData.result
    type svalue = ParserData.svalue

    val makeLexer = LrParser.Stream.streamify oo Lex.makeLexer
    val parse = fn (lookahead,lexer,error,arg) =>
        (fn (a,b) => (ParserData.Actions.extract a,b))
     (LrParser.parse {table = ParserData.table,
                lexer=lexer,
                lookahead=lookahead,
                saction = ParserData.Actions.actions,
                arg=arg,
                void= ParserData.Actions.void,
                ec = {is_keyword = ParserData.EC.is_keyword,
                      noShift = ParserData.EC.noShift,
                      preferred_change = ParserData.EC.preferred_change,
                      errtermvalue = ParserData.EC.errtermvalue,
                      error=error,
                      showTerminal = ParserData.EC.showTerminal,
                      terms = ParserData.EC.terms}}
      )
    val sameToken = Token.sameToken
end;
