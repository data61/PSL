(* Modified by Frédéric Tuong
 * Isabelle/C
 * (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *)
(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)

(* base.sig: Base signature file for SML-Yacc.  This file contains signatures
   that must be loaded before any of the files produced by ML-Yacc are loaded
*)

(* STREAM: signature for a lazy stream.*)

signature STREAM1 =
 sig type ('xa, 'xb) stream
     val streamify : ((('stack * 'stack_ml * 'stack_pos * 'stack_tree) * 'arg) -> '_a * (('stack * 'stack_ml * 'stack_pos * 'stack_tree) * 'arg)) -> 'arg -> ('_a, (('stack * 'stack_ml * 'stack_pos * 'stack_tree) * 'arg)) stream * 'arg
     val cons : '_a * (('_a, '_b) stream * '_b) -> ('_a, '_b) stream * '_b
     val get : ('_a, '_b) stream * '_b -> '_a * (('_a, '_b) stream * '_b)
 end

signature STREAM2 =
 sig type 'xa stream
     val streamify : (unit -> '_a) -> '_a stream
     val cons : '_a * '_a stream -> '_a stream
     val get : '_a stream -> '_a * '_a stream
 end

(* LR_TABLE: signature for an LR Table.

   The list of actions and gotos passed to mkLrTable must be ordered by state
   number. The values for state 0 are the first in the list, the values for
    state 1 are next, etc.
*)

signature LR_TABLE =
    sig
        datatype ('a,'b) pairlist = EMPTY | PAIR of 'a * 'b * ('a,'b) pairlist
        datatype state = STATE of int
        datatype term = T of int
        datatype nonterm = NT of int
        datatype action = SHIFT of state
                        | REDUCE of int
                        | ACCEPT
                        | ERROR
        type table

        val numStates : table -> int
        val numRules : table -> int
        val describeActions : table -> state ->
                                (term,action) pairlist * action
        val describeGoto : table -> state -> (nonterm,state) pairlist
        val action : table -> state * term -> action
        val goto : table -> state * nonterm -> state
        val initialState : table -> state
        exception Goto of state * nonterm

        val mkLrTable : {actions : ((term,action) pairlist * action) array,
                         gotos : (nonterm,state) pairlist array,
                         numStates : int, numRules : int,
                         initialState : state} -> table
    end

(* TOKEN: signature revealing the internal structure of a token. This signature
   TOKEN distinct from the signature {parser name}_TOKENS produced by ML-Yacc.
   The {parser name}_TOKENS structures contain some types and functions to
    construct tokens from values and positions.

   The representation of token was very carefully chosen here to allow the
   polymorphic parser to work without knowing the types of semantic values
   or line numbers.

   This has had an impact on the TOKENS structure produced by SML-Yacc, which
   is a structure parameter to lexer functors.  We would like to have some
   type 'a token which functions to construct tokens would create.  A
   constructor function for a integer token might be

          INT: int * 'a * 'a -> 'a token.

   This is not possible because we need to have tokens with the representation
   given below for the polymorphic parser.

   Thus our constructur functions for tokens have the form:

          INT: int * 'a * 'a -> (svalue,'a) token

   This in turn has had an impact on the signature that lexers for SML-Yacc
   must match and the types that a user must declare in the user declarations
   section of lexers.
*)

signature TOKEN =
    sig
        structure LALR_Table : LR_TABLE
        datatype ('a,'b) token = TOKEN of LALR_Table.term * ('a * 'b * 'b)
        val sameToken : ('a,'b) token * ('a,'b) token -> bool
    end

(* LR_PARSER: signature for a polymorphic LR parser *)

signature LR_PARSER1 =
    sig
        structure Stream : STREAM1
        structure LALR_Table : LR_TABLE
        structure Token : TOKEN

        sharing LALR_Table = Token.LALR_Table

        type ('_b, '_c) stack = (LALR_Table.state, '_b, '_c) C_Env.stack'

        type ('_b, '_c, 'arg1, 'arg2) lexer = (('arg1 -> '_b * 'arg1,'_c) Token.token, ('_b, '_c) stack * 'arg1) Stream.stream * 'arg2

        val parse : {table : LALR_Table.table,
                     saction : int *
                               '_c *
                               (LALR_Table.state * ('_b * '_c * '_c)) list *
                               'arg
                               ->    LALR_Table.nonterm *
                                     (('arg -> '_b * 'arg) * '_c * '_c) *
                                     (LALR_Table.state * ('_b * '_c * '_c)) list,
                     void : 'arg -> '_b * 'arg,
                     void_position : '_c,
                     start : ('arg -> '_b * 'arg, '_c) Token.token,
                     accept : '_c * '_c -> ('_b, '_c) stack * 'arg -> 'user * 'arg,
                     reduce_init : (('_c * '_c) list * int) * 'arg -> 'arg,
                     reduce_get : (LALR_Table.state, '_b, '_c) C_Env.rule_reduce -> 'arg -> (LALR_Table.state, '_b, '_c) C_Env.rule_output0 * 'arg,
                     ec : { is_keyword : LALR_Table.term -> bool,
                            noShift : LALR_Table.term -> bool,
                            preferred_change : (LALR_Table.term list * LALR_Table.term list) list,
                            errtermvalue : LALR_Table.term -> 'arg -> '_b * 'arg,
                            showTerminal : LALR_Table.term -> string,
                            terms: LALR_Table.term list,
                            error : '_c * '_c -> ('_b, '_c) stack * 'arg -> 'user * 'arg
                           },
                     lookahead : int  (* max amount of lookahead used in *)
                                      (* error correction *)
                    }
                    -> ('_b, '_c, 'arg, 'arg) lexer
                    -> ('_b, '_c, 'arg, 'user * 'arg) lexer
    end

signature LR_PARSER2 =
    sig
        structure Stream : STREAM2
        structure LALR_Table : LR_TABLE
        structure Token : TOKEN

        sharing LALR_Table = Token.LALR_Table

        exception ParseError

        val parse : {table : LALR_Table.table,
                     lexer : ('_b,'_c) Token.token Stream.stream,
                     arg: 'arg,
                     saction : int *
                               '_c *
                               (LALR_Table.state * ('_b * '_c * '_c)) list *
                               'arg
                               ->    LALR_Table.nonterm *
                                     ('_b * '_c * '_c) *
                                     (LALR_Table.state * ('_b * '_c * '_c)) list,
                     void : '_b,
                     ec : { is_keyword : LALR_Table.term -> bool,
                            noShift : LALR_Table.term -> bool,
                            preferred_change : (LALR_Table.term list * LALR_Table.term list) list,
                            errtermvalue : LALR_Table.term -> '_b,
                            showTerminal : LALR_Table.term -> string,
                            terms: LALR_Table.term list,
                            error : string * '_c * '_c -> unit
                           },
                     lookahead : int  (* max amount of lookahead used in *)
                                      (* error correction *)
                    }
                    -> '_b * ('_b,'_c) Token.token Stream.stream
    end

(* LEXER: a signature that most lexers produced for use with SML-Yacc's
   output will match.  The user is responsible for declaring type token,
   type pos, and type svalue in the LALR_Lex_Instance section of a lexer.

   Note that type token is abstract in the lexer.  This allows SML-Yacc to
   create a TOKENS signature for use with lexers produced by ML-Lex that
   treats the type token abstractly.  Lexers that are functors parametrized by
   a Tokens structure matching a TOKENS signature cannot examine the structure
   of tokens.
*)

signature LEXER =
   sig
       structure LALR_Lex_Instance :
           sig
                type ('a,'b) token
                type pos
                type svalue
           end
        val makeLexer : (int -> string)
                        -> unit
                        -> (LALR_Lex_Instance.svalue, LALR_Lex_Instance.pos) LALR_Lex_Instance.token
   end

(* ARG_LEXER: the %arg option of ML-Lex allows users to produce lexers which
   also take an argument before yielding a function from unit to a token
*)

signature ARG_LEXER1 =
   sig
       structure LALR_Lex_Instance :
           sig
                type ('a,'b) token
                type pos
                type arg
                type svalue0
                type svalue = arg -> svalue0 * arg
                type state
           end
        type stack = (LALR_Lex_Instance.state, LALR_Lex_Instance.svalue0, LALR_Lex_Instance.pos) C_Env.stack'
        val makeLexer : (stack * LALR_Lex_Instance.arg)
                        -> (LALR_Lex_Instance.svalue, LALR_Lex_Instance.pos) LALR_Lex_Instance.token
                         * (stack * LALR_Lex_Instance.arg)
   end

signature ARG_LEXER2 =
   sig
       structure LALR_Lex_Instance :
           sig
                type ('a,'b) token
                type pos
                type arg
                type svalue
           end
        val makeLexer : (int -> string)
                        -> LALR_Lex_Instance.arg
                        -> unit
                        -> (LALR_Lex_Instance.svalue,LALR_Lex_Instance.pos) LALR_Lex_Instance.token
   end

(* PARSER_DATA: the signature of ParserData structures in {parser name}LrValsFun
   produced by  SML-Yacc.  All such structures match this signature.

   The {parser name}LrValsFun produces a structure which contains all the values
   except for the lexer needed to call the polymorphic parser mentioned
   before.

*)

signature PARSER_DATA1 =
   sig
        (* the type of line numbers *)
        type pos

        (* the type of the user-supplied argument to the parser *)
        type arg

        (* the type of semantic values *)
        type svalue0
        type svalue = arg -> svalue0 * arg

        (* the intended type of the result of the parser.  This value is
           produced by applying extract from the structure Actions to the
           final semantic value resultiing from a parse.
         *)
        type result

        structure LALR_Table : LR_TABLE
        structure Token : TOKEN
        sharing Token.LALR_Table = LALR_Table

        (* structure Actions contains the functions which mantain the
           semantic values stack in the parser.  Void is used to provide
           a default value for the semantic stack.
         *)
        structure Actions :
          sig
              val actions : int * pos * (LALR_Table.state * (svalue0 * pos * pos)) list * arg
                            -> LALR_Table.nonterm * (svalue * pos * pos) * (LALR_Table.state * (svalue0 * pos * pos)) list
              val void : svalue
              val extract : svalue0 -> result
          end

        (* structure EC contains information used to improve error
           recovery in an error-correcting parser *)
        structure EC :
           sig
             val is_keyword : LALR_Table.term -> bool
             val noShift : LALR_Table.term -> bool
             val preferred_change : (LALR_Table.term list * LALR_Table.term list) list
             val errtermvalue : LALR_Table.term -> svalue
             val showTerminal : LALR_Table.term -> string
             val terms: LALR_Table.term list
           end

        (* table is the LR table for the parser *)
        val table : LALR_Table.table
    end

signature PARSER_DATA2 =
   sig
        (* the type of line numbers *)
        type pos

        (* the type of the user-supplied argument to the parser *)
        type arg

        (* the type of semantic values *)
        type svalue

        (* the intended type of the result of the parser.  This value is
           produced by applying extract from the structure Actions to the
           final semantic value resultiing from a parse.
         *)
        type result

        structure LALR_Table : LR_TABLE
        structure Token : TOKEN
        sharing Token.LALR_Table = LALR_Table

        (* structure Actions contains the functions which mantain the
           semantic values stack in the parser.  Void is used to provide
           a default value for the semantic stack.
         *)
        structure Actions :
          sig
              val actions : int * pos * (LALR_Table.state * (svalue * pos * pos)) list * arg
                            -> LALR_Table.nonterm * (svalue * pos * pos) * (LALR_Table.state * (svalue * pos * pos)) list
              val void : svalue
              val extract : svalue -> result
          end

        (* structure EC contains information used to improve error
           recovery in an error-correcting parser *)
        structure EC :
           sig
             val is_keyword : LALR_Table.term -> bool
             val noShift : LALR_Table.term -> bool
             val preferred_change : (LALR_Table.term list * LALR_Table.term list) list
             val errtermvalue : LALR_Table.term -> svalue
             val showTerminal : LALR_Table.term -> string
             val terms: LALR_Table.term list
           end

        (* table is the LR table for the parser *)
        val table : LALR_Table.table
    end

(* signature PARSER is the signature that most user parsers created by
   SML-Yacc will match.
*)

signature PARSER2 =
    sig
        structure Token : TOKEN
        structure Stream : STREAM2
        exception ParseError

        (* type pos is the type of line numbers *)
        type pos

        (* type result is the type of the result from the parser *)
        type result

        (* the type of the user-supplied argument to the parser *)
        type arg

        (* type svalue is the type of semantic values for the semantic value
           stack
         *)
        type svalue

        (* val makeLexer is used to create a stream of tokens for the parser *)
        val makeLexer : (int -> string)
                        -> (svalue, pos) Token.token Stream.stream

        (* val parse takes a stream of tokens and a function to print
           errors and returns a value of type result and a stream containing
           the unused tokens
         *)
        val parse : int * ((svalue, pos) Token.token Stream.stream) * (string * pos * pos -> unit) * arg
                    -> result * (svalue, pos) Token.token Stream.stream

        val sameToken : (svalue, pos) Token.token * (svalue,pos) Token.token
                        -> bool
     end

(* signature ARG_PARSER is the signature that will be matched by parsers whose
    lexer takes an additional argument.
*)

signature ARG_PARSER1 =
    sig
        structure Token : TOKEN
        structure Stream : STREAM1

        type arg
        type pos
        type svalue0
        type svalue = arg -> svalue0 * arg

        type stack = (Token.LALR_Table.state, svalue0, pos) C_Env.stack'

        type ('arg1, 'arg2) lexer = ((svalue, pos) Token.token, stack * 'arg1) Stream.stream * 'arg2

        val makeLexer : arg -> (arg, arg) lexer
        val parse :   int
                    * (pos * pos -> stack * arg -> 'user * arg)
                    * pos
                    * (svalue, pos) Token.token
                    * (pos * pos -> stack * arg -> 'user * arg)
                    * (((pos * pos) list * int) * arg -> arg)
                    * ((Token.LALR_Table.state, svalue0, pos) C_Env.rule_reduce -> arg -> (Token.LALR_Table.state, svalue0, pos) C_Env.rule_output0 * arg)
                   -> (arg, arg) lexer
                   -> (arg, 'user * arg) lexer
        val sameToken : (svalue, pos) Token.token * (svalue, pos) Token.token -> bool
     end

signature ARG_PARSER2 =
    sig
        structure Token : TOKEN
        structure Stream : STREAM2
        exception ParseError

        type arg
        type pos
        type result
        type svalue

        val makeLexer : (int -> string) -> arg
                        -> (svalue, pos) Token.token Stream.stream
        val parse : int * ((svalue, pos) Token.token Stream.stream) * (string * pos * pos -> unit) * arg
                    -> result * (svalue, pos) Token.token Stream.stream
        val sameToken : (svalue, pos) Token.token * (svalue,pos) Token.token
                        -> bool
     end
