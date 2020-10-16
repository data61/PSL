(*
 *  Signature for a Lexer with %posarg set
 *)
signature POS_LEXER =
   sig
       structure UserDeclarations :
           sig
                type ('a,'b) token
                type pos
                type svalue
           end
        val makeLexer : ((int -> string) * int) -> unit ->
         (UserDeclarations.svalue,UserDeclarations.pos) UserDeclarations.token
   end

(*
 * Mapping POS_LEXER to LEXER by setting 'pos' to 0
 *)
functor Pos0_Lexer (L : POS_LEXER) : LEXER =
struct
  structure UserDeclarations = L.UserDeclarations
  val makeLexer = fn strm => L.makeLexer (strm,0);
end

structure LtlLrVals = LtlLrValsFun(structure Token = LrParser.Token);
structure LtlLex : POS_LEXER = LtlLexFun(LtlLrVals.Tokens);

structure LtlParser = Join(
	structure ParserData = LtlLrVals.ParserData
	structure Lex=Pos0_Lexer(LtlLex)
	structure LrParser=LrParser);

structure PropLtl =
struct
  exception ParseError = LtlParser.ParseError;
  fun parse mla g pE = 
    let 
      val (tree,_) = LtlParser.parse(mla, LtlParser.makeLexer g, pE, ())
    in 
      tree
    end
end
