signature Ltl_TOKENS =
sig
type ('a,'b) token
type svalue
val BAD_CHAR:  'a * 'a -> (svalue,'a) token
val EOF:  'a * 'a -> (svalue,'a) token
val IDENT: (string) *  'a * 'a -> (svalue,'a) token
val RPAREN:  'a * 'a -> (svalue,'a) token
val LPAREN:  'a * 'a -> (svalue,'a) token
val STRONGRELEASE:  'a * 'a -> (svalue,'a) token
val WEAKUNTIL:  'a * 'a -> (svalue,'a) token
val RELEASE:  'a * 'a -> (svalue,'a) token
val UNTIL:  'a * 'a -> (svalue,'a) token
val GLOBAL:  'a * 'a -> (svalue,'a) token
val FINAL:  'a * 'a -> (svalue,'a) token
val NEXT:  'a * 'a -> (svalue,'a) token
val FALSE:  'a * 'a -> (svalue,'a) token
val TRUE:  'a * 'a -> (svalue,'a) token
val IFF:  'a * 'a -> (svalue,'a) token
val IMPL:  'a * 'a -> (svalue,'a) token
val AND:  'a * 'a -> (svalue,'a) token
val OR:  'a * 'a -> (svalue,'a) token
val NOT:  'a * 'a -> (svalue,'a) token
end
signature Ltl_LRVALS=
sig
structure Tokens : Ltl_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
