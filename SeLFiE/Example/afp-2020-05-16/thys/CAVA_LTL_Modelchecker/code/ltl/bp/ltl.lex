structure T = Tokens

type pos = int
type svalue = T.svalue
type ('a,'b) token = ('a,'b) T.token
type lexresult = (svalue,pos) token

val error = fn x => TextIO.output(TextIO.stdOut, x ^ "\n");
val eof = fn () => T.EOF (~1,0);

%%
%full
%header (functor LtlLexFun(Tokens: Ltl_TOKENS));
%reject
%posarg

alpha = [a-zA-Z_];
digit = [0-9];
ws = [\ \t];

%%

\n          => (continue ());
{ws}+       => (continue ());
"true"      => (T.TRUE (yypos,0));
"false"     => (T.FALSE (yypos,0));
"~"|"!"     => (T.NOT (yypos,0));
"|"+|"\\/"  => (T.OR (yypos,0));
"&"+|"/\\"  => (T.AND (yypos,0));
"X"         => (T.NEXT (yypos,0));
"U"         => (T.UNTIL (yypos,0));
"V"|"R"     => (T.RELEASE (yypos,0));
"-->"|"->"  => (T.IMPL (yypos,0));
"<-->"|"<->" => (T.IFF (yypos,0));
"F"|"<>"    => (T.FINAL (yypos,0));
"G"|"[]"    => (T.GLOBAL (yypos,0));
"("         => (T.LPAREN (yypos,0));
")"         => (T.RPAREN (yypos,0));
{alpha}({alpha}|{digit})* => (if yytext = "GF" orelse yytext = "FG" then 
                                REJECT() 
                              else (T.IDENT(yytext,yypos,0)));
{digit}+    => (T.IDENT_ARG(valOf(IntInf.fromString yytext), yypos, 0));
.           => (error("Bad character: " ^ yytext); T.BAD_CHAR (yypos,0));
