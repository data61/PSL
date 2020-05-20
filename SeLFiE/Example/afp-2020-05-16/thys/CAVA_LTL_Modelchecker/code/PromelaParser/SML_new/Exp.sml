open Basic;

val digit = satisfy Char.isDigit
(* consumes an integer number and returns error message in case of fail *)
val number = 
    let
        fun f acc nil = acc
            | f acc (c :: cs) = f (10 * acc + (Char.ord c - Char.ord #"0")) cs
    in
        list digit 
        >>= (fn nil => fail "number expected"
               | cs => return (f 0 cs))
    end

val space = list (satisfy Char.isSpace)
fun trim p = p -- space

fun symbol cs = "'" ^ cs ^ "' expected" !! 
                try (items (explode cs) ==> implode)
val $ = trim o symbol

(* consumes usage of an operator, which may be existant zero or more times

nxt is the next operator in the hiearchy *)
fun sop opStr opF nxt = 
                nxt ()
            >>| list ($ opStr) >> nxt ()
            =|> foldl opF

fun expr _ = exprAdd ()
and exprAdd _ = sop "+" (op +) exprMul
and exprMul _ = sop "*" (op *) exprBase
and exprBase _ = "expression expected" !!
            $"(" >> expr() -- $")"
            (* change the above to
            $"(" >>= (fn _ => expr() -- $")")
            to make it work in MLton *)
         || trim number

val _ = expr();

print "expr not mutual recursive on construction\n";
val _ = parse (expr()) "(1+2)*3";
print "expr works\n";
