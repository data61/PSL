theory gcd
  imports "../utp_easy_parser"
begin

alphabet gcd_ss =
  x :: int
  y :: int

abbreviation gcd_prog :: "int \<Rightarrow> int \<Rightarrow> gcd_ss hrel" where
  "gcd_prog X Y \<equiv>
   x := \<guillemotleft>X\<guillemotright> ;;
   y := \<guillemotleft>Y\<guillemotright> ;;
   while \<not> (x = y)
   invr x > 0 \<and> y > 0 \<and> gcd(x,y) = gcd(\<guillemotleft>X\<guillemotright>, \<guillemotleft>Y\<guillemotright>)
   do
      if x > y 
         then x := x - y
         else y := y - x
      fi
   od"

lemma "TRY(id \<Turnstile> gcd_prog 6 21)"
  apply (sym_eval)
  oops

lemma gcd_verify:
  "{{\<guillemotleft>X\<guillemotright> > 0 \<and> \<guillemotleft>Y > 0\<guillemotright>}} gcd_prog X Y {{x = gcd(\<guillemotleft>X\<guillemotright>, \<guillemotleft>Y\<guillemotright>)}}"
  oops

end