(*  Author:  Tobias Nipkow  *)

section "Comparing Enumeration and Archive"

theory ArchComp
imports "Flyspeck-Tame.ArchCompProps" "HOL-Library.Code_Target_Numeral"
begin

subsection \<open>Proofs by evaluation using generated code\<close>

lemma pre_iso_test3: "\<forall>g \<in> set Tri. pre_iso_test g"
by eval

lemma pre_iso_test4: "\<forall>g \<in> set Quad. pre_iso_test g"
by eval

lemma pre_iso_test5: "\<forall>g \<in> set Pent. pre_iso_test g"
by eval

lemma pre_iso_test6: "\<forall>g \<in> set Hex. pre_iso_test g"
by eval

lemma same3: "samet (tameEnumFilter 0) Tri"
by eval

lemma same4: "samet (tameEnumFilter 1) Quad"
by eval

lemma same5: "samet (tameEnumFilter 2) Pent"
by eval

lemma same6: "samet (tameEnumFilter 3) Hex"
by eval

end
