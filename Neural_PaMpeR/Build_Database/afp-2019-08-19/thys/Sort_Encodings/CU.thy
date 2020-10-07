(* Countable version of UFOL structures: *)
theory CU
imports U
begin

locale Struct = U.Struct wtFsym wtPsym arOf parOf D intF intP
for wtFsym and wtPsym
and arOf :: "'fsym \<Rightarrow> nat"
and parOf :: "'psym \<Rightarrow> nat"
and D :: "univ \<Rightarrow> bool"
and intF :: "'fsym \<Rightarrow> univ list \<Rightarrow> univ"
and intP :: "'psym \<Rightarrow> univ list \<Rightarrow> bool"

locale Model = U.Model wtFsym wtPsym arOf parOf \<Phi> D intF intP
for wtFsym and wtPsym
and arOf :: "'fsym \<Rightarrow> nat"
and parOf :: "'psym \<Rightarrow> nat"
and \<Phi>
and D :: "univ \<Rightarrow> bool"
and intF :: "'fsym \<Rightarrow> univ list \<Rightarrow> univ"
and intP :: "'psym \<Rightarrow> univ list \<Rightarrow> bool"


end
