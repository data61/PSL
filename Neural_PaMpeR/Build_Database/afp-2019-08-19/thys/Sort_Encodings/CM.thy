(* Countable version of MFOL structures: *)
theory CM
imports M
begin

(* Countable Versions of the locales from M
that assume a fixed countable carrier univ
instead of an arbitrary one 'univ: *)
locale Tstruct = M.Tstruct intT
for intT :: "'tp \<Rightarrow> univ \<Rightarrow> bool"

locale Struct = M.Struct wtFsym wtPsym arOf resOf parOf intT intF intP
for wtFsym and wtPsym
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf :: "'psym \<Rightarrow> 'tp list"
and intT :: "'tp \<Rightarrow> univ \<Rightarrow> bool"
and intF and intP

locale Model = M.Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP
for wtFsym and wtPsym
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf :: "'psym \<Rightarrow> 'tp list" and \<Phi>
and intT :: "'tp \<Rightarrow> univ \<Rightarrow> bool"
and intF and intP

sublocale Struct < Tstruct ..
sublocale Model < Struct ..


end
