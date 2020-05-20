(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "Combining automata and regular expressions"

theory AutoRegExp
imports Automata RegExp2NA RegExp2NAe
begin

theorem "DA.accepts (na2da(rexp2na r)) w = (w : lang r)"
by (simp add: NA_DA_equiv[THEN sym] accepts_rexp2na)

theorem  "DA.accepts (nae2da(rexp2nae r)) w = (w : lang r)"
by (simp add: NAe_DA_equiv accepts_rexp2nae)

end
