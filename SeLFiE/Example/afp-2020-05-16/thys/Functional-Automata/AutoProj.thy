(*  Author:     Tobias Nipkow
    Copyright   1998 TUM

Is there an optimal order of arguments for `next'?
Currently we can have laws like `delta A (a#w) = delta A w o delta A a'
Otherwise we could have `acceps A == fin A o delta A (start A)'
and use foldl instead of foldl2.
*)

section "Projection functions for automata"

theory AutoProj
imports Main
begin

definition start :: "'a * 'b * 'c \<Rightarrow> 'a" where "start A = fst A"
definition "next" :: "'a * 'b * 'c \<Rightarrow> 'b" where "next A = fst(snd(A))"
definition fin :: "'a * 'b * 'c \<Rightarrow> 'c" where "fin A = snd(snd(A))"

lemma [simp]: "start(q,d,f) = q"
by(simp add:start_def)

lemma [simp]: "next(q,d,f) = d"
by(simp add:next_def)

lemma [simp]: "fin(q,d,f) = f"
by(simp add:fin_def)

end
