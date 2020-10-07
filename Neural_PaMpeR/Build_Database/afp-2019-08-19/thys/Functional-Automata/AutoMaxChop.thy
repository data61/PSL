(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "Automata based scanner"

theory AutoMaxChop
imports DA MaxChop
begin

primrec auto_split :: "('a,'s)da \<Rightarrow> 's  \<Rightarrow> 'a list * 'a list \<Rightarrow> 'a list \<Rightarrow> 'a splitter" where
"auto_split A q res ps []     = (if fin A q then (ps,[]) else res)" |
"auto_split A q res ps (x#xs) =
   auto_split A (next A x q) (if fin A q then (ps,x#xs) else res) (ps@[x]) xs"

definition
 auto_chop :: "('a,'s)da \<Rightarrow> 'a chopper" where
"auto_chop A = chop (\<lambda>xs. auto_split A (start A) ([],xs) [] xs)"


lemma delta_snoc: "delta A (xs@[y]) q = next A y (delta A xs q)"
by simp

lemma auto_split_lemma:
 "\<And>q ps res. auto_split A (delta A ps q) res ps xs =
              maxsplit (\<lambda>ys. fin A (delta A ys q)) res ps xs"
apply (induct xs)
 apply simp
apply (simp add: delta_snoc[symmetric] del: delta_append)
done

lemma auto_split_is_maxsplit:
 "auto_split A (start A) res [] xs = maxsplit (accepts A) res [] xs"
apply (unfold accepts_def)
apply (subst delta_Nil[where ?s = "start A", symmetric])
apply (subst auto_split_lemma)
apply simp
done

lemma is_maxsplitter_auto_split:
 "is_maxsplitter (accepts A) (\<lambda>xs. auto_split A (start A) ([],xs) [] xs)"
by (simp add: auto_split_is_maxsplit is_maxsplitter_maxsplit)


lemma is_maxchopper_auto_chop:
 "is_maxchopper (accepts A) (auto_chop A)"
apply (unfold auto_chop_def)
apply (rule is_maxchopper_chop)
apply (rule is_maxsplitter_auto_split)
done

end
