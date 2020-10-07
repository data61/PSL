(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "Generic scanner"

theory MaxChop
imports MaxPrefix
begin

type_synonym 'a chopper = "'a list \<Rightarrow> 'a list list * 'a list"

definition
 is_maxchopper :: "('a list \<Rightarrow> bool) \<Rightarrow> 'a chopper \<Rightarrow> bool" where
"is_maxchopper P chopper =
 (\<forall>xs zs yss.
    (chopper(xs) = (yss,zs)) =
    (xs = concat yss @ zs \<and> (\<forall>ys \<in> set yss. ys \<noteq> []) \<and>
     (case yss of
        [] \<Rightarrow> is_maxpref P [] xs
      | us#uss \<Rightarrow> is_maxpref P us xs \<and> chopper(concat(uss)@zs) = (uss,zs))))"

definition
 reducing :: "'a splitter \<Rightarrow> bool" where
"reducing splitf =
 (\<forall>xs ys zs. splitf xs = (ys,zs) \<and> ys \<noteq> [] \<longrightarrow> length zs < length xs)"

function chop :: "'a splitter \<Rightarrow> 'a list \<Rightarrow> 'a list list \<times> 'a list" where
  [simp del]: "chop splitf xs = (if reducing splitf
                      then let pp = splitf xs
                           in if fst pp = [] then ([], xs)
                           else let qq = chop splitf (snd pp)
                                in (fst pp # fst qq, snd qq)
                      else undefined)"
by pat_completeness auto

termination apply (relation "measure (length \<circ> snd)")
apply (auto simp: reducing_def)
apply (case_tac "splitf xs")
apply auto
done

lemma chop_rule: "reducing splitf \<Longrightarrow>
  chop splitf xs = (let (pre, post) = splitf xs
                    in if pre = [] then ([], xs)
                       else let (xss, zs) = chop splitf post
                            in (pre # xss,zs))"
apply (simp add: chop.simps)
apply (simp add: Let_def split: prod.split)
done

lemma reducing_maxsplit: "reducing(\<lambda>qs. maxsplit P ([],qs) [] qs)"
by (simp add: reducing_def maxsplit_eq)

lemma is_maxsplitter_reducing:
 "is_maxsplitter P splitf \<Longrightarrow> reducing splitf"
by(simp add:is_maxsplitter_def reducing_def)

lemma chop_concat[rule_format]: "is_maxsplitter P splitf \<Longrightarrow>
  (\<forall>yss zs. chop splitf xs = (yss,zs) \<longrightarrow> xs = concat yss @ zs)"
apply (induct xs rule:length_induct)
apply (simp (no_asm_simp) split del: if_split
            add: chop_rule[OF is_maxsplitter_reducing])
apply (simp add: Let_def is_maxsplitter_def split: prod.split)
done

lemma chop_nonempty: "is_maxsplitter P splitf \<Longrightarrow>
  \<forall>yss zs. chop splitf xs = (yss,zs) \<longrightarrow> (\<forall>ys \<in> set yss. ys \<noteq> [])"
apply (induct xs rule:length_induct)
apply (simp (no_asm_simp) add: chop_rule is_maxsplitter_reducing)
apply (simp add: Let_def is_maxsplitter_def split: prod.split)
apply (intro allI impI)
apply (rule ballI)
apply (erule exE)
apply (erule allE)
apply auto
done

lemma is_maxchopper_chop:
 assumes prem: "is_maxsplitter P splitf" shows "is_maxchopper P (chop splitf)"
apply(unfold is_maxchopper_def)
apply clarify
apply (rule iffI)
 apply (rule conjI)
  apply (erule chop_concat[OF prem])
 apply (rule conjI)
  apply (erule prem[THEN chop_nonempty[THEN spec, THEN spec, THEN mp]])
 apply (erule rev_mp)
 apply (subst prem[THEN is_maxsplitter_reducing[THEN chop_rule]])
 apply (simp add: Let_def prem[simplified is_maxsplitter_def]
             split: prod.split)
 apply clarify
 apply (rule conjI)
  apply (clarify)
 apply (clarify)
 apply simp
 apply (frule chop_concat[OF prem])
 apply (clarify)
apply (subst prem[THEN is_maxsplitter_reducing, THEN chop_rule])
apply (simp add: Let_def prem[simplified is_maxsplitter_def]
             split: prod.split)
apply (clarify)
apply (rename_tac xs1 ys1 xss1 ys)
apply (simp split: list.split_asm)
 apply (simp add: is_maxpref_def)
 apply (blast intro: prefix_append[THEN iffD2])
apply (rule conjI)
 apply (clarify)
 apply (simp (no_asm_use) add: is_maxpref_def)
 apply (blast intro: prefix_append[THEN iffD2])
apply (clarify)
apply (rename_tac us uss)
apply (subgoal_tac "xs1=us")
 apply simp
apply simp
apply (simp (no_asm_use) add: is_maxpref_def)
apply (blast intro: prefix_append[THEN iffD2] prefix_order.antisym)
done

end
