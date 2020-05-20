section \<open>Special constants\<close>

theory Consts
imports
  Constructors
  Higher_Order_Terms.Nterm
begin

locale special_constants = constructors

locale pre_constants = special_constants +
  fixes heads :: "name fset"
begin

definition all_consts :: "name fset" where
"all_consts = heads |\<union>| C"

abbreviation welldefined :: "'a::term \<Rightarrow> bool" where
"welldefined t \<equiv> consts t |\<subseteq>| all_consts"

sublocale welldefined: simple_syntactic_and welldefined
by standard auto

end

declare pre_constants.all_consts_def[code]

locale constants = pre_constants +
  assumes disjnt: "fdisjnt heads C"
  \<comment> \<open>Conceptually the following assumptions should belong into @{locale constructors}, but I prefer
      to keep that one assumption-free.\<close>
  assumes distinct_ctr: "distinct all_constructors"
begin

lemma distinct_ctr': "distinct (map as_string all_constructors)"
unfolding distinct_map
using distinct_ctr
by (auto intro: inj_onI dest: name.expand)

end

end