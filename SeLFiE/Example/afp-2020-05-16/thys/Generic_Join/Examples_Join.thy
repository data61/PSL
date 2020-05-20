section \<open>Example instantiations and queries\<close>

theory Examples_Join
  imports Generic_Join
begin

subsection \<open>Instantiations\<close>

global_interpretation Max_getIJ: getIJ "\<lambda>_ _ V. (V - {Max V}, {Max V})"
  defines Max_getIJ_genericJoin = "Max_getIJ.genericJoin"
  and Max_getIJ_wrapperGenericJoin = "Max_getIJ.wrapperGenericJoin"
  by standard (metis Diff_disjoint Max_in One_nat_def Pair_inject Suc_1 Suc_le_mono card.insert_remove card_empty card_infinite card_insert_disjoint finite.emptyI inf_commute insert_Diff insert_absorb insert_is_Un insert_not_empty le_numeral_extra(4) not_numeral_le_zero sup_commute)


global_interpretation Min_getIJ: getIJ "\<lambda>_ _ V. ({Min V}, V - {Min V})"
  defines Min_getIJ_genericJoin = "Min_getIJ.genericJoin"
  and Min_getIJ_wrapperGenericJoin = "Min_getIJ.wrapperGenericJoin"
  by standard (metis Diff_disjoint Min_in One_nat_def Pair_inject Suc_1 card.insert_remove card_empty card_infinite card_insert_disjoint finite.emptyI insert_Diff insert_absorb insert_is_Un insert_not_empty le_numeral_extra(4) not_less_eq_eq not_numeral_le_zero)

subsection \<open>Queries\<close>

value "Max_getIJ.genericJoin {0, 1} {({0 , 1}, {[Some (0 :: nat), Some 0], [Some 1, Some 1]}), ({0 , 1}, {[Some 0, Some 0], [Some 0, Some 1]})} {} :: nat table"
value "Min_getIJ.genericJoin {0, 1} {({0 , 1}, {[Some (0 :: nat), Some 0], [Some 1, Some 1]}), ({0 , 1}, {[Some 0, Some 0], [Some 0, Some 1]})} {} :: nat table"

fun protoTableTriangle :: "nat \<Rightarrow> nat table" where
  "protoTableTriangle 0 = {[Some 0, Some 0]}"
| "protoTableTriangle (Suc n) = (protoTableTriangle n) \<union> {[Some (Suc n), Some 0], [Some 0, Some (Suc n)]}"

fun auxInsertNoneTriangle :: "nat tuple \<Rightarrow> nat \<Rightarrow> nat tuple" where
  "auxInsertNoneTriangle l 0 = None # l"
| "auxInsertNoneTriangle (x # q) (Suc n) = x # (auxInsertNoneTriangle q n)"
| "auxInsertNoneTriangle [] (Suc v) = undefined"

fun insertNoneTriangle :: "nat table \<Rightarrow> nat \<Rightarrow> nat table" where
  "insertNoneTriangle t n = {auxInsertNoneTriangle x n | x . x \<in> t}"

value "set [0 ..< 5]"

fun getTableTriangle :: "nat \<Rightarrow> nat \<Rightarrow> nat atable" where
  "getTableTriangle n i = ({0, 1, 2} - {i}, insertNoneTriangle (protoTableTriangle n) i)"

fun getQueryTriangle :: "nat \<Rightarrow> nat query" where
  "getQueryTriangle n = {getTableTriangle n 0, getTableTriangle n 1, getTableTriangle n 2}"

definition verticesTriangle :: vertices where "verticesTriangle = {0, 1, 2}"

value "getQueryTriangle 2"

value "Max_getIJ.genericJoin verticesTriangle (getQueryTriangle 2) {({0, 2}, {[Some 0, None, Some 0]})}"

value "let n = 2 in let ((_, A), (_, B), (_, C)) = (getTableTriangle n 0, getTableTriangle n 1, getTableTriangle n 2) in
let AB = join A True B in join AB True C"
value "Min_getIJ.wrapperGenericJoin (getQueryTriangle 2) {}"
value "Max_getIJ.wrapperGenericJoin (getQueryTriangle 2) {}"
value "New_max.wrapperGenericJoin (getQueryTriangle 2) {}"

end
