(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
                 Philipp Meyer <meyerphi@in.tum.de>
*)
section \<open>\isaheader {The hashable Typeclass}\<close>
theory HashCode
imports 
  Native_Word.Uint32 
begin

text_raw \<open>\label{thy:HashCode}\<close>

text \<open>
  In this theory a typeclass of hashable types is established.
  For hashable types, there is a function \<open>hashcode\<close>, that
  maps any entity of this type to an unsigned 32 bit word value.

  This theory defines the hashable typeclass and provides instantiations
  for a couple of standard types.
\<close>

type_synonym
  hashcode = "uint32"

definition "nat_of_hashcode \<equiv> nat_of_uint32"
definition "int_of_hashcode \<equiv> int_of_uint32"
definition "integer_of_hashcode \<equiv> integer_of_uint32"

class hashable =
  fixes hashcode :: "'a \<Rightarrow> hashcode"
  and def_hashmap_size :: "'a itself \<Rightarrow> nat"
  assumes def_hashmap_size: "1 < def_hashmap_size TYPE('a)"
begin
  definition bounded_hashcode :: "uint32 \<Rightarrow> 'a \<Rightarrow> uint32" where
    "bounded_hashcode n x = (hashcode x) mod n"
 
  lemma bounded_hashcode_bounds: "1 < n \<Longrightarrow> bounded_hashcode n a < n"
    unfolding bounded_hashcode_def
    by (transfer, simp add: word_less_def uint_mod)

  definition bounded_hashcode_nat :: "nat \<Rightarrow> 'a \<Rightarrow> nat" where
    "bounded_hashcode_nat n x = nat_of_hashcode (hashcode x) mod n"

  lemma bounded_hashcode_nat_bounds: "1 < n \<Longrightarrow> bounded_hashcode_nat n a < n"
    unfolding bounded_hashcode_nat_def
    by transfer simp
end

instantiation unit :: hashable
begin
  definition [simp]: "hashcode (u :: unit) = 0"
  definition "def_hashmap_size = (\<lambda>_ :: unit itself. 2)"
  instance
    by (intro_classes)(simp_all add: def_hashmap_size_unit_def)
end

instantiation bool :: hashable
begin
  definition [simp]: "hashcode (b :: bool) = (if b then 1 else 0)"
  definition "def_hashmap_size = (\<lambda>_ :: bool itself. 2)"
  instance by (intro_classes)(simp_all add: def_hashmap_size_bool_def)
end

instantiation "int" :: hashable
begin
  definition [simp]: "hashcode (i :: int) = uint32_of_int i"
  definition "def_hashmap_size = (\<lambda>_ :: int itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_int_def)
end

instantiation "integer" :: hashable
begin
  definition [simp]: "hashcode (i :: integer) = Uint32 i"
  definition "def_hashmap_size = (\<lambda>_ :: integer itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_integer_def)
end

instantiation "nat" :: hashable
begin
  definition [simp]: "hashcode (n :: nat) = uint32_of_int (int n)"
  definition "def_hashmap_size = (\<lambda>_ :: nat itself. 16)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_nat_def)
end

instantiation char :: hashable
begin
  definition [simp]: "hashcode (c :: char) == uint32_of_int (of_char c)"
  definition "def_hashmap_size = (\<lambda>_ :: char itself. 32)"
  instance by(intro_classes)(simp_all add: def_hashmap_size_char_def)
end

instantiation prod :: (hashable, hashable) hashable
begin
  definition "hashcode x == (hashcode (fst x) * 33 + hashcode (snd x))"
  definition "def_hashmap_size = (\<lambda>_ :: ('a \<times> 'b) itself. def_hashmap_size TYPE('a) + def_hashmap_size TYPE('b))"
  instance using def_hashmap_size[where ?'a="'a"] def_hashmap_size[where ?'a="'b"]
    by(intro_classes)(simp_all add: def_hashmap_size_prod_def)
end

instantiation sum :: (hashable, hashable) hashable
begin
  definition "hashcode x == (case x of Inl a \<Rightarrow> 2 * hashcode a | Inr b \<Rightarrow> 2 * hashcode b + 1)"
  definition "def_hashmap_size = (\<lambda>_ :: ('a + 'b) itself. def_hashmap_size TYPE('a) + def_hashmap_size TYPE('b))"
  instance using def_hashmap_size[where ?'a="'a"] def_hashmap_size[where ?'a="'b"]
    by(intro_classes)(simp_all add: bounded_hashcode_bounds def_hashmap_size_sum_def split: sum.split)
end

instantiation list :: (hashable) hashable
begin
  definition "hashcode = foldl (\<lambda>h x. h * 33 + hashcode x) 5381"
  definition "def_hashmap_size = (\<lambda>_ :: 'a list itself. 2 * def_hashmap_size TYPE('a))"
  instance
  proof
    from def_hashmap_size[where ?'a = "'a"]
    show "1 < def_hashmap_size TYPE('a list)"
      by(simp add: def_hashmap_size_list_def)
  qed
end

instantiation option :: (hashable) hashable
begin
  definition "hashcode opt = (case opt of None \<Rightarrow> 0 | Some a \<Rightarrow> hashcode a + 1)"
  definition "def_hashmap_size = (\<lambda>_ :: 'a option itself. def_hashmap_size TYPE('a) + 1)"
  instance using def_hashmap_size[where ?'a = "'a"]
    by(intro_classes)(simp_all add: def_hashmap_size_option_def split: option.split)
end

lemma hashcode_option_simps [simp]:
  "hashcode None = 0"
  "hashcode (Some a) = 1 + hashcode a"
  by(simp_all add: hashcode_option_def)

lemma bounded_hashcode_option_simps [simp]:
  "bounded_hashcode n None = 0"
  "bounded_hashcode n (Some a) = (hashcode a + 1) mod n"
  apply (simp_all add: bounded_hashcode_def, transfer, simp_all add: word_mod_def)
  apply (simp_all add: algebra_simps)
  done

(*
lemma bounded_hashcode_option_simps [simp]:
  "bounded_hashcode n None = 0"
  "bounded_hashcode n (Some a) = (bounded_hashcode n a + 1) mod n"
  apply (simp_all add: bounded_hashcode_def, transfer, simp_all add: word_mod_def)
  apply (simp_all add: algebra_simps mod_add_right_eq)
*)

instantiation String.literal :: hashable
begin

definition hashcode_literal :: "String.literal \<Rightarrow> uint32" 
  where "hashcode_literal s = hashcode (String.explode s)"

definition def_hashmap_size_literal  :: "String.literal itself \<Rightarrow> nat"
  where "def_hashmap_size_literal _ = 10"

instance
  by standard (simp_all only: def_hashmap_size_literal_def)

end


hide_type (open) word

end
