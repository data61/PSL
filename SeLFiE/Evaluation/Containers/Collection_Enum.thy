(*  Title:      Containers/Collection_Enum.thy
    Author:     Andreas Lochbihler, KIT
                René Thiemann, UIBK *)

theory Collection_Enum imports
  Containers_Auxiliary
  Containers_Generator
begin

section \<open>A type class for optional enumerations\<close>

subsection \<open>Definition\<close>

class cenum =
  fixes cEnum :: "('a list \<times> (('a \<Rightarrow> bool) \<Rightarrow> bool) \<times> (('a \<Rightarrow> bool) \<Rightarrow> bool)) option"
  assumes UNIV_cenum: "cEnum = Some (enum, enum_all, enum_ex) \<Longrightarrow> UNIV = set enum"
  and cenum_all_UNIV: "cEnum = Some (enum, enum_all, enum_ex) \<Longrightarrow> enum_all P = Ball UNIV P"
  and cenum_ex_UNIV: "cEnum = Some (enum, enum_all, enum_ex) \<Longrightarrow> enum_ex P = Bex UNIV P"
begin

lemma ID_cEnum: 
  "ID cEnum = Some (enum, enum_all, enum_ex)
  \<Longrightarrow> UNIV = set enum \<and> enum_all = Ball UNIV \<and> enum_ex = Bex UNIV"
unfolding ID_def id_apply fun_eq_iff
by(intro conjI allI UNIV_cenum cenum_all_UNIV cenum_ex_UNIV fun_eq_iff)

lemma in_cenum: "ID cEnum = Some (enum, rest) \<Longrightarrow> f \<in> set enum"
by(cases rest)(auto dest: ID_cEnum)

abbreviation cenum :: "'a list" 
where "cenum \<equiv> fst (the (ID cEnum))"

abbreviation cenum_all :: "('a \<Rightarrow> bool) \<Rightarrow> bool" 
where "cenum_all \<equiv> fst (snd (the (ID cEnum)))"

abbreviation cenum_ex :: "('a \<Rightarrow> bool) \<Rightarrow> bool" 
where "cenum_ex \<equiv> snd (snd (the (ID cEnum)))"

end

syntax "_CENUM" :: "type => logic"  ("(1CENUM/(1'(_')))")

parse_translation \<open>
let
  fun cenum_tr [ty] =
     (Syntax.const @{syntax_const "_constrain"} $ Syntax.const @{const_syntax "cEnum"} $
       (Syntax.const @{type_syntax option} $ 
         (Syntax.const @{type_syntax prod} $
           (Syntax.const @{type_syntax list} $ ty) $
           (Syntax.const @{type_syntax prod} $
             (Syntax.const @{type_syntax fun} $
               (Syntax.const @{type_syntax fun} $ ty $ (Syntax.const @{type_syntax bool})) $
               (Syntax.const @{type_syntax bool})) $
             (Syntax.const @{type_syntax fun} $
               (Syntax.const @{type_syntax fun} $ ty $ (Syntax.const @{type_syntax bool})) $
               (Syntax.const @{type_syntax bool}))))))
    | cenum_tr ts = raise TERM ("cenum_tr", ts);
in [(@{syntax_const "_CENUM"}, K cenum_tr)] end
\<close>

typed_print_translation \<open>
let
  fun cenum_tr' ctxt
    (Type (@{type_name option}, [Type (@{type_name prod}, [Type (@{type_name list}, [T]), _])])) ts =
    Term.list_comb (Syntax.const @{syntax_const "_CENUM"} $ Syntax_Phases.term_of_typ ctxt T, ts)
  | cenum_tr' _ _ _ = raise Match;
in [(@{const_syntax cEnum}, cenum_tr')]
end
\<close>

subsection \<open>Generator for the @{class cenum}-class\<close>

text \<open>
This generator registers itself at the derive-manager for the class @{class cenum}.
To be more precise, one can currently only choose to not support enumeration 
by passing "no" as parameter.  

\begin{itemize}
\item \texttt{instantiation type :: (type,\ldots,type) (no) cenum}
\end{itemize}
\<close>

text \<open>
This generator can be used for arbitrary types, not just datatypes. 
\<close>

ML_file \<open>cenum_generator.ML\<close>


subsection \<open>Instantiations\<close>

context fixes cenum_all :: "('a \<Rightarrow> bool) \<Rightarrow> bool" begin
fun all_n_lists :: "('a list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool"
where [simp del]:
  "all_n_lists P n = (if n = 0 then P [] else cenum_all (\<lambda>x. all_n_lists (\<lambda>xs. P (x # xs)) (n - 1)))"
end


context fixes cenum_ex :: "('a \<Rightarrow> bool) \<Rightarrow> bool" begin
fun ex_n_lists :: "('a list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool"
where [simp del]:
  "ex_n_lists P n \<longleftrightarrow> (if n = 0 then P [] else cenum_ex (%x. ex_n_lists (%xs. P (x # xs)) (n - 1)))"
end

lemma all_n_lists_iff: fixes cenum shows
  "all_n_lists (Ball (set cenum)) P n \<longleftrightarrow> (\<forall>xs \<in> set (List.n_lists n cenum). P xs)"
proof(induct P n rule: all_n_lists.induct)
  case (1 P n)
  show ?case
  proof(cases n)
    case 0
    thus ?thesis by(simp add: all_n_lists.simps)
  next
    case (Suc n')
    thus ?thesis using "1" by(subst all_n_lists.simps) auto
  qed
qed

lemma ex_n_lists_iff: fixes cenum shows
  "ex_n_lists (Bex (set cenum)) P n \<longleftrightarrow> (\<exists>xs \<in> set (List.n_lists n cenum). P xs)"
proof(induct P n rule: ex_n_lists.induct)
  case (1 P n)
  show ?case
  proof(cases n)
    case 0
    thus ?thesis by(simp add: ex_n_lists.simps)
  next
    case (Suc n')
    thus ?thesis using "1" by(subst ex_n_lists.simps) auto
  qed
qed

instantiation "fun" :: (cenum, cenum) cenum begin

definition 
  "CENUM('a \<Rightarrow> 'b) =
  (case ID CENUM('a) of None \<Rightarrow> None | Some (enum_a, enum_all_a, enum_ex_a) \<Rightarrow>
     case ID CENUM('b) of None \<Rightarrow> None | Some (enum_b, enum_all_b, enum_ex_b) \<Rightarrow> Some 
       (map (\<lambda>ys. the o map_of (zip enum_a ys)) (List.n_lists (length enum_a) enum_b),
        \<lambda>P. all_n_lists enum_all_b (\<lambda>bs. P (the o map_of (zip enum_a bs))) (length enum_a),
        \<lambda>P. ex_n_lists enum_ex_b (\<lambda>bs. P (the o map_of (zip enum_a bs))) (length enum_a)))"
instance proof
  fix enum enum_all enum_ex P
  assume "CENUM('a \<Rightarrow> 'b) = Some (enum, enum_all, enum_ex)"
  then obtain enum_a enum_all_a enum_ex_a enum_b enum_all_b enum_ex_b
    where a: "ID CENUM('a) = Some (enum_a, enum_all_a, enum_ex_a)"
    and b: "ID CENUM('b) = Some (enum_b, enum_all_b, enum_ex_b)"
    and enum: "enum = map (\<lambda>ys. the o map_of (zip enum_a ys)) (List.n_lists (length enum_a) enum_b)"
    and enum_all: "enum_all = (\<lambda>P. all_n_lists enum_all_b (\<lambda>bs. P (the o map_of (zip enum_a bs))) (length enum_a))"
    and enum_ex: "enum_ex = (\<lambda>P. ex_n_lists enum_ex_b (\<lambda>bs. P (the o map_of (zip enum_a bs))) (length enum_a))"
    by(fastforce simp add: cEnum_fun_def split: option.split_asm)
  
  show "UNIV = set enum"
  proof (rule UNIV_eq_I)
    fix f :: "'a \<Rightarrow> 'b"
    have "f = the \<circ> map_of (zip enum_a (map f enum_a))"
      by (auto simp add: map_of_zip_map fun_eq_iff intro: in_cenum[OF a])
    then show "f \<in> set enum"
      by (auto simp add: enum set_n_lists intro: in_cenum[OF b])
  qed

  show "enum_all P = Ball UNIV P"
  proof
    assume "enum_all P"
    show "Ball UNIV P"
    proof
      fix f :: "'a \<Rightarrow> 'b"
      have f: "f = the \<circ> map_of (zip (enum_a) (map f enum_a))"
        by (auto simp add: map_of_zip_map fun_eq_iff intro: in_cenum[OF a])
      from \<open>enum_all P\<close> have "P (the \<circ> map_of (zip enum_a (map f enum_a)))"
        apply(simp add: enum_all ID_cEnum[OF b] all_n_lists_iff set_n_lists)
        apply(erule allE, erule mp)
        apply(auto simp add: in_cenum[OF b])
        done
      with f show "P f" by simp
    qed
  next
    assume "Ball UNIV P"
    from this show "enum_all P"
      by(simp add: enum_all ID_cEnum[OF b] all_n_lists_iff)
  qed

  show "enum_ex P = Bex UNIV P"
  proof
    assume "enum_ex P"
    from this show "Bex UNIV P"
      by(auto simp add: enum_ex ID_cEnum[OF b] ex_n_lists_iff)
  next
    assume "Bex UNIV P"
    from this obtain f where "P f" ..
    also have f: "f = the \<circ> map_of (zip (enum_a) (map f enum_a))"
      by (auto simp add: map_of_zip_map fun_eq_iff intro: in_cenum[OF a])
    finally show "enum_ex P"
      apply(simp add: enum_ex ID_cEnum[OF b] ex_n_lists_iff o_def)
      apply(erule bexI)
      apply(auto simp add: set_n_lists intro!: in_cenum[OF b])
      done
  qed
qed
end

instantiation set :: (cenum) cenum begin
definition
  "CENUM('a set) =
  (case ID CENUM('a) of None \<Rightarrow> None | Some (enum_a, enum_all_a, enum_ex_a) \<Rightarrow> Some 
    (map set (subseqs enum_a),
     \<lambda>P. list_all P (map set (subseqs enum_a)),
     \<lambda>P. list_ex P (map set (subseqs enum_a))))"
instance 
  by(intro_classes)(auto simp add: cEnum_set_def subseqs_powset list_ex_iff list_all_iff split: option.split_asm dest!: ID_cEnum)
end

instantiation unit :: cenum begin
definition "CENUM(unit) = Some (enum_class.enum, enum_class.enum_all, enum_class.enum_ex)"
instance by(intro_classes)(auto simp add: cEnum_unit_def enum_UNIV enum_all_UNIV enum_ex_UNIV)
end

instantiation bool :: cenum begin
definition "CENUM(bool) = Some (enum_class.enum, enum_class.enum_all, enum_class.enum_ex)"
instance by(intro_classes)(auto simp add: cEnum_bool_def enum_UNIV enum_all_UNIV enum_ex_UNIV)
end

instantiation prod :: (cenum, cenum) cenum begin
definition 
  "CENUM('a \<times> 'b) =
  (case ID CENUM('a) of None \<Rightarrow> None | Some (enum_a, enum_all_a, enum_ex_a) \<Rightarrow>
     case ID CENUM('b) of None \<Rightarrow> None | Some (enum_b, enum_all_b, enum_ex_b) \<Rightarrow> Some 
       (List.product enum_a enum_b,
        \<lambda>P. enum_all_a (%x. enum_all_b (%y. P (x, y))),
        \<lambda>P. enum_ex_a (%x. enum_ex_b (%y. P (x, y)))))"
instance
  by(intro_classes)(auto 4 4 simp add: cEnum_prod_def split: option.split_asm dest!: ID_cEnum)
end

instantiation sum :: (cenum, cenum) cenum begin
definition 
  "CENUM('a + 'b) =
  (case ID CENUM('a) of None \<Rightarrow> None | Some (enum_a, enum_all_a, enum_ex_a) \<Rightarrow>
     case ID CENUM('b) of None \<Rightarrow> None | Some (enum_b, enum_all_b, enum_ex_b) \<Rightarrow> Some 
       (map Inl enum_a @ map Inr enum_b,
        \<lambda>P. enum_all_a (\<lambda>x. P (Inl x)) \<and> enum_all_b (\<lambda>x. P (Inr x)),
        \<lambda>P. enum_ex_a (\<lambda>x. P (Inl x)) \<or> enum_ex_b (\<lambda>x. P (Inr x))))"
instance
  by(intro_classes)(auto 4 4 simp add: cEnum_sum_def UNIV_sum split: option.split_asm dest!: ID_cEnum)
end

instantiation option :: (cenum) cenum begin
definition
  "CENUM('a option) =
  (case ID CENUM('a) of None \<Rightarrow> None | Some (enum_a, enum_all_a, enum_ex_a) \<Rightarrow> Some 
    (None # map Some enum_a,
     \<lambda>P. P None \<and> enum_all_a (\<lambda>x. P (Some x)),
     \<lambda>P. P None \<or> enum_ex_a (\<lambda>x. P (Some x))))"
instance 
  by(intro_classes)(auto simp add: cEnum_option_def UNIV_option_conv split: option.split_asm dest: ID_cEnum)
end

instantiation Enum.finite_1 :: cenum begin
definition "CENUM(Enum.finite_1) = Some (enum_class.enum, enum_class.enum_all, enum_class.enum_ex)"
instance by(intro_classes)(auto simp add: cEnum_finite_1_def enum_UNIV enum_all_UNIV enum_ex_UNIV)
end

instantiation Enum.finite_2 :: cenum begin
definition "CENUM(Enum.finite_2) = Some (enum_class.enum, enum_class.enum_all, enum_class.enum_ex)"
instance by(intro_classes)(auto simp add: cEnum_finite_2_def enum_UNIV enum_all_UNIV enum_ex_UNIV)
end

instantiation Enum.finite_3 :: cenum begin
definition "CENUM(Enum.finite_3) = Some (enum_class.enum, enum_class.enum_all, enum_class.enum_ex)"
instance by(intro_classes)(auto simp add: cEnum_finite_3_def enum_UNIV enum_all_UNIV enum_ex_UNIV)
end

instantiation Enum.finite_4 :: cenum begin
definition "CENUM(Enum.finite_4) = Some (enum_class.enum, enum_class.enum_all, enum_class.enum_ex)"
instance by(intro_classes)(auto simp add: cEnum_finite_4_def enum_UNIV enum_all_UNIV enum_ex_UNIV)
end

instantiation Enum.finite_5 :: cenum begin
definition "CENUM(Enum.finite_5) = Some (enum_class.enum, enum_class.enum_all, enum_class.enum_ex)"
instance by(intro_classes)(auto simp add: cEnum_finite_5_def enum_UNIV enum_all_UNIV enum_ex_UNIV)
end

instantiation char :: cenum begin
definition "CENUM(char) = Some (enum_class.enum, enum_class.enum_all, enum_class.enum_ex)"
instance by(intro_classes)(auto simp add: cEnum_char_def enum_UNIV enum_all_UNIV enum_ex_UNIV)
end

derive (no) cenum list nat int integer natural String.literal

end
