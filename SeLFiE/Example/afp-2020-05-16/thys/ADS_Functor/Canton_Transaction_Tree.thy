theory Canton_Transaction_Tree imports
  Inclusion_Proof_Construction
begin

section \<open>Canton's hierarchical transaction trees\<close>

typedecl view_data
typedecl view_metadata
typedecl common_metadata
typedecl participant_metadata

datatype view = View view_metadata view_data (subviews: "view list")

datatype transaction = Transaction common_metadata participant_metadata (views: "view list")

subsection \<open>Views as authenticated data structures\<close>

type_synonym view_metadata\<^sub>h = "view_metadata blindable\<^sub>h"
type_synonym view_data\<^sub>h = "view_data blindable\<^sub>h"

datatype view\<^sub>h = View\<^sub>h "((view_metadata\<^sub>h \<times>\<^sub>h view_data\<^sub>h) \<times>\<^sub>h view\<^sub>h list\<^sub>h) blindable\<^sub>h"

type_synonym view_metadata\<^sub>m = "(view_metadata, view_metadata) blindable\<^sub>m"
type_synonym view_data\<^sub>m = "(view_data, view_data) blindable\<^sub>m"

datatype view\<^sub>m = View\<^sub>m 
  "((view_metadata\<^sub>m \<times>\<^sub>m view_data\<^sub>m) \<times>\<^sub>m view\<^sub>m list\<^sub>m,
    (view_metadata\<^sub>h \<times>\<^sub>h view_data\<^sub>h) \<times>\<^sub>h view\<^sub>h list\<^sub>h) blindable\<^sub>m"

abbreviation (input) hash_view_data :: "(view_data\<^sub>m, view_data\<^sub>h) hash" where
  "hash_view_data \<equiv> hash_blindable id"
abbreviation (input) blinding_of_view_data :: "view_data\<^sub>m blinding_of" where
  "blinding_of_view_data \<equiv> blinding_of_blindable id (=)"
abbreviation (input) merge_view_data :: "view_data\<^sub>m merge" where
  "merge_view_data \<equiv> merge_blindable id merge_discrete"

lemma merkle_view_data:
  "merkle_interface hash_view_data blinding_of_view_data merge_view_data"
  by unfold_locales

abbreviation (input) hash_view_metadata :: "(view_metadata\<^sub>m, view_metadata\<^sub>h) hash" where
  "hash_view_metadata \<equiv> hash_blindable id"
abbreviation (input) blinding_of_view_metadata :: "view_metadata\<^sub>m blinding_of" where
  "blinding_of_view_metadata \<equiv> blinding_of_blindable id (=)"
abbreviation (input) merge_view_metadata :: "view_metadata\<^sub>m merge" where
  "merge_view_metadata \<equiv> merge_blindable id merge_discrete"

lemma merkle_view_metadata:
  "merkle_interface hash_view_metadata blinding_of_view_metadata merge_view_metadata"
  by unfold_locales

type_synonym view_content = "view_metadata \<times> view_data"
type_synonym view_content\<^sub>h = "view_metadata\<^sub>h \<times>\<^sub>h view_data\<^sub>h"
type_synonym view_content\<^sub>m = "view_metadata\<^sub>m \<times>\<^sub>m view_data\<^sub>m"

locale view_merkle begin

type_synonym view\<^sub>h' = "view_content\<^sub>h rose_tree\<^sub>h"

primrec from_view\<^sub>h :: "view\<^sub>h \<Rightarrow> view\<^sub>h'" where
  "from_view\<^sub>h (View\<^sub>h x) = Tree\<^sub>h (map_blindable\<^sub>h (map_prod id (map from_view\<^sub>h)) x)"

primrec to_view\<^sub>h :: "view\<^sub>h' \<Rightarrow> view\<^sub>h" where
  "to_view\<^sub>h (Tree\<^sub>h x) = View\<^sub>h (map_blindable\<^sub>h (map_prod id (map to_view\<^sub>h)) x)"

lemma from_to_view\<^sub>h [simp]: "from_view\<^sub>h (to_view\<^sub>h x) = x"
  apply(induction x)
  apply(simp add: blindable\<^sub>h.map_comp o_def prod.map_comp)
  apply(simp cong: blindable\<^sub>h.map_cong prod.map_cong list.map_cong add: blindable\<^sub>h.map_id[unfolded id_def])
  done

lemma to_from_view\<^sub>h [simp]: "to_view\<^sub>h (from_view\<^sub>h x) = x"
  apply(induction x)
  apply(simp add: blindable\<^sub>h.map_comp o_def prod.map_comp)
  apply(simp cong: blindable\<^sub>h.map_cong prod.map_cong list.map_cong add: blindable\<^sub>h.map_id[unfolded id_def])
  done

lemma iso_view\<^sub>h: "type_definition from_view\<^sub>h to_view\<^sub>h UNIV"
  by unfold_locales simp_all

setup_lifting iso_view\<^sub>h

lemma cr_view\<^sub>h_Grp: "cr_view\<^sub>h = Grp UNIV to_view\<^sub>h"
  by(simp add: cr_view\<^sub>h_def Grp_def fun_eq_iff)(transfer, auto)

lemma View\<^sub>h_transfer [transfer_rule]: includes lifting_syntax shows
  "(rel_blindable\<^sub>h (rel_prod (=) (list_all2 pcr_view\<^sub>h)) ===> pcr_view\<^sub>h) Tree\<^sub>h View\<^sub>h"
  by(simp add: rel_fun_def view\<^sub>h.pcr_cr_eq cr_view\<^sub>h_Grp list.rel_Grp eq_alt prod.rel_Grp blindable\<^sub>h.rel_Grp)
    (simp add: Grp_def)

type_synonym view\<^sub>m' = "(view_content\<^sub>m, view_content\<^sub>h) rose_tree\<^sub>m"

primrec from_view\<^sub>m :: "view\<^sub>m \<Rightarrow> view\<^sub>m'" where
  "from_view\<^sub>m (View\<^sub>m x) = Tree\<^sub>m (map_blindable\<^sub>m (map_prod id (map from_view\<^sub>m)) (map_prod id (map from_view\<^sub>h)) x)"

primrec to_view\<^sub>m :: "view\<^sub>m' \<Rightarrow> view\<^sub>m" where
  "to_view\<^sub>m (Tree\<^sub>m x) = View\<^sub>m (map_blindable\<^sub>m (map_prod id (map to_view\<^sub>m)) (map_prod id (map to_view\<^sub>h)) x)"

lemma from_to_view\<^sub>m [simp]: "from_view\<^sub>m (to_view\<^sub>m x) = x"
  apply(induction x)
  apply(simp add: blindable\<^sub>m.map_comp o_def prod.map_comp)
  apply(simp cong: blindable\<^sub>m.map_cong prod.map_cong list.map_cong add: blindable\<^sub>m.map_id[unfolded id_def])
  done

lemma to_from_view\<^sub>m [simp]: "to_view\<^sub>m (from_view\<^sub>m x) = x"
  apply(induction x)
  apply(simp add: blindable\<^sub>m.map_comp o_def prod.map_comp)
  apply(simp cong: blindable\<^sub>m.map_cong prod.map_cong list.map_cong add: blindable\<^sub>m.map_id[unfolded id_def])
  done

lemma iso_view\<^sub>m: "type_definition from_view\<^sub>m to_view\<^sub>m UNIV"
  by unfold_locales simp_all

setup_lifting iso_view\<^sub>m

lemma cr_view\<^sub>m_Grp: "cr_view\<^sub>m = Grp UNIV to_view\<^sub>m"
  by(simp add: cr_view\<^sub>m_def Grp_def fun_eq_iff)(transfer, auto)

lemma View\<^sub>m_transfer [transfer_rule]: includes lifting_syntax shows
  "(rel_blindable\<^sub>m (rel_prod (=) (list_all2 pcr_view\<^sub>m)) (rel_prod (=) (list_all2 pcr_view\<^sub>h)) ===> pcr_view\<^sub>m) Tree\<^sub>m View\<^sub>m"
  by(simp add: rel_fun_def view\<^sub>h.pcr_cr_eq view\<^sub>m.pcr_cr_eq cr_view\<^sub>h_Grp cr_view\<^sub>m_Grp list.rel_Grp eq_alt prod.rel_Grp blindable\<^sub>m.rel_Grp)
    (simp add: Grp_def)

end

code_datatype View\<^sub>h
code_datatype View\<^sub>m

context begin
interpretation view_merkle .

abbreviation (input) hash_view_content :: "(view_content\<^sub>m, view_content\<^sub>h) hash" where
  "hash_view_content \<equiv> hash_prod hash_view_metadata hash_view_data"

abbreviation (input) blinding_of_view_content :: "view_content\<^sub>m blinding_of" where
  "blinding_of_view_content \<equiv> blinding_of_prod blinding_of_view_metadata blinding_of_view_data"

abbreviation (input) merge_view_content :: "view_content\<^sub>m merge" where
  "merge_view_content \<equiv> merge_prod merge_view_metadata merge_view_data"

lift_definition hash_view :: "(view\<^sub>m, view\<^sub>h) hash" is
  "hash_tree hash_view_content" .

lift_definition blinding_of_view :: "view\<^sub>m blinding_of" is
  "blinding_of_tree hash_view_content blinding_of_view_content" .

lift_definition merge_view :: "view\<^sub>m merge" is
  "merge_tree hash_view_content merge_view_content" .

lemma merkle_view [locale_witness]: "merkle_interface hash_view blinding_of_view merge_view"
  by transfer unfold_locales

lemma hash_view_simps [simp]:
  "hash_view (View\<^sub>m x) = 
   View\<^sub>h (hash_blindable (hash_prod hash_view_content (hash_list hash_view)) x)"
  by transfer(simp add: hash_rt_F\<^sub>m_def prod.map_comp hash_blindable_def blindable\<^sub>m.map_id)

lemma blinding_of_view_iff [simp]:
  "blinding_of_view (View\<^sub>m x) (View\<^sub>m y) \<longleftrightarrow>
   blinding_of_blindable (hash_prod hash_view_content (hash_list hash_view))
     (blinding_of_prod blinding_of_view_content (blinding_of_list blinding_of_view)) x y"
  by transfer simp

lemma blinding_of_view_induct [consumes 1, induct pred: blinding_of_view]:
  assumes "blinding_of_view x y"
    and "\<And>x y. blinding_of_blindable (hash_prod hash_view_content (hash_list hash_view))
             (blinding_of_prod blinding_of_view_content (blinding_of_list (\<lambda>x y. blinding_of_view x y \<and> P x y))) x y
         \<Longrightarrow> P (View\<^sub>m x) (View\<^sub>m y)"
  shows "P x y"
  using assms by transfer(rule blinding_of_tree.induct)

lemma merge_view_simps [simp]:
  "merge_view (View\<^sub>m x) (View\<^sub>m y) =
   map_option View\<^sub>m (merge_rt_F\<^sub>m hash_view_content merge_view_content hash_view merge_view x y)"
  by transfer simp

end

subsection \<open>Transaction trees as authenticated data structures\<close>

type_synonym common_metadata\<^sub>h = "common_metadata blindable\<^sub>h"
type_synonym common_metadata\<^sub>m = "(common_metadata, common_metadata) blindable\<^sub>m"

type_synonym participant_metadata\<^sub>h = "participant_metadata blindable\<^sub>h"
type_synonym participant_metadata\<^sub>m = "(participant_metadata, participant_metadata) blindable\<^sub>m"

datatype transaction\<^sub>h = Transaction\<^sub>h 
  (the_Transaction\<^sub>h: "((common_metadata\<^sub>h \<times>\<^sub>h participant_metadata\<^sub>h) \<times>\<^sub>h view\<^sub>h list\<^sub>h) blindable\<^sub>h")

datatype transaction\<^sub>m = Transaction\<^sub>m 
  (the_Transaction\<^sub>m: "((common_metadata\<^sub>m \<times>\<^sub>m participant_metadata\<^sub>m) \<times>\<^sub>m view\<^sub>m list\<^sub>m,
    (common_metadata\<^sub>h \<times>\<^sub>h participant_metadata\<^sub>h) \<times>\<^sub>h view\<^sub>h list\<^sub>h) blindable\<^sub>m")

abbreviation (input) hash_common_metadata :: "(common_metadata\<^sub>m, common_metadata\<^sub>h) hash" where
  "hash_common_metadata \<equiv> hash_blindable id"
abbreviation (input) blinding_of_common_metadata :: "common_metadata\<^sub>m blinding_of" where
  "blinding_of_common_metadata \<equiv> blinding_of_blindable id (=)"
abbreviation (input) merge_common_metadata :: "common_metadata\<^sub>m merge" where
  "merge_common_metadata \<equiv> merge_blindable id merge_discrete"

abbreviation (input) hash_participant_metadata :: "(participant_metadata\<^sub>m, participant_metadata\<^sub>h) hash" where
  "hash_participant_metadata \<equiv> hash_blindable id"
abbreviation (input) blinding_of_participant_metadata :: "participant_metadata\<^sub>m blinding_of" where
  "blinding_of_participant_metadata \<equiv> blinding_of_blindable id (=)"
abbreviation (input) merge_participant_metadata :: "participant_metadata\<^sub>m merge" where
  "merge_participant_metadata \<equiv> merge_blindable id merge_discrete"

locale transaction_merkle begin

lemma iso_transaction\<^sub>h: "type_definition the_Transaction\<^sub>h Transaction\<^sub>h UNIV"
  by unfold_locales simp_all

setup_lifting iso_transaction\<^sub>h

lemma Transaction\<^sub>h_transfer [transfer_rule]: includes lifting_syntax shows
  "((=) ===> pcr_transaction\<^sub>h) id Transaction\<^sub>h"
  by(simp add: transaction\<^sub>h.pcr_cr_eq cr_transaction\<^sub>h_def rel_fun_def)

lemma iso_transaction\<^sub>m: "type_definition the_Transaction\<^sub>m Transaction\<^sub>m UNIV"
  by unfold_locales simp_all

setup_lifting iso_transaction\<^sub>m

lemma Transaction\<^sub>m_transfer [transfer_rule]: includes lifting_syntax shows
  "((=) ===> pcr_transaction\<^sub>m) id Transaction\<^sub>m"
  by(simp add: transaction\<^sub>m.pcr_cr_eq cr_transaction\<^sub>m_def rel_fun_def)

end

code_datatype Transaction\<^sub>h
code_datatype Transaction\<^sub>m

context begin
interpretation transaction_merkle .

lift_definition hash_transaction :: "(transaction\<^sub>m, transaction\<^sub>h) hash" is
  "hash_blindable (hash_prod (hash_prod hash_common_metadata hash_participant_metadata) (hash_list hash_view))" .

lift_definition blinding_of_transaction :: "transaction\<^sub>m blinding_of" is
  "blinding_of_blindable 
     (hash_prod (hash_prod hash_common_metadata hash_participant_metadata) (hash_list hash_view))
     (blinding_of_prod (blinding_of_prod blinding_of_common_metadata blinding_of_participant_metadata) (blinding_of_list blinding_of_view))" .

lift_definition merge_transaction :: "transaction\<^sub>m merge" is
  "merge_blindable
     (hash_prod (hash_prod hash_common_metadata hash_participant_metadata) (hash_list hash_view))
     (merge_prod (merge_prod merge_common_metadata merge_participant_metadata) (merge_list merge_view))" .

lemma merkle_transaction [locale_witness]:
  "merkle_interface hash_transaction blinding_of_transaction merge_transaction"
  by transfer unfold_locales

lemmas hash_transaction_simps [simp] = hash_transaction.abs_eq
lemmas blinding_of_transaction_iff [simp] = blinding_of_transaction.abs_eq
lemmas merge_transaction_simps [simp] = merge_transaction.abs_eq

end

interpretation transaction:
  merkle_interface hash_transaction blinding_of_transaction merge_transaction 
  by(rule merkle_transaction)

subsection \<open>
Constructing authenticated data structures for views
\<close>

context view_merkle begin

type_synonym view' = "(view_metadata \<times> view_data) rose_tree"

primrec from_view :: "view \<Rightarrow> view'" where
  "from_view (View vm vd vs) = Tree ((vm, vd), map from_view vs)"

primrec to_view :: "view' \<Rightarrow> view" where
  "to_view (Tree x) = View (fst (fst x)) (snd (fst x)) (snd (map_prod id (map to_view) x))"

lemma from_to_view [simp]: "from_view (to_view x) = x"
  by(induction x)(clarsimp cong: map_cong)

lemma to_from_view [simp]: "to_view (from_view x) = x"
  by(induction x)(clarsimp cong: map_cong)

lemma iso_view: "type_definition from_view to_view UNIV"
  by unfold_locales simp_all

setup_lifting iso_view

definition View' :: "(view_metadata \<times> view_data) \<times> view list \<Rightarrow> view" where
  "View' = (\<lambda>((vm, vd), vs). View vm vd vs)"

lemma View_View': "View = (\<lambda>vm vd vs. View' ((vm, vd), vs))"
  by(simp add: View'_def)

lemma cr_view_Grp: "cr_view = Grp UNIV to_view"
  by(simp add: cr_view_def Grp_def fun_eq_iff)(transfer, auto)

lemma View'_transfer [transfer_rule]: includes lifting_syntax shows
  "(rel_prod (=) (list_all2 pcr_view) ===> pcr_view) Tree View'"
  by(simp add: view.pcr_cr_eq cr_view_Grp eq_alt prod.rel_Grp rose_tree.rel_Grp list.rel_Grp)
    (auto simp add: Grp_def View'_def)

end

code_datatype View

context begin
interpretation view_merkle .

abbreviation embed_view_content :: "view_metadata \<times> view_data \<Rightarrow> view_metadata\<^sub>m \<times> view_data\<^sub>m" where
  "embed_view_content \<equiv> map_prod Unblinded Unblinded"

lift_definition embed_view :: "view \<Rightarrow> view\<^sub>m" is "embed_source_tree embed_view_content" .

lemma embed_view_simps [simp]:
  "embed_view (View vm vd vs) = View\<^sub>m (Unblinded ((Unblinded vm, Unblinded vd), map embed_view vs))"
  unfolding View_View' by transfer simp

end

context transaction_merkle begin

primrec the_Transaction :: "transaction \<Rightarrow> (common_metadata \<times> participant_metadata) \<times> view list" where
  "the_Transaction (Transaction cm pm views) = ((cm, pm), views)" for views

definition Transaction' :: "(common_metadata \<times> participant_metadata) \<times> view list \<Rightarrow> transaction" where
  "Transaction' = (\<lambda>((cm, pm), views). Transaction cm pm views)"

lemma Transaction_Transaction': "Transaction = (\<lambda>cm pm views. Transaction' ((cm, pm), views))"
  by(simp add: Transaction'_def)

lemma the_Transaction_inverse [simp]: "Transaction' (the_Transaction x) = x" 
  by(cases x)(simp add: Transaction'_def)

lemma Transaction'_inverse [simp]: "the_Transaction (Transaction' x) = x"
  by(simp add: Transaction'_def split_def)

lemma iso_transaction: "type_definition the_Transaction Transaction' UNIV"
  by unfold_locales simp_all

setup_lifting iso_transaction

lemma Transaction'_transfer [transfer_rule]: includes lifting_syntax shows
  "((=) ===> pcr_transaction) id Transaction'"
  by(simp add: transaction.pcr_cr_eq cr_transaction_def rel_fun_def)

end

code_datatype Transaction

context begin
interpretation transaction_merkle .

lift_definition embed_transaction :: "transaction \<Rightarrow> transaction\<^sub>m" is
  "Unblinded \<circ> map_prod (map_prod Unblinded Unblinded) (map embed_view)" .

lemma embed_transaction_simps [simp]:
  "embed_transaction (Transaction cm pm views) =
   Transaction\<^sub>m (Unblinded ((Unblinded cm, Unblinded pm), map embed_view views))" 
  for views unfolding Transaction_Transaction' by transfer simp

end

subsubsection \<open>Inclusion proof for the mediator\<close>

primrec mediator_view :: "view \<Rightarrow> view\<^sub>m" where
  "mediator_view (View vm vd vs) =
   View\<^sub>m (Unblinded ((Unblinded vm, Blinded (Content vd)), map mediator_view vs))"

primrec mediator_transaction_tree :: "transaction \<Rightarrow> transaction\<^sub>m" where
  "mediator_transaction_tree (Transaction cm pm views) =
   Transaction\<^sub>m (Unblinded ((Unblinded cm, Blinded (Content pm)), map mediator_view views))"
  for views

lemma blinding_of_mediator_view [simp]: "blinding_of_view (mediator_view view) (embed_view view)"
  by(induction view)(auto simp add: list.rel_map intro!: list.rel_refl_strong)

lemma blinding_of_mediator_transaction_tree:
  "blinding_of_transaction (mediator_transaction_tree tt) (embed_transaction tt)"
  by(cases tt)(auto simp add: list.rel_map intro: list.rel_refl_strong)

subsubsection \<open>Inclusion proofs for participants\<close>

text \<open>Next, we define a function for producing all transaction views from a given view,
  and prove its properties.\<close>

type_synonym view_path_elem = "(view_metadata \<times> view_data) blindable \<times> view list \<times> view list"
type_synonym view_path = "view_path_elem list"
type_synonym view_zipper = "view_path \<times> view"

type_synonym view_path_elem\<^sub>m = "(view_metadata\<^sub>m \<times>\<^sub>m view_data\<^sub>m) \<times> view\<^sub>m list\<^sub>m \<times> view\<^sub>m list\<^sub>m"
type_synonym view_path\<^sub>m = "view_path_elem\<^sub>m list"
type_synonym view_zipper\<^sub>m = "view_path\<^sub>m \<times> view\<^sub>m"

context begin
interpretation view_merkle .

lift_definition zipper_of_view :: "view \<Rightarrow> view_zipper" is zipper_of_tree .
lift_definition view_of_zipper :: "view_zipper \<Rightarrow> view" is tree_of_zipper .

lift_definition zipper_of_view\<^sub>m :: "view\<^sub>m \<Rightarrow> view_zipper\<^sub>m" is zipper_of_tree\<^sub>m .
lift_definition view_of_zipper\<^sub>m :: "view_zipper\<^sub>m \<Rightarrow> view\<^sub>m" is tree_of_zipper\<^sub>m .

lemma view_of_zipper\<^sub>m_Nil [simp]: "view_of_zipper\<^sub>m ([], t) = t"
  by transfer simp

lift_definition blind_view_path_elem :: "view_path_elem \<Rightarrow> view_path_elem\<^sub>m" is
  "blind_path_elem embed_view_content hash_view_content" .

lift_definition blind_view_path :: "view_path \<Rightarrow> view_path\<^sub>m" is
  "blind_path embed_view_content hash_view_content" .

lift_definition embed_view_path_elem :: "view_path_elem \<Rightarrow> view_path_elem\<^sub>m" is
  "embed_path_elem embed_view_content" .

lift_definition embed_view_path :: "view_path \<Rightarrow> view_path\<^sub>m" is
  "embed_path embed_view_content" .

lift_definition hash_view_path_elem :: "view_path_elem\<^sub>m \<Rightarrow> (view_content\<^sub>h \<times> view\<^sub>h list \<times> view\<^sub>h list)" is
  "hash_path_elem hash_view_content" .

lift_definition zippers_view :: "view_zipper \<Rightarrow> view_zipper\<^sub>m list" is
  "zippers_rose_tree embed_view_content hash_view_content" .

lemma embed_view_path_Nil [simp]: "embed_view_path [] = []"
  by transfer(simp add: embed_path_def)

lemma zippers_view_same_hash:
  assumes "z \<in> set (zippers_view (p, t))"
  shows "hash_view (view_of_zipper\<^sub>m z) = hash_view (view_of_zipper\<^sub>m (embed_view_path p, embed_view t))"
  using assms by transfer(rule zippers_rose_tree_same_hash')

lemma zippers_view_blinding_of:
  assumes "z \<in> set (zippers_view (p, t))"
  shows "blinding_of_view (view_of_zipper\<^sub>m z) (view_of_zipper\<^sub>m (blind_view_path p, embed_view t))"
  using assms by transfer(rule zippers_rose_tree_blinding_of, unfold_locales)

end

primrec blind_view :: "view \<Rightarrow> view\<^sub>m" where
  "blind_view (View vm vd subviews) = 
   View\<^sub>m (Blinded (Content ((Content vm, Content vd), map (hash_view \<circ> embed_view) subviews)))"
  for subviews

lemma hash_blind_view: "hash_view (blind_view view) = hash_view (embed_view view)"
  by(cases view) simp

primrec blind_transaction :: "transaction \<Rightarrow> transaction\<^sub>m" where
  "blind_transaction (Transaction cm pm views) = 
   Transaction\<^sub>m (Blinded (Content ((Content cm, Content pm), map (hash_view \<circ> blind_view) views)))"
  for views

lemma hash_blind_transaction:
  "hash_transaction (blind_transaction transaction) = hash_transaction (embed_transaction transaction)"
  by(cases transaction)(simp add: hash_blind_view)


typedecl participant
consts recipients :: "view_metadata \<Rightarrow> participant list"

fun view_recipients :: "view\<^sub>m \<Rightarrow> participant set" where
  "view_recipients (View\<^sub>m (Unblinded ((Unblinded vm, vd), subviews))) = set (recipients vm)" for subviews
| "view_recipients _ = {}" \<comment> \<open>Sane default case\<close>

context fixes participant :: participant begin

definition view_trees_for :: "view \<Rightarrow> view\<^sub>m list" where
  "view_trees_for view =
   map view_of_zipper\<^sub>m
     (filter (\<lambda>(_, t). participant \<in> view_recipients t) 
       (zippers_view ([], view)))"

primrec transaction_views_for :: "transaction \<Rightarrow> transaction\<^sub>m list" where
  "transaction_views_for (Transaction cm pm views) =
   map (\<lambda>view\<^sub>m. Transaction\<^sub>m (Unblinded ((Unblinded cm, Unblinded pm), view\<^sub>m)))
  (concat (map (\<lambda>(l, v, r). map (\<lambda>v\<^sub>m. map blind_view l @ [v\<^sub>m] @ map blind_view r) (view_trees_for v)) (splits views)))"
  for views
   
lemma view_trees_for_same_hash:
  "vt \<in> set (view_trees_for view) \<Longrightarrow> hash_view vt = hash_view (embed_view view)"
  by(auto simp add: view_trees_for_def dest: zippers_view_same_hash)

lemma transaction_views_for_same_hash:
  "t\<^sub>m \<in> set (transaction_views_for t) \<Longrightarrow> hash_transaction t\<^sub>m = hash_transaction (embed_transaction t)"
  by(cases t)(clarsimp simp add: splits_iff hash_blind_view view_trees_for_same_hash)

definition transaction_projection_for :: "transaction \<Rightarrow> transaction\<^sub>m" where
  "transaction_projection_for t =
   (let tvs = transaction_views_for t
    in if tvs = [] then blind_transaction t else the (transaction.Merge (set tvs)))"

lemma transaction_projection_for_same_hash:
  "hash_transaction (transaction_projection_for t) = hash_transaction (embed_transaction t)"
proof(cases "transaction_views_for t = []")
  case True thus ?thesis by(simp add: transaction_projection_for_def Let_def hash_blind_transaction)
next
  case False
  then have "transaction.Merge (set (transaction_views_for t)) \<noteq> None"
    by(intro transaction.Merge_defined)(auto simp add: transaction_views_for_same_hash)
  with False show ?thesis
    apply(clarsimp simp add: transaction_projection_for_def neq_Nil_conv simp del: transaction.Merge_insert)
    apply(drule transaction.Merge_hash[symmetric], blast)
    apply(auto intro: transaction_views_for_same_hash)
    done
qed

lemma transaction_projection_for_upper:
  assumes "t\<^sub>m \<in> set (transaction_views_for t)"
  shows "blinding_of_transaction t\<^sub>m (transaction_projection_for t)"
proof -
  from assms have "transaction.Merge (set (transaction_views_for t)) \<noteq> None"
    by(intro transaction.Merge_defined)(auto simp add: transaction_views_for_same_hash)
  with assms show ?thesis
    by(auto simp add: transaction_projection_for_def Let_def dest: transaction.Merge_upper)
qed

end

end