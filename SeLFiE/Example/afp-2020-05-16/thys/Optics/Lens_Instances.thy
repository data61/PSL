section \<open>Lens Instances\<close>

theory Lens_Instances
  imports Lens_Order Lens_Symmetric "HOL-Eisbach.Eisbach"
  keywords "alphabet" :: "thy_defn"
begin

text \<open>In this section we define a number of concrete instantiations of the lens locales, including
  functions lenses, list lenses, and record lenses.\<close>

subsection \<open>Function Lens\<close>

text \<open>A function lens views the valuation associated with a particular domain element @{typ "'a"}.
      We require that range type of a lens function has cardinality of at least 2; this ensures
      that properties of independence are provable.\<close>

definition fun_lens :: "'a \<Rightarrow> ('b::two \<Longrightarrow> ('a \<Rightarrow> 'b))" where
[lens_defs]: "fun_lens x = \<lparr> lens_get = (\<lambda> f. f x), lens_put = (\<lambda> f u. f(x := u)) \<rparr>"

lemma fun_vwb_lens: "vwb_lens (fun_lens x)"
  by (unfold_locales, simp_all add: fun_lens_def)

text \<open>Two function lenses are independent if and only if the domain elements are different.\<close>
    
lemma fun_lens_indep:
  "fun_lens x \<bowtie> fun_lens y \<longleftrightarrow> x \<noteq> y"
proof -
  obtain u v :: "'a::two" where "u \<noteq> v"
    using two_diff by auto
  thus ?thesis
    by (auto simp add: fun_lens_def lens_indep_def)
qed

subsection \<open>Function Range Lens\<close>
  
text \<open>The function range lens allows us to focus on a particular region of a function's range.\<close>

definition fun_ran_lens :: "('c \<Longrightarrow> 'b) \<Rightarrow> (('a \<Rightarrow> 'b) \<Longrightarrow> '\<alpha>) \<Rightarrow> (('a \<Rightarrow> 'c) \<Longrightarrow> '\<alpha>)" where
[lens_defs]: "fun_ran_lens X Y = \<lparr> lens_get = \<lambda> s. get\<^bsub>X\<^esub> \<circ> get\<^bsub>Y\<^esub> s
                                 , lens_put = \<lambda> s v. put\<^bsub>Y\<^esub> s (\<lambda> x::'a. put\<^bsub>X\<^esub> (get\<^bsub>Y\<^esub> s x) (v x)) \<rparr>"

lemma fun_ran_mwb_lens: "\<lbrakk> mwb_lens X; mwb_lens Y \<rbrakk> \<Longrightarrow> mwb_lens (fun_ran_lens X Y)"
  by (unfold_locales, auto simp add: fun_ran_lens_def)

lemma fun_ran_wb_lens: "\<lbrakk> wb_lens X; wb_lens Y \<rbrakk> \<Longrightarrow> wb_lens (fun_ran_lens X Y)"
  by (unfold_locales, auto simp add: fun_ran_lens_def)

lemma fun_ran_vwb_lens: "\<lbrakk> vwb_lens X; vwb_lens Y \<rbrakk> \<Longrightarrow> vwb_lens (fun_ran_lens X Y)"
  by (unfold_locales, auto simp add: fun_ran_lens_def)

subsection \<open>Map Lens\<close>

text \<open>The map lens allows us to focus on a particular region of a partial function's range. It
  is only a mainly well-behaved lens because it does not satisfy the PutGet law when the view
  is not in the domain.\<close> 
  
definition map_lens :: "'a \<Rightarrow> ('b \<Longrightarrow> ('a \<rightharpoonup> 'b))" where
[lens_defs]: "map_lens x = \<lparr> lens_get = (\<lambda> f. the (f x)), lens_put = (\<lambda> f u. f(x \<mapsto> u)) \<rparr>"

lemma map_mwb_lens: "mwb_lens (map_lens x)"
  by (unfold_locales, simp_all add: map_lens_def)

lemma source_map_lens: "\<S>\<^bsub>map_lens x\<^esub> = {f. x \<in> dom(f)}"
  by (force simp add: map_lens_def lens_source_def)

subsection \<open>List Lens\<close>

text \<open>The list lens allows us to view a particular element of a list. In order to show it is mainly
  well-behaved we need to define to additional list functions. The following function adds 
  a number undefined elements to the end of a list.\<close>
  
definition list_pad_out :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
"list_pad_out xs k = xs @ replicate (k + 1 - length xs) undefined"

text \<open>The following function is like @{term "list_update"} but it adds additional elements to the
  list if the list isn't long enough first.\<close>

definition list_augment :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
"list_augment xs k v = (list_pad_out xs k)[k := v]"

text \<open>The following function is like @{term nth} but it expressly returns @{term undefined} when
  the list isn't long enough.\<close>

definition nth' :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" where
"nth' xs i = (if (length xs > i) then xs ! i else undefined)"

text \<open>We can prove some additional laws about list update and append.\<close>

lemma list_update_append_lemma1: "i < length xs \<Longrightarrow> xs[i := v] @ ys = (xs @ ys)[i := v]"
  by (simp add: list_update_append)

lemma list_update_append_lemma2: "i < length ys \<Longrightarrow> xs @ ys[i := v] = (xs @ ys)[i + length xs := v]"
  by (simp add: list_update_append)

text \<open>We can also prove some laws about our new operators.\<close>
    
lemma nth'_0 [simp]: "nth' (x # xs) 0 = x"
  by (simp add: nth'_def)

lemma nth'_Suc [simp]: "nth' (x # xs) (Suc n) = nth' xs n"
  by (simp add: nth'_def)

lemma list_augment_0 [simp]:
  "list_augment (x # xs) 0 y = y # xs"
  by (simp add: list_augment_def list_pad_out_def)

lemma list_augment_Suc [simp]:
  "list_augment (x # xs) (Suc n) y = x # list_augment xs n y"
  by (simp add: list_augment_def list_pad_out_def)

lemma list_augment_twice:
  "list_augment (list_augment xs i u) j v = (list_pad_out xs (max i j))[i:=u, j:=v]"
  apply (auto simp add: list_augment_def list_pad_out_def list_update_append_lemma1 replicate_add[THEN sym] max_def)
  apply (metis Suc_le_mono add.commute diff_diff_add diff_le_mono le_add_diff_inverse2)
done

lemma list_augment_last [simp]:
  "list_augment (xs @ [y]) (length xs) z = xs @ [z]"
  by (induct xs, simp_all)

lemma list_augment_idem [simp]:
  "i < length xs \<Longrightarrow> list_augment xs i (xs ! i) = xs"
  by (simp add: list_augment_def list_pad_out_def)

text \<open>We can now prove that @{term list_augment} is commutative for different (arbitrary) indices.\<close>
  
lemma list_augment_commute:
  "i \<noteq> j \<Longrightarrow> list_augment (list_augment \<sigma> j v) i u = list_augment (list_augment \<sigma> i u) j v"
  by (simp add: list_augment_twice list_update_swap max.commute)

text \<open>We can also prove that we can always retrieve an element we have added to the list, since
  @{term list_augment} extends the list when necessary. This isn't true of @{term list_update}. \<close>
    
lemma nth_list_augment: "list_augment xs k v ! k = v"
  by (simp add: list_augment_def list_pad_out_def)
    
lemma nth'_list_augment: "nth' (list_augment xs k v) k = v"
  by (auto simp add: nth'_def nth_list_augment list_augment_def list_pad_out_def)

text \<open> The length is expanded if not already long enough, or otherwise left as it is. \<close>

lemma length_list_augment_1: "k \<ge> length xs \<Longrightarrow> length (list_augment xs k v) = Suc k"
  by (simp add: list_augment_def list_pad_out_def)

lemma length_list_augment_2: "k < length xs \<Longrightarrow> length (list_augment xs k v) = length xs"
  by (simp add: list_augment_def list_pad_out_def)

text \<open>We also have it that @{term list_augment} cancels itself.\<close>
    
lemma list_augment_same_twice: "list_augment (list_augment xs k u) k v = list_augment xs k v"
  by (simp add: list_augment_def list_pad_out_def)

lemma nth'_list_augment_diff: "i \<noteq> j \<Longrightarrow> nth' (list_augment \<sigma> i v) j = nth' \<sigma> j"
  by (auto simp add: list_augment_def list_pad_out_def nth_append nth'_def)

text \<open>Finally we can create the list lenses, of which there are three varieties. One that allows
  us to view an index, one that allows us to view the head, and one that allows us to view the tail.
  They are all mainly well-behaved lenses.\<close>
    
definition list_lens :: "nat \<Rightarrow> ('a::two \<Longrightarrow> 'a list)" where
[lens_defs]: "list_lens i = \<lparr> lens_get = (\<lambda> xs. nth' xs i)
                            , lens_put = (\<lambda> xs x. list_augment xs i x) \<rparr>"

abbreviation hd_lens ("hd\<^sub>L") where "hd_lens \<equiv> list_lens 0"

definition tl_lens :: "'a list \<Longrightarrow> 'a list" ("tl\<^sub>L") where
[lens_defs]: "tl_lens = \<lparr> lens_get = (\<lambda> xs. tl xs)
                        , lens_put = (\<lambda> xs xs'. hd xs # xs') \<rparr>"

lemma list_mwb_lens: "mwb_lens (list_lens x)"
  by (unfold_locales, simp_all add: list_lens_def nth'_list_augment list_augment_same_twice)

text \<open> The set of constructible sources is precisely those where the length is greater than the
  given index. \<close>

lemma source_list_lens: "\<S>\<^bsub>list_lens i\<^esub> = {xs. length xs > i}"
  apply (auto simp add: lens_source_def list_lens_def)
   apply (metis length_list_augment_1 length_list_augment_2 lessI not_less)
  apply (metis list_augment_idem)
  done

lemma tail_lens_mwb:
  "mwb_lens tl\<^sub>L"
  by (unfold_locales, simp_all add: tl_lens_def)

lemma source_tail_lens: "\<S>\<^bsub>tl\<^sub>L\<^esub> = {xs. xs \<noteq> []}"
  using list.exhaust_sel by (auto simp add: tl_lens_def lens_source_def)
  
text \<open>Independence of list lenses follows when the two indices are different.\<close>
    
lemma list_lens_indep:
  "i \<noteq> j \<Longrightarrow> list_lens i \<bowtie> list_lens j"
  by (simp add: list_lens_def lens_indep_def list_augment_commute nth'_list_augment_diff)

lemma hd_tl_lens_indep [simp]:
  "hd\<^sub>L \<bowtie> tl\<^sub>L"
  apply (rule lens_indepI)
    apply (simp_all add: list_lens_def tl_lens_def)
    apply (metis hd_conv_nth hd_def length_greater_0_conv list.case(1) nth'_def nth'_list_augment)
   apply (metis (full_types) hd_conv_nth hd_def length_greater_0_conv list.case(1) nth'_def)
  apply (metis One_nat_def diff_Suc_Suc diff_zero length_0_conv length_list_augment_1 length_tl linorder_not_less list.exhaust list.sel(2) list.sel(3) list_augment_0 not_less_zero)
done

lemma hd_tl_lens_pbij: "pbij_lens (hd\<^sub>L +\<^sub>L tl\<^sub>L)"
  by (unfold_locales, auto simp add: lens_defs)

subsection \<open>Record Field Lenses\<close>

text \<open>We also add support for record lenses. Every record created can yield a lens for each field.
  These cannot be created generically and thus must be defined case by case as new records are
  created. We thus create a new Isabelle outer syntax command \textbf{alphabet} which enables this. 
  We first create syntax that allows us to obtain a lens from a given field using the internal
  record syntax translations.\<close>
  
abbreviation (input) "fld_put f \<equiv> (\<lambda> \<sigma> u. f (\<lambda>_. u) \<sigma>)"

syntax 
  "_FLDLENS" :: "id \<Rightarrow> logic"  ("FLDLENS _")
translations 
  "FLDLENS x" => "\<lparr> lens_get = x, lens_put = CONST fld_put (_update_name x) \<rparr>"

text \<open> We also allow the extraction of the "base lens", which characterises all the fields added
  by a record without the extension. \<close>

syntax
  "_BASELENS" :: "id \<Rightarrow> logic"  ("BASELENS _")

abbreviation (input) "base_lens t e m \<equiv> \<lparr> lens_get = t, lens_put = \<lambda> s v. e v (m s) \<rparr>"

ML \<open>
  fun baselens_tr [Free (name, _)] =
    let
      val extend = Free (name ^ ".extend", dummyT);
      val truncate = Free (name ^ ".truncate", dummyT);
      val more = Free (name ^ ".more", dummyT);
    in
      Const (@{const_syntax "base_lens"}, dummyT) $ truncate $ extend $ more
    end
  | baselens_tr _ = raise Match;
\<close>

parse_translation \<open>[(@{syntax_const "_BASELENS"}, K baselens_tr)]\<close>  

text \<open>We also introduce the \textbf{alphabet} command that creates a record with lenses for each field.
  For each field a lens is created together with a proof that it is very well-behaved, and for each 
  pair of lenses an independence theorem is generated. Alphabets can also be extended which yields 
  sublens proofs between the extension field lens and record extension lenses. \<close>

ML_file \<open>Lens_Record.ML\<close>

text \<open>The following theorem attribute stores splitting theorems for alphabet types which which is useful
  for proof automation.\<close>

named_theorems alpha_splits

subsection \<open>Type Definition Lens\<close>

text \<open> Every type defined by a \<^bold>\<open>typedef\<close> command induces a partial bijective lens constructed
  using the abstraction and representation functions. \<close>

context type_definition
begin

definition typedef_lens :: "'b \<Longrightarrow> 'a" ("typedef\<^sub>L") where
[lens_defs]: "typedef\<^sub>L = \<lparr> lens_get = Abs, lens_put = (\<lambda> s. Rep) \<rparr>"

lemma pbij_typedef_lens [simp]: "pbij_lens typedef\<^sub>L"
  by (unfold_locales, simp_all add: lens_defs Rep_inverse)

lemma source_typedef_lens: "\<S>\<^bsub>typedef\<^sub>L\<^esub> = A"
  using Rep_cases by (auto simp add: lens_source_def lens_defs Rep)

lemma bij_typedef_lens_UNIV: "A = UNIV \<Longrightarrow> bij_lens typedef\<^sub>L"
  by (auto intro: pbij_vwb_is_bij_lens simp add: mwb_UNIV_src_is_vwb_lens source_typedef_lens)

end

subsection \<open>Mapper Lenses\<close>

definition lmap_lens :: 
  "(('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow> ('\<gamma> \<Rightarrow> '\<delta>)) \<Rightarrow> 
   (('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<delta> \<Rightarrow> '\<gamma>) \<Rightarrow> 
   ('\<gamma> \<Rightarrow> '\<alpha>) \<Rightarrow> 
   ('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> 
   ('\<delta> \<Longrightarrow> '\<gamma>)" where
  [lens_defs]:
  "lmap_lens f g h l = \<lparr>
  lens_get = f (get\<^bsub>l\<^esub>),
  lens_put = g o (put\<^bsub>l\<^esub>) o h \<rparr>"
  
text \<open>
  The parse translation below yields a heterogeneous mapping lens for any
  record type. This achieved through the utility function above that
  constructs a functorial lens. This takes as input a heterogeneous mapping
  function that lifts a function on a record's extension type to an update
  on the entire record, and also the record's ``more'' function. The first input
  is given twice as it has different polymorphic types, being effectively
  a type functor construction which are not explicitly supported by HOL. We note 
  that the \<open>more_update\<close> function does something similar to the extension lifting, 
  but is not precisely suitable here since it only considers homogeneous functions, 
  namely of type \<open>'a \<Rightarrow> 'a\<close> rather than \<open>'a \<Rightarrow> 'b\<close>.
\<close>
  
syntax 
  "_lmap" :: "id \<Rightarrow> logic" ("lmap[_]")

ML \<open>
  fun lmap_tr [Free (name, _)] =
    let
      val extend = Free (name ^ ".extend", dummyT);
      val truncate = Free (name ^ ".truncate", dummyT);
      val more = Free (name ^ ".more", dummyT);
      val map_ext = Abs ("f", dummyT,
                    Abs ("r", dummyT,
                      extend $ (truncate $ Bound 0) $ (Bound 1 $ (more $ (Bound 0)))))

    in
      Const (@{const_syntax "lmap_lens"}, dummyT) $ map_ext $ map_ext $ more
    end
  | lmap_tr _ = raise Match;
\<close>

parse_translation \<open>[(@{syntax_const "_lmap"}, K lmap_tr)]\<close>  

subsection \<open>Lens Interpretation\<close>

named_theorems lens_interp_laws

locale lens_interp = interp
begin
declare meta_interp_law [lens_interp_laws]
declare all_interp_law [lens_interp_laws]
declare exists_interp_law [lens_interp_laws]

end

subsection \<open> Tactic \<close>

text \<open> A simple tactic for simplifying lens expressions \<close>

declare split_paired_all [alpha_splits]

method lens_simp = (simp add: alpha_splits lens_defs prod.case_eq_if)

end
