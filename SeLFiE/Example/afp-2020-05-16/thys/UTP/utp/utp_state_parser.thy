section \<open> State Variable Declaration Parser \<close>

theory utp_state_parser
  imports "utp_rel"
begin

text \<open> This theory sets up a parser for state blocks, as an alternative way of providing lenses to
  a predicate. A program with local variables can be represented by a predicate indexed by a tuple
  of lenses, where each lens represents a variable. These lenses must then be supplied with respect
  to a suitable state space. Instead of creating a type to represent this alphabet, we can create
  a product type for the state space, with an entry for each variable. Then each variable becomes
  a composition of the @{term fst\<^sub>L} and @{term snd\<^sub>L} lenses to index the correct position in the
  variable vector. 

  We first creation a vacuous definition that will mark when an indexed predicate denotes a state
  block. \<close>

definition state_block :: "('v \<Rightarrow> 'p) \<Rightarrow> 'v \<Rightarrow> 'p" where
[upred_defs]: "state_block f x = f x"

text \<open> We declare a number of syntax translations to produce lens and product types, to obtain
  a type for the overall state space, to construct a tuple that denotes the lens vector parameter, 
  to construct the vector itself, and finally to construct the state declaration. \<close>

syntax
  "_lensT" :: "type \<Rightarrow> type \<Rightarrow> type" ("LENSTYPE'(_, _')")
  "_pairT" :: "type \<Rightarrow> type \<Rightarrow> type" ("PAIRTYPE'(_, _')")
  "_state_type" :: "pttrn \<Rightarrow> type"
  "_state_tuple" :: "type \<Rightarrow> pttrn \<Rightarrow> logic"
  "_state_lenses" :: "pttrn \<Rightarrow> logic"
  "_state_decl" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("LOCAL _ \<bullet> _" [0, 10] 10) 

translations
  (type) "PAIRTYPE('a, 'b)" => (type) "'a \<times> 'b"
  (type) "LENSTYPE('a, 'b)" => (type) "'a \<Longrightarrow> 'b"

  "_state_type (_constrain x t)" => "t"
  "_state_type (CONST Pair (_constrain x t) vs)" => "_pairT t (_state_type vs)"

  "_state_tuple st (_constrain x t)" => "_constrain x (_lensT t st)"
  "_state_tuple st (CONST Pair (_constrain x t) vs)" =>
    "CONST Product_Type.Pair (_constrain x (_lensT t st)) (_state_tuple st vs)"

  "_state_decl vs P" =>
    "CONST state_block (_abs (_state_tuple (_state_type vs) vs) P) (_state_lenses vs)"
  "_state_decl vs P" <= "CONST state_block (_abs vs P) k"

parse_translation \<open>
  let
    open HOLogic;
    val lens_comp = Const (@{const_syntax "lens_comp"}, dummyT);
    val fst_lens = Const (@{const_syntax "fst_lens"}, dummyT);
    val snd_lens = Const (@{const_syntax "snd_lens"}, dummyT);
    val id_lens = Const (@{const_syntax "id_lens"}, dummyT);
    (* Construct a tuple of lenses for each of the possible locally declared variables *)
    fun 
      state_lenses n st = 
        if (n = 1) 
          then st
          else pair_const dummyT dummyT $ (lens_comp $ fst_lens $ st) $ (state_lenses (n - 1) (lens_comp $ snd_lens $ st));
    fun
      (* Add up the number of variable declarations in the tuple *)
      var_decl_num (Const (@{const_syntax "Product_Type.Pair"},_) $ _ $ vs) = var_decl_num vs + 1 |
      var_decl_num _ = 1;

    
    fun state_lens ctxt [vs] = state_lenses (var_decl_num vs) id_lens ;
  in
  [("_state_lenses", state_lens)]
  end
\<close>

subsection \<open> Examples \<close>

term  "LOCAL (x::int, y::real, z::int) \<bullet> x := (&x + &z)"

lemma "LOCAL p \<bullet> II = II"
  by (rel_auto)


end