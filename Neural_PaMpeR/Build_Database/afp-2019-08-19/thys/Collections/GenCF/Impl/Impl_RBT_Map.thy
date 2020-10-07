section \<open>\isaheader{Red-Black Tree based Maps}\<close>
theory Impl_RBT_Map
imports 
  "HOL-Library.RBT_Impl"
  "../../Lib/RBT_add"
  Automatic_Refinement.Automatic_Refinement
  "../../Iterator/Iterator"
  "../Intf/Intf_Comp"
  "../Intf/Intf_Map"
begin

(* TODO: Move to common/RBT_add (replace) *)

subsection \<open>Standard Setup\<close>

  inductive_set color_rel where
    "(color.R,color.R) \<in> color_rel"
   | "(color.B,color.B) \<in> color_rel"

  inductive_cases color_rel_elims:
    "(x,color.R) \<in> color_rel"
    "(x,color.B) \<in> color_rel"
    "(color.R,y) \<in> color_rel"
    "(color.B,y) \<in> color_rel"

  thm color_rel_elims

  lemma param_color[param]:
    "(color.R,color.R)\<in>color_rel"
    "(color.B,color.B)\<in>color_rel"
    "(case_color,case_color)\<in>R \<rightarrow> R \<rightarrow> color_rel \<rightarrow> R"
    by (auto 
      intro: color_rel.intros
      elim: color_rel.cases
      split: color.split)

  inductive_set rbt_rel_aux for Ra Rb where
    "(rbt.Empty,rbt.Empty)\<in>rbt_rel_aux Ra Rb"
  | "\<lbrakk> (c,c')\<in>color_rel; 
       (l,l')\<in>rbt_rel_aux Ra Rb; (a,a')\<in>Ra; (b,b')\<in>Rb; 
       (r,r')\<in>rbt_rel_aux Ra Rb \<rbrakk>
    \<Longrightarrow> (rbt.Branch c l a b r, rbt.Branch c' l' a' b' r')\<in>rbt_rel_aux Ra Rb"

  inductive_cases rbt_rel_aux_elims:  (* Argh! This seems to use 
    the default simpset to simplify the result. If relators are in this 
    simpset, we get an undesired result! *)
    "(x,rbt.Empty)\<in>rbt_rel_aux Ra Rb"
    "(rbt.Empty,x')\<in>rbt_rel_aux Ra Rb"
    "(rbt.Branch c l a b r,x')\<in>rbt_rel_aux Ra Rb"
    "(x,rbt.Branch c' l' a' b' r')\<in>rbt_rel_aux Ra Rb"

  definition "rbt_rel \<equiv> rbt_rel_aux"
  lemma rbt_rel_aux_fold: "rbt_rel_aux Ra Rb \<equiv> \<langle>Ra,Rb\<rangle>rbt_rel"
    by (simp add: rbt_rel_def relAPP_def)

  lemmas rbt_rel_intros = rbt_rel_aux.intros[unfolded rbt_rel_aux_fold]
  lemmas rbt_rel_cases = rbt_rel_aux.cases[unfolded rbt_rel_aux_fold]
  lemmas rbt_rel_induct[induct set] 
    = rbt_rel_aux.induct[unfolded rbt_rel_aux_fold]
  lemmas rbt_rel_elims = rbt_rel_aux_elims[unfolded rbt_rel_aux_fold]

  lemma param_rbt1[param]: 
    "(rbt.Empty,rbt.Empty) \<in> \<langle>Ra,Rb\<rangle>rbt_rel"
    "(rbt.Branch,rbt.Branch) \<in> 
      color_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> Ra \<rightarrow> Rb \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel"
    by (auto intro: rbt_rel_intros)

  lemma param_case_rbt[param]:
    "(case_rbt,case_rbt) \<in> 
      Ra \<rightarrow> (color_rel \<rightarrow> \<langle>Rb,Rc\<rangle>rbt_rel \<rightarrow> Rb \<rightarrow> Rc \<rightarrow> \<langle>Rb,Rc\<rangle>rbt_rel \<rightarrow> Ra) 
        \<rightarrow> \<langle>Rb,Rc\<rangle>rbt_rel \<rightarrow> Ra"
    apply clarsimp
    apply (erule rbt_rel_cases)
    apply simp
    apply simp
    apply parametricity
    done

  lemma param_rec_rbt[param]: "(rec_rbt, rec_rbt) \<in> 
    Ra \<rightarrow> (color_rel \<rightarrow> \<langle>Rb,Rc\<rangle>rbt_rel \<rightarrow> Rb \<rightarrow> Rc \<rightarrow> \<langle>Rb,Rc\<rangle>rbt_rel
     \<rightarrow> Ra \<rightarrow> Ra \<rightarrow> Ra) \<rightarrow> \<langle>Rb,Rc\<rangle>rbt_rel \<rightarrow> Ra"
  proof (intro fun_relI, goal_cases)
    case (1 s s' f f' t t') from this(3,1,2) show ?case
      apply (induct arbitrary: s s')
      apply simp
      apply simp
      apply parametricity
      done
  qed

  lemma param_paint[param]: 
    "(paint,paint)\<in>color_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel"
    unfolding paint_def
    by parametricity

  lemma param_balance[param]: 
    shows "(balance,balance) \<in> 
      \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> Ra \<rightarrow> Rb \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel"
  proof (intro fun_relI, goal_cases)
    case (1 t1 t1' a a' b b' t2 t2')
    thus ?case
      apply (induct t1' a' b' t2' arbitrary: t1 a b t2 rule: balance.induct)
      apply (elim_all rbt_rel_elims color_rel_elims)
      apply (simp_all only: balance.simps)
      apply (parametricity)+
      done
  qed


  lemma param_rbt_ins[param]:
    fixes less
    assumes param_less[param]: "(less,less') \<in> Ra \<rightarrow> Ra \<rightarrow> Id"
    shows "(ord.rbt_ins less,ord.rbt_ins less') \<in> 
             (Ra\<rightarrow>Rb\<rightarrow>Rb\<rightarrow>Rb) \<rightarrow> Ra \<rightarrow> Rb \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel"
  proof (intro fun_relI, goal_cases)
    case (1 f f' a a' b b' t t')
    thus ?case
      apply (induct f' a' b' t' arbitrary: f a b t rule: ord.rbt_ins.induct)
      apply (elim_all rbt_rel_elims color_rel_elims)
      apply (simp_all only: ord.rbt_ins.simps rbt_ins.simps)
      apply parametricity+
      done
  qed

  term rbt_insert
  lemma param_rbt_insert[param]:
    fixes less
    assumes param_less[param]: "(less,less') \<in> Ra \<rightarrow> Ra \<rightarrow> Id"
    shows "(ord.rbt_insert less,ord.rbt_insert less') \<in> 
      Ra \<rightarrow> Rb \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel"
    unfolding rbt_insert_def ord.rbt_insert_def
    unfolding rbt_insert_with_key_def[abs_def] 
      ord.rbt_insert_with_key_def[abs_def] 
    by parametricity

  lemma param_rbt_lookup[param]:
    fixes less
    assumes param_less[param]: "(less,less') \<in> Ra \<rightarrow> Ra \<rightarrow> Id"
    shows "(ord.rbt_lookup less,ord.rbt_lookup less') \<in> 
             \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> Ra \<rightarrow> \<langle>Rb\<rangle>option_rel"
    unfolding rbt_lookup_def ord.rbt_lookup_def
    by parametricity

  term balance_left
  lemma param_balance_left[param]: 
    "(balance_left, balance_left) \<in> 
      \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> Ra \<rightarrow> Rb \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel"
  proof (intro fun_relI, goal_cases)
    case (1 l l' a a' b b' r r')
    thus ?case
      apply (induct l a b r arbitrary: l' a' b' r' rule: balance_left.induct)
      apply (elim_all rbt_rel_elims color_rel_elims)
      apply (simp_all only: balance_left.simps)
      apply parametricity+
      done
  qed

  term balance_right
  lemma param_balance_right[param]: 
    "(balance_right, balance_right) \<in> 
      \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> Ra \<rightarrow> Rb \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel"
  proof (intro fun_relI, goal_cases)
    case (1 l l' a a' b b' r r')
    thus ?case
      apply (induct l a b r arbitrary: l' a' b' r' rule: balance_right.induct)
      apply (elim_all rbt_rel_elims color_rel_elims)
      apply (simp_all only: balance_right.simps)
      apply parametricity+
      done
  qed

  lemma param_combine[param]:
    "(combine,combine)\<in>\<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel"
  proof (intro fun_relI, goal_cases)
    case (1 t1 t1' t2 t2')
    thus ?case
      apply (induct t1 t2 arbitrary: t1' t2' rule: combine.induct)
      apply (elim_all rbt_rel_elims color_rel_elims)
      apply (simp_all only: combine.simps)
      apply parametricity+
      done
  qed

  lemma ih_aux1: "\<lbrakk> (a',b)\<in>R; a'=a \<rbrakk> \<Longrightarrow> (a,b)\<in>R" by auto
  lemma is_eq: "a=b \<Longrightarrow> a=b" .

  lemma param_rbt_del_aux:
    fixes br
    fixes less
    assumes param_less[param]: "(less,less') \<in> Ra \<rightarrow> Ra \<rightarrow> Id"
    shows
    "\<lbrakk> (ak1,ak1')\<in>Ra; (al,al')\<in>\<langle>Ra,Rb\<rangle>rbt_rel; (ak,ak')\<in>Ra;
      (av,av')\<in>Rb; (ar,ar')\<in>\<langle>Ra,Rb\<rangle>rbt_rel 
    \<rbrakk> \<Longrightarrow> (ord.rbt_del_from_left less ak1 al ak av ar, 
      ord.rbt_del_from_left less' ak1' al' ak' av' ar') 
    \<in> \<langle>Ra,Rb\<rangle>rbt_rel"
    "\<lbrakk> (bk1,bk1')\<in>Ra; (bl,bl')\<in>\<langle>Ra,Rb\<rangle>rbt_rel; (bk,bk')\<in>Ra;
      (bv,bv')\<in>Rb; (br,br')\<in>\<langle>Ra,Rb\<rangle>rbt_rel 
    \<rbrakk> \<Longrightarrow> (ord.rbt_del_from_right less bk1 bl bk bv br, 
      ord.rbt_del_from_right less' bk1' bl' bk' bv' br') 
    \<in> \<langle>Ra,Rb\<rangle>rbt_rel"
    "\<lbrakk> (ck,ck')\<in>Ra; (ct,ct')\<in>\<langle>Ra,Rb\<rangle>rbt_rel \<rbrakk> 
      \<Longrightarrow> (ord.rbt_del less ck ct, ord.rbt_del less' ck' ct') \<in> \<langle>Ra,Rb\<rangle>rbt_rel"
    apply (induct 
      ak1' al' ak' av' ar' and bk1' bl' bk' bv' br' and ck' ct'
      arbitrary: ak1 al ak av ar and bk1 bl bk bv br and ck ct
      rule: ord.rbt_del_from_left_rbt_del_from_right_rbt_del.induct)
    (* TODO/FIXME: We do not have 'deep' elimination rules, thus
      we have to do some ughly hack to apply the rbt_rel-elimination inside
      the induction hypothesis. *)
    apply (assumption
      | elim rbt_rel_elims color_rel_elims 
      | simp (no_asm_use) only: rbt_del.simps ord.rbt_del.simps
          rbt_del_from_left.simps ord.rbt_del_from_left.simps
          rbt_del_from_right.simps ord.rbt_del_from_right.simps
      | parametricity
      | rule rbt_rel_intros
      | hypsubst
      | (simp, rule ih_aux1, rprems)
      | (rule is_eq, simp)
    ) +
    done

  lemma param_rbt_del[param]:
    fixes less
    assumes param_less: "(less,less') \<in> Ra \<rightarrow> Ra \<rightarrow> Id"
    shows
    "(ord.rbt_del_from_left less, ord.rbt_del_from_left less') \<in> 
      Ra \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> Ra \<rightarrow> Rb \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel"
    "(ord.rbt_del_from_right less, ord.rbt_del_from_right less') \<in>
      Ra \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> Ra \<rightarrow> Rb \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel"
    "(ord.rbt_del less,ord.rbt_del less') \<in> 
      Ra \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel"
    by (intro fun_relI, blast intro: param_rbt_del_aux[OF param_less])+

  lemma param_rbt_delete[param]:
    fixes less
    assumes param_less[param]: "(less,less') \<in> Ra \<rightarrow> Ra \<rightarrow> Id"
    shows "(ord.rbt_delete less, ord.rbt_delete less') 
      \<in> Ra \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel"
    unfolding rbt_delete_def[abs_def] ord.rbt_delete_def[abs_def]
    by parametricity

  term ord.rbt_insert_with_key

  abbreviation compare_rel :: "(RBT_Impl.compare \<times> _) set" 
    where "compare_rel \<equiv> Id"

  lemma param_compare[param]:
    "(RBT_Impl.LT,RBT_Impl.LT)\<in>compare_rel"
    "(RBT_Impl.GT,RBT_Impl.GT)\<in>compare_rel"
    "(RBT_Impl.EQ,RBT_Impl.EQ)\<in>compare_rel"
    "(RBT_Impl.case_compare,RBT_Impl.case_compare)\<in>R\<rightarrow>R\<rightarrow>R\<rightarrow>compare_rel\<rightarrow>R"
    by (auto split: RBT_Impl.compare.split)

  lemma param_rbtreeify_aux[param]:
    "\<lbrakk>n\<le>length kvs; (n,n')\<in>nat_rel; (kvs,kvs')\<in>\<langle>\<langle>Ra,Rb\<rangle>prod_rel\<rangle>list_rel\<rbrakk> 
    \<Longrightarrow> (rbtreeify_f n kvs,rbtreeify_f n' kvs')
      \<in> \<langle>\<langle>Ra,Rb\<rangle>rbt_rel, \<langle>\<langle>Ra,Rb\<rangle>prod_rel\<rangle>list_rel\<rangle>prod_rel"
    "\<lbrakk>n\<le>Suc (length kvs); (n,n')\<in>nat_rel; (kvs,kvs')\<in>\<langle>\<langle>Ra,Rb\<rangle>prod_rel\<rangle>list_rel\<rbrakk>
    \<Longrightarrow> (rbtreeify_g n kvs,rbtreeify_g n' kvs')
      \<in> \<langle>\<langle>Ra,Rb\<rangle>rbt_rel, \<langle>\<langle>Ra,Rb\<rangle>prod_rel\<rangle>list_rel\<rangle>prod_rel"
    apply (induct n kvs and n kvs 
      arbitrary: n' kvs' and n' kvs'
      rule: rbtreeify_induct)

    (* TODO: Still requires some manual proof! *)
    apply (simp only: pair_in_Id_conv)
    apply (simp (no_asm_use) only: rbtreeify_f_simps rbtreeify_g_simps)
    apply parametricity

    apply (elim list_relE prod_relE)
    apply (simp only: pair_in_Id_conv)
    apply hypsubst
    apply (simp (no_asm_use) only: rbtreeify_f_simps rbtreeify_g_simps)
    apply parametricity

    apply clarsimp
    apply (subgoal_tac "(rbtreeify_f n kvs, rbtreeify_f n kvs'a) 
      \<in> \<langle>\<langle>Ra, Rb\<rangle>rbt_rel, \<langle>\<langle>Ra, Rb\<rangle>prod_rel\<rangle>list_rel\<rangle>prod_rel")
    apply (clarsimp elim!: list_relE prod_relE)
    apply parametricity
    apply (rule refl)
    apply rprems
    apply (rule refl)
    apply assumption

    apply clarsimp
    apply (subgoal_tac "(rbtreeify_f n kvs, rbtreeify_f n kvs'a) 
      \<in> \<langle>\<langle>Ra, Rb\<rangle>rbt_rel, \<langle>\<langle>Ra, Rb\<rangle>prod_rel\<rangle>list_rel\<rangle>prod_rel")
    apply (clarsimp elim!: list_relE prod_relE)
    apply parametricity
    apply (rule refl)
    apply rprems
    apply (rule refl)
    apply assumption

    apply simp
    apply parametricity

    apply clarsimp
    apply parametricity

    apply clarsimp
    apply (subgoal_tac "(rbtreeify_g n kvs, rbtreeify_g n kvs'a) 
      \<in> \<langle>\<langle>Ra, Rb\<rangle>rbt_rel, \<langle>\<langle>Ra, Rb\<rangle>prod_rel\<rangle>list_rel\<rangle>prod_rel")
    apply (clarsimp elim!: list_relE prod_relE)
    apply parametricity
    apply (rule refl)
    apply parametricity
    apply (rule refl)

    apply clarsimp
    apply (subgoal_tac "(rbtreeify_f n kvs, rbtreeify_f n kvs'a) 
      \<in> \<langle>\<langle>Ra, Rb\<rangle>rbt_rel, \<langle>\<langle>Ra, Rb\<rangle>prod_rel\<rangle>list_rel\<rangle>prod_rel")
    apply (clarsimp elim!: list_relE prod_relE)
    apply parametricity
    apply (rule refl)
    apply parametricity
    apply (rule refl)
    done    

  lemma param_rbtreeify[param]:
    "(rbtreeify, rbtreeify) \<in> \<langle>\<langle>Ra,Rb\<rangle>prod_rel\<rangle>list_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel"
    unfolding rbtreeify_def[abs_def]
    apply parametricity
    by simp

  lemma param_sunion_with[param]:
    fixes less
    shows "\<lbrakk> (less,less') \<in> Ra \<rightarrow> Ra \<rightarrow> Id; 
      (f,f')\<in>(Ra\<rightarrow>Rb\<rightarrow>Rb\<rightarrow>Rb); (a,a')\<in>\<langle>\<langle>Ra,Rb\<rangle>prod_rel\<rangle>list_rel;
      (b,b')\<in>\<langle>\<langle>Ra,Rb\<rangle>prod_rel\<rangle>list_rel \<rbrakk> 
    \<Longrightarrow> (ord.sunion_with less f a b, ord.sunion_with less' f' a' b') \<in> 
      \<langle>\<langle>Ra,Rb\<rangle>prod_rel\<rangle>list_rel"
    apply (induct f' a' b' arbitrary: f a b 
      rule: ord.sunion_with.induct[of less'])
    apply (elim_all list_relE prod_relE)
    apply (simp_all only: ord.sunion_with.simps)
    apply parametricity
    apply simp_all
    done

  lemma skip_red_alt:
    "RBT_Impl.skip_red t = (case t of 
      (Branch color.R l k v r) \<Rightarrow> l
    | _ \<Rightarrow> t)"
    by (auto split: rbt.split color.split)

  function compare_height :: 
    "('a, 'b) RBT_Impl.rbt \<Rightarrow> ('a, 'b) RBT_Impl.rbt \<Rightarrow> ('a, 'b) RBT_Impl.rbt \<Rightarrow> ('a, 'b) RBT_Impl.rbt \<Rightarrow> RBT_Impl.compare"
    where
    "compare_height sx s t tx =
  (case (RBT_Impl.skip_red sx, RBT_Impl.skip_red s, RBT_Impl.skip_red t, RBT_Impl.skip_red tx) of
     (Branch _ sx' _ _ _, Branch _ s' _ _ _, Branch _ t' _ _ _, Branch _ tx' _ _ _) \<Rightarrow> 
       compare_height (RBT_Impl.skip_black sx') s' t' (RBT_Impl.skip_black tx')
   | (_, rbt.Empty, _, Branch _ _ _ _ _) \<Rightarrow> RBT_Impl.LT
   | (Branch _ _ _ _ _, _, rbt.Empty, _) \<Rightarrow> RBT_Impl.GT
   | (Branch _ sx' _ _ _, Branch _ s' _ _ _, Branch _ t' _ _ _, rbt.Empty) \<Rightarrow>
       compare_height (RBT_Impl.skip_black sx') s' t' rbt.Empty
   | (rbt.Empty, Branch _ s' _ _ _, Branch _ t' _ _ _, Branch _ tx' _ _ _) \<Rightarrow>
       compare_height rbt.Empty s' t' (RBT_Impl.skip_black tx')
   | _ \<Rightarrow> RBT_Impl.EQ)"
    by pat_completeness auto

  lemma skip_red_size: "size (RBT_Impl.skip_red b) \<le> size b"
    by (auto simp add: skip_red_alt split: rbt.split color.split)

  lemma skip_black_size: "size (RBT_Impl.skip_black b) \<le> size b"
    unfolding RBT_Impl.skip_black_def
    apply (auto 
      simp add: Let_def 
      split: rbt.split color.split
    )
    using skip_red_size[of b]
    apply auto
    done
    
  termination 
  proof -
    {
      fix s t x
      assume A: "s = RBT_Impl.skip_red t"
        and B: "x < size s"
      note B
      also note A
      also note skip_red_size
      finally have "x < size t" .
    } note AUX=this

    show "All compare_height_dom"
      apply (relation 
        "measure (\<lambda>(a, b, c, d). size a + size b + size c + size d)")
      apply rule

      (* FIXME: This is solved by
        apply (smt rbt.size(4) skip_black_size skip_red_size)+
        which is, however, not allowed for afp.
        *)

      apply (clarsimp simp: Let_def split: rbt.splits color.splits)
      apply (intro add_less_mono trans_less_add2 
        order_le_less_trans[OF skip_black_size], (erule AUX, simp)+) []

      apply (clarsimp simp: Let_def split: rbt.splits color.splits)
      apply (rule trans_less_add1)
      apply (intro add_less_mono trans_less_add2 
        order_le_less_trans[OF skip_black_size], (erule AUX, simp)+) []

      apply (clarsimp simp: Let_def split: rbt.splits color.splits)
      apply (intro add_less_mono trans_less_add2 
        order_le_less_trans[OF skip_black_size], (erule AUX, simp)+) []
      done
  qed

  lemmas [simp del] = compare_height.simps

  lemma compare_height_alt: 
    "RBT_Impl.compare_height sx s t tx = compare_height sx s t tx"
    apply (induct sx s t tx rule: compare_height.induct)
    apply (subst RBT_Impl.compare_height.simps)
    apply (subst compare_height.simps)
    apply (auto split: rbt.split)
    done

  term RBT_Impl.skip_red
  lemma param_skip_red[param]: "(RBT_Impl.skip_red,RBT_Impl.skip_red) 
    \<in> \<langle>Rk,Rv\<rangle>rbt_rel \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_rel"
    unfolding skip_red_alt[abs_def] by parametricity

  lemma param_skip_black[param]: "(RBT_Impl.skip_black,RBT_Impl.skip_black) 
    \<in> \<langle>Rk,Rv\<rangle>rbt_rel \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_rel"
    unfolding RBT_Impl.skip_black_def[abs_def] by parametricity

  term case_rbt
  lemma param_case_rbt':
    assumes "(t,t')\<in>\<langle>Rk,Rv\<rangle>rbt_rel"
    assumes "\<lbrakk>t=rbt.Empty; t'=rbt.Empty\<rbrakk> \<Longrightarrow> (fl,fl')\<in>R"
    assumes "\<And>c l k v r c' l' k' v' r'. \<lbrakk> 
      t = Branch c l k v r; t' = Branch c' l' k' v' r'; 
      (c,c')\<in>color_rel;
      (l,l')\<in>\<langle>Rk,Rv\<rangle>rbt_rel; (k,k')\<in>Rk; (v,v')\<in>Rv; (r,r')\<in>\<langle>Rk,Rv\<rangle>rbt_rel
    \<rbrakk> \<Longrightarrow> (fb c l k v r, fb' c' l' k' v' r') \<in> R"
    shows "(case_rbt fl fb t, case_rbt fl' fb' t') \<in> R"
    using assms by (auto split: rbt.split elim: rbt_rel_elims)
      
  lemma compare_height_param_aux[param]:
    "\<lbrakk> (sx,sx')\<in>\<langle>Rk,Rv\<rangle>rbt_rel; (s,s')\<in>\<langle>Rk,Rv\<rangle>rbt_rel;
       (t,t')\<in>\<langle>Rk,Rv\<rangle>rbt_rel; (tx,tx')\<in>\<langle>Rk,Rv\<rangle>rbt_rel \<rbrakk>
    \<Longrightarrow> (compare_height sx s t tx, compare_height sx' s' t' tx') \<in> compare_rel"
    apply (induct sx' s' t' tx' arbitrary: sx s t tx 
      rule: compare_height.induct)
    apply (subst (2) compare_height.simps)
    apply (subst compare_height.simps)
    apply (parametricity add: param_case_prod' param_case_rbt', (simp only: prod.inject)+) []
    done

  lemma compare_height_param[param]:
    "(RBT_Impl.compare_height,RBT_Impl.compare_height) \<in> 
      \<langle>Rk,Rv\<rangle>rbt_rel \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_rel \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_rel \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_rel 
      \<rightarrow> compare_rel"
    unfolding compare_height_alt[abs_def]
    by parametricity

  lemma param_rbt_union[param]:
    fixes less
    assumes param_less[param]: "(less,less') \<in> Ra \<rightarrow> Ra \<rightarrow> Id"
    shows "(ord.rbt_union less, ord.rbt_union less') 
      \<in> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> \<langle>Ra,Rb\<rangle>rbt_rel"
    unfolding ord.rbt_union_def[abs_def] ord.rbt_union_with_key_def[abs_def]
      ord.rbt_insert_with_key_def[abs_def]
    unfolding RBT_Impl.fold_def RBT_Impl.entries_def
    by parametricity

term rm_iterateoi
lemma param_rm_iterateoi[param]: "(rm_iterateoi,rm_iterateoi) 
  \<in> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> (Rc\<rightarrow>Id) \<rightarrow> (\<langle>Ra,Rb\<rangle>prod_rel \<rightarrow> Rc \<rightarrow> Rc) \<rightarrow> Rc \<rightarrow> Rc"
  unfolding rm_iterateoi_def
  by (parametricity)

lemma param_rm_reverse_iterateoi[param]: 
  "(rm_reverse_iterateoi,rm_reverse_iterateoi) 
    \<in> \<langle>Ra,Rb\<rangle>rbt_rel \<rightarrow> (Rc\<rightarrow>Id) \<rightarrow> (\<langle>Ra,Rb\<rangle>prod_rel \<rightarrow> Rc \<rightarrow> Rc) \<rightarrow> Rc \<rightarrow> Rc"
  unfolding rm_reverse_iterateoi_def
  by (parametricity)


lemma param_color_eq[param]: 
  "((=), (=))\<in>color_rel\<rightarrow>color_rel\<rightarrow>Id"
  by (auto elim: color_rel.cases)

lemma param_color_of[param]: 
  "(color_of, color_of)\<in>\<langle>Rk,Rv\<rangle>rbt_rel\<rightarrow>color_rel"
  unfolding color_of_def
  by parametricity

term bheight
lemma param_bheight[param]:
  "(bheight,bheight)\<in>\<langle>Rk,Rv\<rangle>rbt_rel\<rightarrow>Id"
  unfolding bheight_def
  by (parametricity)

lemma inv1_param[param]: "(inv1,inv1)\<in>\<langle>Rk,Rv\<rangle>rbt_rel\<rightarrow>Id"
  unfolding inv1_def
  by (parametricity)

lemma inv2_param[param]: "(inv2,inv2)\<in>\<langle>Rk,Rv\<rangle>rbt_rel\<rightarrow>Id"
  unfolding inv2_def
  by (parametricity)

term ord.rbt_less
lemma rbt_less_param[param]: "(ord.rbt_less,ord.rbt_less) \<in> 
  (Rk\<rightarrow>Rk\<rightarrow>Id) \<rightarrow> Rk \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_rel \<rightarrow> Id"
  unfolding ord.rbt_less_prop[abs_def]
  apply (parametricity add: param_list_ball)
  unfolding RBT_Impl.keys_def RBT_Impl.entries_def
  apply (parametricity)
  done

term ord.rbt_greater
lemma rbt_greater_param[param]: "(ord.rbt_greater,ord.rbt_greater) \<in> 
  (Rk\<rightarrow>Rk\<rightarrow>Id) \<rightarrow> Rk \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_rel \<rightarrow> Id"
  unfolding ord.rbt_greater_prop[abs_def]
  apply (parametricity add: param_list_ball)
  unfolding RBT_Impl.keys_def RBT_Impl.entries_def
  apply (parametricity)
  done

lemma rbt_sorted_param[param]:
  "(ord.rbt_sorted,ord.rbt_sorted)\<in>(Rk\<rightarrow>Rk\<rightarrow>Id)\<rightarrow>\<langle>Rk,Rv\<rangle>rbt_rel\<rightarrow>Id"
  unfolding ord.rbt_sorted_def[abs_def]
  by (parametricity)

lemma is_rbt_param[param]: "(ord.is_rbt,ord.is_rbt) \<in> 
  (Rk\<rightarrow>Rk\<rightarrow>Id) \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_rel \<rightarrow> Id"
  unfolding ord.is_rbt_def[abs_def]
  by (parametricity)

definition "rbt_map_rel' lt = br (ord.rbt_lookup lt) (ord.is_rbt lt)"

lemma (in linorder) rbt_map_impl:
  "(rbt.Empty,Map.empty) \<in> rbt_map_rel' (<)"
  "(rbt_insert,\<lambda>k v m. m(k\<mapsto>v)) 
    \<in> Id \<rightarrow> Id \<rightarrow> rbt_map_rel' (<) \<rightarrow> rbt_map_rel' (<)"
  "(rbt_lookup,\<lambda>m k. m k) \<in> rbt_map_rel' (<) \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>option_rel"
  "(rbt_delete,\<lambda>k m. m|`(-{k})) \<in> Id \<rightarrow> rbt_map_rel' (<) \<rightarrow> rbt_map_rel' (<)"
  "(rbt_union,(++)) 
    \<in> rbt_map_rel' (<) \<rightarrow> rbt_map_rel' (<) \<rightarrow> rbt_map_rel' (<)"
  by (auto simp add: 
    rbt_lookup_rbt_insert rbt_lookup_rbt_delete rbt_lookup_rbt_union
    rbt_union_is_rbt
    rbt_map_rel'_def br_def)

lemma sorted_wrt_keys_true[simp]: "sorted_wrt (\<lambda>(_,_) (_,_). True) l"
  apply (induct l)
  apply auto
  done

(*
lemma (in linorder) rbt_it_linord_impl: 
  "is_map_iterator_linord (rbt_map_rel' (<)) Id Id Id 
    (rm_iterateoi::_ \<Rightarrow> ('a,'v,'s) map_iterator)"
  unfolding is_map_iterator_genord_def is_map_iterator_linord_def 
    gen_map_iterator_genord_def[abs_def]
  apply (intro fun_relI)
  apply (clarsimp intro!: chooseR.intros[OF _ IdI])
proof -
  case (goal1 t s' c f s)
  hence "is_rbt t" and [simp]: "s'=(rbt_lookup t)" 
    unfolding rbt_map_rel'_def br_def by simp_all
  hence RSORTED: "rbt_sorted t" by (simp add: is_rbt_def)
 
  thm rm_iterateoi_correct
  from rm_iterateoi_correct[OF RSORTED,
    unfolded set_iterator_map_linord_def
      set_iterator_genord_def
  ] obtain l where 
      "distinct l" 
      and "map_to_set (rbt_lookup t) = set l"
      and "sorted_wrt (\<lambda>(k,_) (k',_). k \<le> k') l"
      and "(rm_iterateoi t::('a,'v,'s) map_iterator) = foldli l"
    by blast
  thus ?case 
    apply (rule_tac exI[where x=l])
    apply (simp add: sorted_wrt_keys_map_fst)
    by (metis iterate_to_list_foldli map_iterator_foldli_conv rev_rev_ident 
      set_iterator_foldli_correct)
qed

lemma (in linorder) rbt_it_rev_linord_impl: 
  "is_map_iterator_rev_linord (rbt_map_rel' (<)) Id Id Id 
    (rm_reverse_iterateoi::_ \<Rightarrow> ('a,'v,'s) map_iterator)"
  unfolding is_map_iterator_genord_def is_map_iterator_rev_linord_def 
    gen_map_iterator_genord_def[abs_def]
  apply (intro fun_relI)
  apply (clarsimp intro!: chooseR.intros[OF _ IdI])
proof -
  case (goal1 t s' c f s)
  hence "is_rbt t" and [simp]: "s'=(rbt_lookup t)" 
    unfolding rbt_map_rel'_def br_def by simp_all
  hence RSORTED: "rbt_sorted t" by (simp add: is_rbt_def)
  
  from rm_reverse_iterateoi_correct[unfolded 
    set_iterator_map_rev_linord_def
    set_iterator_genord_def,
    OF RSORTED
  ] obtain l where 
      "distinct l" 
      and "map_to_set (rbt_lookup t) = set l"
      and "sorted_wrt (\<lambda>(k,_) (k',_). k \<ge> k') l"
      and "(rm_reverse_iterateoi t::('a,'v,'s) map_iterator) = foldli l"
    by blast
  thus ?case 
    apply (rule_tac exI[where x=l])
    apply (simp add: sorted_wrt_keys_map_fst)
    by (metis iterate_to_list_foldli map_iterator_foldli_conv rev_rev_ident 
      set_iterator_foldli_correct)
qed

lemma (in linorder) rbt_it_impl: 
  "is_map_iterator (rbt_map_rel' (<)) Id Id Id rm_iterateoi"
  unfolding is_map_iterator_def 
  apply (rule is_map_iterator_genord_weaken)
  apply (rule rbt_it_linord_impl[unfolded is_map_iterator_linord_def])
  ..

*)

definition rbt_map_rel_def_internal:
  "rbt_map_rel lt Rk Rv \<equiv> \<langle>Rk,Rv\<rangle>rbt_rel O rbt_map_rel' lt"

lemma rbt_map_rel_def: 
  "\<langle>Rk,Rv\<rangle>rbt_map_rel lt \<equiv> \<langle>Rk,Rv\<rangle>rbt_rel O rbt_map_rel' lt"
  by (simp add: rbt_map_rel_def_internal relAPP_def)

(*
lemma (in linorder) autoref_gen_rbt_iterate_linord:
  "is_map_iterator_linord 
    (\<langle>Rk,Rv\<rangle>rbt_map_rel (<)) (Rk::(_\<times>'a) set) Rv R\<sigma> rm_iterateoi"
proof -
  note param_rm_iterateoi[of Rk Rv R\<sigma>]
  also note rbt_it_linord_impl[
    unfolded is_map_iterator_linord_def is_map_iterator_genord_def]
  finally (relcompI) show ?thesis
    unfolding is_map_iterator_linord_def is_map_iterator_genord_def
    apply -
    apply (erule rev_subsetD)
    apply (simp add: rbt_map_rel_def rbt_map_rel'_def)
    apply (
      rule Orderings.order_trans[OF fun_rel_comp_dist] fun_rel_mono subset_refl
      | simp
    )+
    done
qed

lemma (in linorder) autoref_gen_rbt_iterate_rev_linord:
  "is_map_iterator_rev_linord 
    (\<langle>Rk,Rv\<rangle>rbt_map_rel (<)) (Rk::(_\<times>'a) set) Rv R\<sigma> rm_reverse_iterateoi"
proof -
  note param_rm_reverse_iterateoi[of Rk Rv R\<sigma>]
  also note rbt_it_rev_linord_impl[
    unfolded is_map_iterator_rev_linord_def is_map_iterator_genord_def]
  finally (relcompI) show ?thesis
    unfolding is_map_iterator_rev_linord_def is_map_iterator_genord_def
    apply -
    apply (erule rev_subsetD)
    apply (simp add: rbt_map_rel_def rbt_map_rel'_def)
    apply (
      rule Orderings.order_trans[OF fun_rel_comp_dist] fun_rel_mono subset_refl
      | simp
    )+
    done
qed

lemma (in linorder) autoref_gen_rbt_iterate:
  "is_map_iterator 
    (\<langle>Rk,Rv\<rangle>rbt_map_rel (<)) (Rk::(_\<times>'a) set) Rv R\<sigma> rm_iterateoi"
proof -
  note param_rm_iterateoi[of Rk Rv R\<sigma>]
  also note rbt_it_impl[
    unfolded is_map_iterator_def is_map_iterator_genord_def]
  finally (relcompI) show ?thesis
    unfolding is_map_iterator_def is_map_iterator_genord_def
    apply -
    apply (erule rev_subsetD)
    apply (simp add: rbt_map_rel_def rbt_map_rel'_def)
    apply (
      rule Orderings.order_trans[OF fun_rel_comp_dist] fun_rel_mono subset_refl
      | simp
    )+
    done
qed
*)

lemma (in linorder) autoref_gen_rbt_empty: 
  "(rbt.Empty,Map.empty) \<in> \<langle>Rk,Rv\<rangle>rbt_map_rel (<)"
  by (auto simp: rbt_map_rel_def 
    intro!: rbt_map_impl rbt_rel_intros)

lemma (in linorder) autoref_gen_rbt_insert:
  fixes less_impl
  assumes param_less: "(less_impl,(<)) \<in> Rk \<rightarrow> Rk \<rightarrow> Id"
  shows "(ord.rbt_insert less_impl,\<lambda>k v m. m(k\<mapsto>v)) \<in> 
    Rk \<rightarrow> Rv \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_map_rel (<) \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_map_rel (<)"
  apply (intro fun_relI)
  unfolding rbt_map_rel_def
  apply (auto intro!: relcomp.intros)
  apply (rule param_rbt_insert[OF param_less, param_fo])
  apply assumption+
  apply (rule rbt_map_impl[param_fo])
  apply (rule IdI | assumption)+
  done

lemma (in linorder) autoref_gen_rbt_lookup:
  fixes less_impl
  assumes param_less: "(less_impl,(<)) \<in> Rk \<rightarrow> Rk \<rightarrow> Id"
  shows "(ord.rbt_lookup less_impl, \<lambda>m k. m k) \<in> 
    \<langle>Rk,Rv\<rangle>rbt_map_rel (<) \<rightarrow> Rk \<rightarrow> \<langle>Rv\<rangle>option_rel"
  unfolding rbt_map_rel_def
  apply (intro fun_relI)
  apply (elim relcomp.cases)
  apply hypsubst
  apply (subst R_O_Id[symmetric])
  apply (rule relcompI)
  apply (rule param_rbt_lookup[OF param_less, param_fo])
  apply assumption+
  apply (subst option_rel_id_simp[symmetric])
  apply (rule rbt_map_impl[param_fo])
  apply assumption
  apply (rule IdI)
  done

lemma (in linorder) autoref_gen_rbt_delete:
  fixes less_impl
  assumes param_less: "(less_impl,(<)) \<in> Rk \<rightarrow> Rk \<rightarrow> Id"
  shows "(ord.rbt_delete less_impl, \<lambda>k m. m |`(-{k})) \<in> 
    Rk \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_map_rel (<) \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_map_rel (<)"
  unfolding rbt_map_rel_def
  apply (intro fun_relI)
  apply (elim relcomp.cases)
  apply hypsubst
  apply (rule relcompI)
  apply (rule param_rbt_delete[OF param_less, param_fo])
  apply assumption+
  apply (rule rbt_map_impl[param_fo])
  apply (rule IdI)
  apply assumption
  done

lemma (in linorder) autoref_gen_rbt_union:
  fixes less_impl
  assumes param_less: "(less_impl,(<)) \<in> Rk \<rightarrow> Rk \<rightarrow> Id"
  shows "(ord.rbt_union less_impl, (++)) \<in> 
    \<langle>Rk,Rv\<rangle>rbt_map_rel (<) \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_map_rel (<) \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_map_rel (<)"
  unfolding rbt_map_rel_def
  apply (intro fun_relI)
  apply (elim relcomp.cases)
  apply hypsubst
  apply (rule relcompI)
  apply (rule param_rbt_union[OF param_less, param_fo])
  apply assumption+
  apply (rule rbt_map_impl[param_fo])
  apply assumption+
  done

subsection \<open>A linear ordering on red-black trees\<close>

abbreviation "rbt_to_list t \<equiv> it_to_list rm_iterateoi t"

lemma (in linorder) rbt_to_list_correct: 
  assumes SORTED: "rbt_sorted t"
  shows "rbt_to_list t = sorted_list_of_map (rbt_lookup t)" (is "?tl = _")
proof -
  from map_it_to_list_linord_correct[where it=rm_iterateoi, OF 
    rm_iterateoi_correct[OF SORTED]
  ] have 
      M: "map_of ?tl = rbt_lookup t"
      and D: "distinct (map fst ?tl)"
      and S: "sorted (map fst ?tl)"
    by (simp_all)

  from the_sorted_list_of_map[OF D S] M show ?thesis
    by simp
qed

definition 
  "cmp_rbt cmpk cmpv \<equiv> cmp_img rbt_to_list (cmp_lex (cmp_prod cmpk cmpv))"

lemma (in linorder) param_rbt_sorted_list_of_map[param]:
  shows "(rbt_to_list, sorted_list_of_map) \<in> 
  \<langle>Rk, Rv\<rangle>rbt_map_rel (<) \<rightarrow> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel"
  apply (auto simp: rbt_map_rel_def rbt_map_rel'_def br_def
    rbt_to_list_correct[symmetric]
  )
  by (parametricity)

lemma param_rbt_sorted_list_of_map'[param]:
  assumes ELO: "eq_linorder cmp'"
  shows "(rbt_to_list,linorder.sorted_list_of_map (comp2le cmp')) \<in> 
    \<langle>Rk,Rv\<rangle>rbt_map_rel (comp2lt cmp') \<rightarrow> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel"
proof -
  interpret linorder "comp2le cmp'" "comp2lt cmp'"
    using ELO by (simp add: eq_linorder_class_conv)
  show ?thesis
    by parametricity
qed

lemma rbt_linorder_impl:
  assumes ELO: "eq_linorder cmp'"
  assumes [param]: "(cmp,cmp')\<in>Rk\<rightarrow>Rk\<rightarrow>Id"
  shows 
  "(cmp_rbt cmp, cmp_map cmp') \<in> 
    (Rv\<rightarrow>Rv\<rightarrow>Id) 
    \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_map_rel (comp2lt cmp') 
    \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_map_rel (comp2lt cmp') \<rightarrow> Id"
proof -
  interpret linorder "comp2le cmp'" "comp2lt cmp'"
    using ELO by (simp add: eq_linorder_class_conv)

  show ?thesis
    unfolding cmp_map_def[abs_def] cmp_rbt_def[abs_def]
    apply (parametricity add: param_cmp_extend param_cmp_img)
    unfolding rbt_map_rel_def[abs_def] rbt_map_rel'_def br_def
    by auto
qed

lemma color_rel_sv[relator_props]: "single_valued color_rel"
  by (auto intro!: single_valuedI elim: color_rel.cases)

lemma rbt_rel_sv_aux:
  assumes SK: "single_valued Rk" 
  assumes SV: "single_valued Rv"
  assumes I1: "(a,b)\<in>(\<langle>Rk, Rv\<rangle>rbt_rel)"
  assumes I2: "(a,c)\<in>(\<langle>Rk, Rv\<rangle>rbt_rel)"
  shows "b=c"
  using I1 I2
  apply (induct arbitrary: c)
  apply (elim rbt_rel_elims)
  apply simp
  apply (elim rbt_rel_elims)
  apply (simp add: single_valuedD[OF color_rel_sv] 
    single_valuedD[OF SK] single_valuedD[OF SV])
  done

lemma rbt_rel_sv[relator_props]:
  assumes SK: "single_valued Rk" 
  assumes SV: "single_valued Rv"
  shows "single_valued (\<langle>Rk, Rv\<rangle>rbt_rel)"
  by (auto intro: single_valuedI rbt_rel_sv_aux[OF SK SV])

lemma rbt_map_rel_sv[relator_props]:
  "\<lbrakk>single_valued Rk; single_valued Rv\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rk,Rv\<rangle>rbt_map_rel lt)"
  apply (auto simp: rbt_map_rel_def rbt_map_rel'_def)
  apply (rule single_valued_relcomp)
  apply (rule rbt_rel_sv, assumption+)
  apply (rule br_sv)
  done

lemmas [autoref_rel_intf] = REL_INTFI[of "rbt_map_rel x" i_map] for x


subsection \<open>Second Part: Binding\<close>
lemma autoref_rbt_empty[autoref_rules]:
  assumes ELO: "SIDE_GEN_ALGO (eq_linorder cmp')"
  assumes [simplified,param]: "GEN_OP cmp cmp' (Rk\<rightarrow>Rk\<rightarrow>Id)"
  shows "(rbt.Empty,op_map_empty) \<in> 
    \<langle>Rk,Rv\<rangle>rbt_map_rel (comp2lt cmp')"
proof -
  interpret linorder "comp2le cmp'" "comp2lt cmp'"
    using ELO by (simp add: eq_linorder_class_conv)
  show ?thesis
    by (simp) (rule autoref_gen_rbt_empty)
qed

lemma autoref_rbt_update[autoref_rules]:
  assumes ELO: "SIDE_GEN_ALGO (eq_linorder cmp')"
  assumes [simplified,param]: "GEN_OP cmp cmp' (Rk\<rightarrow>Rk\<rightarrow>Id)"
  shows "(ord.rbt_insert (comp2lt cmp),op_map_update) \<in> 
    Rk\<rightarrow>Rv\<rightarrow>\<langle>Rk,Rv\<rangle>rbt_map_rel (comp2lt cmp') 
    \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_map_rel (comp2lt cmp')"
proof -
  interpret linorder "comp2le cmp'" "comp2lt cmp'"
    using ELO by (simp add: eq_linorder_class_conv)
  show ?thesis
    unfolding op_map_update_def[abs_def]
    apply (rule autoref_gen_rbt_insert)
    unfolding comp2lt_def[abs_def]
    by (parametricity)
qed

lemma autoref_rbt_lookup[autoref_rules]:
  assumes ELO: "SIDE_GEN_ALGO (eq_linorder cmp')"
  assumes [simplified,param]: "GEN_OP cmp cmp' (Rk\<rightarrow>Rk\<rightarrow>Id)"
  shows "(\<lambda>k t. ord.rbt_lookup (comp2lt cmp) t k, op_map_lookup) \<in> 
    Rk \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_map_rel (comp2lt cmp') \<rightarrow> \<langle>Rv\<rangle>option_rel"
proof -
  interpret linorder "comp2le cmp'" "comp2lt cmp'"
    using ELO by (simp add: eq_linorder_class_conv)
  show ?thesis
    unfolding op_map_lookup_def[abs_def]
    apply (intro fun_relI)
    apply (rule autoref_gen_rbt_lookup[param_fo])
    apply (unfold comp2lt_def[abs_def]) []
    apply (parametricity)
    apply assumption+
    done
qed

lemma autoref_rbt_delete[autoref_rules]:
  assumes ELO: "SIDE_GEN_ALGO (eq_linorder cmp')"
  assumes [simplified,param]: "GEN_OP cmp cmp' (Rk\<rightarrow>Rk\<rightarrow>Id)"
  shows "(ord.rbt_delete (comp2lt cmp),op_map_delete) \<in>
    Rk \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_map_rel (comp2lt cmp') 
       \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_map_rel (comp2lt cmp')"
proof -
  interpret linorder "comp2le cmp'" "comp2lt cmp'"
    using ELO by (simp add: eq_linorder_class_conv)
  show ?thesis
    unfolding op_map_delete_def[abs_def]
    apply (intro fun_relI)
    apply (rule autoref_gen_rbt_delete[param_fo])
    apply (unfold comp2lt_def[abs_def]) []
    apply (parametricity)
    apply assumption+
    done
qed

lemma autoref_rbt_union[autoref_rules]:
  assumes ELO: "SIDE_GEN_ALGO (eq_linorder cmp')"
  assumes [simplified,param]: "GEN_OP cmp cmp' (Rk\<rightarrow>Rk\<rightarrow>Id)"
  shows "(ord.rbt_union (comp2lt cmp),(++)) \<in>
    \<langle>Rk,Rv\<rangle>rbt_map_rel (comp2lt cmp') \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_map_rel (comp2lt cmp')
       \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_map_rel (comp2lt cmp')"
proof -
  interpret linorder "comp2le cmp'" "comp2lt cmp'"
    using ELO by (simp add: eq_linorder_class_conv)
  show ?thesis
    apply (intro fun_relI)
    apply (rule autoref_gen_rbt_union[param_fo])
    apply (unfold comp2lt_def[abs_def]) []
    apply (parametricity)
    apply assumption+
    done
qed

lemma autoref_rbt_is_iterator[autoref_ga_rules]: 
  assumes ELO: "GEN_ALGO_tag (eq_linorder cmp')"
  shows "is_map_to_sorted_list (comp2le cmp') Rk Rv (rbt_map_rel (comp2lt cmp'))
    rbt_to_list"
proof -
  interpret linorder "comp2le cmp'" "comp2lt cmp'"
    using ELO by (simp add: eq_linorder_class_conv)

  show ?thesis
    unfolding is_map_to_sorted_list_def
      it_to_sorted_list_def
    apply auto
  proof -
    fix r m'
    assume "(r, m') \<in> \<langle>Rk, Rv\<rangle>rbt_map_rel (comp2lt cmp')"
    then obtain r' where R1: "(r,r')\<in>\<langle>Rk,Rv\<rangle>rbt_rel" 
      and R2: "(r',m') \<in> rbt_map_rel' (comp2lt cmp')"
      unfolding rbt_map_rel_def by blast
    
    from R2 have "is_rbt r'" and M': "m' = rbt_lookup r'"
      unfolding rbt_map_rel'_def
      by (simp_all add: br_def)
    hence SORTED: "rbt_sorted r'"
      by (simp add: is_rbt_def)

    from map_it_to_list_linord_correct[where it = rm_iterateoi, OF 
      rm_iterateoi_correct[OF SORTED]
    ] have 
        M: "map_of (rbt_to_list r') = rbt_lookup r'"
        and D: "distinct (map fst (rbt_to_list r'))"
        and S: "sorted (map fst (rbt_to_list r'))"
      by (simp_all)

    show "\<exists>l'. (rbt_to_list r, l') \<in> \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel \<and>
            distinct l' \<and>
            map_to_set m' = set l' \<and>
            sorted_wrt (key_rel (comp2le cmp')) l'"
    proof (intro exI conjI)
      from D show "distinct (rbt_to_list r')" by (rule distinct_mapI)
      from S show "sorted_wrt (key_rel (comp2le cmp')) (rbt_to_list r')"
        unfolding key_rel_def[abs_def]
        by simp
      show "(rbt_to_list r, rbt_to_list r') \<in> \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel"
        by (parametricity add: R1)
      from M show "map_to_set m' = set (rbt_to_list r')"
        by (simp add: M' map_of_map_to_set[OF D])
    qed
  qed
qed
        
(* TODO: Reverse iterator *)

lemmas [autoref_ga_rules] = class_to_eq_linorder

lemma (in linorder) dflt_cmp_id:
  "(dflt_cmp (\<le>) (<), dflt_cmp (\<le>) (<))\<in>Id\<rightarrow>Id\<rightarrow>Id"
  by auto

lemmas [autoref_rules] = dflt_cmp_id

lemma rbt_linorder_autoref[autoref_rules]:
  assumes "SIDE_GEN_ALGO (eq_linorder cmpk')"
  assumes "SIDE_GEN_ALGO (eq_linorder cmpv')"
  assumes "GEN_OP cmpk cmpk' (Rk\<rightarrow>Rk\<rightarrow>Id)"
  assumes "GEN_OP cmpv cmpv' (Rv\<rightarrow>Rv\<rightarrow>Id)"
  shows 
  "(cmp_rbt cmpk cmpv, cmp_map cmpk' cmpv') \<in> 
       \<langle>Rk,Rv\<rangle>rbt_map_rel (comp2lt cmpk') 
    \<rightarrow> \<langle>Rk,Rv\<rangle>rbt_map_rel (comp2lt cmpk') \<rightarrow> Id"
  apply (intro fun_relI)
  apply (rule rbt_linorder_impl[param_fo])
  using assms 
  apply simp_all
  done

(* TODO: Move. This belongs to generic algorithms for orders *)
lemma map_linorder_impl[autoref_ga_rules]:
  assumes "GEN_ALGO_tag (eq_linorder cmpk)"
  assumes "GEN_ALGO_tag (eq_linorder cmpv)"
  shows "eq_linorder (cmp_map cmpk cmpv)"
  using assms apply simp_all
  using map_ord_eq_linorder .

lemma set_linorder_impl[autoref_ga_rules]:
  assumes "GEN_ALGO_tag (eq_linorder cmpk)"
  shows "eq_linorder (cmp_set cmpk)"
  using assms apply simp_all
  using set_ord_eq_linorder .

lemma (in linorder) rbt_map_rel_finite_aux:
  "finite_map_rel (\<langle>Rk,Rv\<rangle>rbt_map_rel (<))"
  unfolding finite_map_rel_def
  by (auto simp: rbt_map_rel_def rbt_map_rel'_def br_def)

lemma rbt_map_rel_finite[relator_props]: 
  assumes ELO: "GEN_ALGO_tag (eq_linorder cmpk)"
  shows "finite_map_rel (\<langle>Rk,Rv\<rangle>rbt_map_rel (comp2lt cmpk))"
proof -
  interpret linorder "comp2le cmpk" "comp2lt cmpk"
    using ELO by (simp add: eq_linorder_class_conv)
  show ?thesis
    using rbt_map_rel_finite_aux .
qed

abbreviation 
  "dflt_rm_rel \<equiv> rbt_map_rel (comp2lt (dflt_cmp (\<le>) (<)))"

lemmas [autoref_post_simps] = dflt_cmp_inv2 dflt_cmp_2inv

lemma [simp,autoref_post_simps]: "ord.rbt_ins (<) = rbt_ins"
proof (intro ext, goal_cases)
  case (1 x xa xb xc) thus ?case
    apply (induct x xa xb xc rule: rbt_ins.induct)
    apply (simp_all add: ord.rbt_ins.simps)
    done
qed

lemma [autoref_post_simps]: "ord.rbt_lookup ((<)::_::linorder\<Rightarrow>_) = rbt_lookup"
  unfolding ord.rbt_lookup_def rbt_lookup_def ..

lemma [simp,autoref_post_simps]:
  "ord.rbt_insert_with_key (<) = rbt_insert_with_key"
  "ord.rbt_insert (<) = rbt_insert"
  unfolding 
    ord.rbt_insert_with_key_def[abs_def] rbt_insert_with_key_def[abs_def]
    ord.rbt_insert_def[abs_def] rbt_insert_def[abs_def]
  by simp_all

(* TODO: Move, probably to some orderings setup theory *)
lemma autoref_comp2eq[autoref_rules_raw]:
  assumes PRIO_TAG_GEN_ALGO
  assumes ELC: "SIDE_GEN_ALGO (eq_linorder cmp')"
  assumes [simplified,param]: "GEN_OP cmp cmp' (R\<rightarrow>R\<rightarrow>Id)"
  shows "(comp2eq cmp, (=)) \<in> R\<rightarrow>R\<rightarrow>Id"
proof -
  from ELC have 1: "eq_linorder cmp'" by simp
  show ?thesis
    apply (subst eq_linorder_comp2eq_eq[OF 1,symmetric])
    by parametricity
qed

lemma pi'_rm[icf_proper_iteratorI]: 
  "proper_it' rm_iterateoi rm_iterateoi"
  "proper_it' rm_reverse_iterateoi rm_reverse_iterateoi"
  apply (rule proper_it'I)
  apply (rule pi_rm)
  apply (rule proper_it'I)
  apply (rule pi_rm_rev)
  done

declare pi'_rm[proper_it]


lemmas autoref_rbt_rules = 
  autoref_rbt_empty
  autoref_rbt_lookup
  autoref_rbt_update
  autoref_rbt_delete
  autoref_rbt_union

lemmas autoref_rbt_rules_linorder[autoref_rules_raw] = 
  autoref_rbt_rules[where Rk="Rk"] for Rk :: "(_\<times>_::linorder) set"

end
