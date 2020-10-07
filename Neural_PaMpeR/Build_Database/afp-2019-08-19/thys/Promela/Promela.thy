section "Formalization of Promela semantics"
theory Promela
imports 
  PromelaDatastructures
  PromelaInvariants
  PromelaStatistics
begin

text \<open>Auxiliary\<close>

lemma mod_integer_le:
  "a \<le> b \<Longrightarrow> 0 < a \<Longrightarrow> x mod (a + 1) \<le> b" for a b x :: integer
  by (metis add_pos_nonneg discrete not_less order.strict_trans2
    unique_euclidean_semiring_numeral_class.pos_mod_bound zero_le_one)

lemma mod_integer_ge:
  "b \<le> 0 \<Longrightarrow> 0 < a \<Longrightarrow> b \<le> x mod (a+1)" for a b x :: integer
  by (metis dual_order.trans less_add_one order.strict_trans
    unique_euclidean_semiring_numeral_class.pos_mod_sign)

text \<open>
  After having defined the datastructures, we present in this theory how to construct the transition system and how to generate the successors of a state, \ie the real semantics of a Promela program.
  For the first task, we take the enriched AST as input, the second one operates on the transition system.
\<close>

subsection \<open>Misc Helpers\<close>
definition add_label :: "String.literal \<Rightarrow> labels \<Rightarrow> nat \<Rightarrow> labels" where
  "add_label l lbls pos = (
     case lm.lookup l lbls of 
       None \<Rightarrow> lm.update l pos lbls
     | Some _ \<Rightarrow> abortv STR ''Label given twice: '' l (\<lambda>_. lbls))"

definition min_prio :: "edge list \<Rightarrow> integer \<Rightarrow> integer" where
  "min_prio es start = Min ((prio ` set es) \<union> {start})"

lemma min_prio_code [code]:
  "min_prio es start = fold  (\<lambda>e pri. if prio e < pri then prio e else pri) es start"
proof -
  from Min.set_eq_fold have "Min (set (start # map prio es)) = fold min (map prio es) start" by metis
  also have "... = fold (min \<circ> prio) es start" by (simp add: fold_map)
  also have "... = fold  (\<lambda>e pri. if prio e < pri then prio e else pri) es start" by (auto intro!: fold_cong)
  finally show ?thesis by (simp add: min_prio_def)
qed
  
definition for_all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "for_all f xs \<longleftrightarrow> (\<forall>x \<in> set xs. f x)"

lemma for_all_code[code]:
  "for_all f xs \<longleftrightarrow> foldli xs id (\<lambda>kv \<sigma>. f kv) True"
  by (simp add: for_all_def foldli_conj)

definition find_remove :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option \<times> 'a list" where
  "find_remove P xs = (case List.find P xs of None \<Rightarrow> (None, xs)
                                            | Some x \<Rightarrow> (Some x, List.remove1 x xs))"

lemma find_remove_code [code]:
  "find_remove P [] = (None, [])"
  "find_remove P (x#xs) = (if P x then (Some x, xs)
                           else apsnd (Cons x) (find_remove P xs))"
  by (induct xs) (auto simp add: find_remove_def dest: find_SomeD split: option.split) 

lemma find_remove_subset:
  "find_remove P xs = (res, xs') \<Longrightarrow> set xs' \<subseteq> set xs"
unfolding find_remove_def
using set_remove1_subset
by (force split: option.splits)

lemma find_remove_length:
  "find_remove P xs = (res, xs') \<Longrightarrow> length xs' \<le> length xs"
unfolding find_remove_def
by (induct xs arbitrary: res xs') (auto split: if_splits option.splits)

subsection \<open>Variable handling\<close>

text \<open>
  Handling variables, with their different scopes (global vs. local), 
  and their different types (array vs channel vs bounded) is one of the main challenges
  of the implementation. 
\<close>

fun lookupVar :: "variable \<Rightarrow> integer option \<Rightarrow> integer" where
  "lookupVar (Var _ val) None = val"
| "lookupVar (Var _ _) (Some _) = abort STR ''Array used on var'' (\<lambda>_.0)"
| "lookupVar (VArray _ _ vals) None = vals !! 0" (* sic! *)
| "lookupVar (VArray _ siz vals) (Some idx) = vals !! nat_of_integer idx"

primrec checkVarValue :: "varType \<Rightarrow> integer \<Rightarrow> integer" where
  "checkVarValue (VTBounded lRange hRange) val = (
     if val \<le> hRange \<and> val \<ge> lRange then val
     else \<comment> \<open>overflowing is well-defined and may actually be used (e.g. bool)\<close>
        if lRange = 0 \<and> val > 0 
        then val mod (hRange + 1)
        else \<comment> \<open>we do not want to implement C-semantics (ie type casts)\<close>
           abort STR ''Value overflow'' (\<lambda>_. lRange))"
| "checkVarValue VTChan val = (
     if val < min_var_value \<or> val > max_var_value 
     then abort STR ''Value overflow'' (\<lambda>_. 0) 
     else val)"

lemma [simp]:
  "variable_inv (Var VTChan 0)"
by simp

context
  fixes type :: varType
  assumes "varType_inv type"
begin

lemma checkVarValue_bounded:
  "checkVarValue type val \<in> {min_var_value..max_var_value}"
  using \<open>varType_inv type\<close>
  by (cases type) (auto intro: mod_integer_le mod_integer_ge)

lemma checkVarValue_bounds:
  "min_var_value \<le> checkVarValue type val"
  "checkVarValue type val \<le> max_var_value"
  using checkVarValue_bounded [of val] by simp_all

lemma checkVarValue_Var:
  "variable_inv (Var type (checkVarValue type val))"
  using \<open>varType_inv type\<close> by (simp add: checkVarValue_bounds)

end

fun editVar :: "variable \<Rightarrow> integer option \<Rightarrow> integer \<Rightarrow> variable" where
  "editVar (Var type _ ) None val = Var type (checkVarValue type val)"
| "editVar (Var _ _) (Some _) _ = abort STR ''Array used on var'' (\<lambda>_. Var VTChan 0)"
| "editVar (VArray type siz vals) None val = (
     let lv = IArray.list_of vals in
     let v' = lv[0:=checkVarValue type val] in
     VArray type siz (IArray v'))"
| "editVar (VArray type siz vals) (Some idx) val = (
     let lv = IArray.list_of vals in
     let v' = lv[(nat_of_integer idx):=checkVarValue type val] in
     VArray type siz (IArray v'))"

lemma editVar_variable_inv:
  assumes "variable_inv v"
  shows "variable_inv (editVar v idx val)"
proof (cases v)
  case (Var type val) with assms have "varType_inv type" by simp
  with Var show ?thesis 
    by (cases idx) 
       (auto intro!: checkVarValue_Var 
             simp del: checkVarValue.simps variable_inv.simps)
next
  case (VArray type siz vals) 
  with assms have [simp, intro!]: "varType_inv type" by simp
  
  show ?thesis
  proof (cases idx)
    case None with assms VArray show ?thesis 
      by (cases "IArray.list_of vals") (auto intro!: checkVarValue_bounds)
  next
    case (Some i)
    note upd_cases = in_set_upd_cases[where l="IArray.list_of vals" and i="nat_of_integer i"]

    from Some VArray assms show ?thesis
      by (cases type)
        (auto elim!: upd_cases intro!: mod_integer_le mod_integer_ge simp add: min_var_value_def)
  qed
qed

definition getVar' 
  :: "bool \<Rightarrow> String.literal \<Rightarrow> integer option 
      \<Rightarrow> 'a gState_scheme \<Rightarrow> pState 
      \<Rightarrow> integer option" 
where
  "getVar' gl v idx g p = (
          let vars = if gl then gState.vars g else pState.vars p in
          map_option (\<lambda>x. lookupVar x idx) (lm.lookup v vars))"

definition setVar' 
  :: "bool \<Rightarrow> String.literal \<Rightarrow> integer option 
      \<Rightarrow> integer 
      \<Rightarrow> 'a gState_scheme \<Rightarrow> pState 
      \<Rightarrow> 'a gState_scheme * pState"
 where
  "setVar' gl v idx val g p = (
     if gl then
        if v = STR ''_'' then (g,p) \<comment> \<open>\<open>''_''\<close> is a write-only scratch variable\<close>
        else case lm.lookup v (gState.vars g) of
               None \<Rightarrow> abortv STR ''Unknown global variable: '' v (\<lambda>_. (g,p))
             | Some x \<Rightarrow> (g\<lparr>gState.vars := lm.update v (editVar x idx val) 
                                                       (gState.vars g)\<rparr>
                         , p)
     else
        case lm.lookup v (pState.vars p) of
          None \<Rightarrow> abortv STR ''Unknown proc variable: '' v (\<lambda>_. (g,p))
        | Some x \<Rightarrow> (g, p\<lparr>pState.vars := lm.update v (editVar x idx val) 
                                                     (pState.vars p)\<rparr>))"

lemma setVar'_gState_inv:
  assumes "gState_inv prog g"
  shows "gState_inv prog (fst (setVar' gl v idx val g p))"
unfolding setVar'_def using assms
by (auto simp add: gState_inv_def lm.correct 
         intro: editVar_variable_inv 
         split: option.splits)

lemma setVar'_gState_progress_rel:
  assumes "gState_inv prog g"
  shows "(g, fst (setVar' gl v idx val g p)) \<in> gState_progress_rel prog"
apply (intro gState_progress_relI)
      apply (fact assms)
    apply (fact setVar'_gState_inv[OF assms])
  apply (auto simp: setVar'_def lm.correct split: option.splits)
done

lemma vardict_inv_process_names:
  assumes "vardict_inv ss proc v"
  and "lm.lookup k v = Some x"
  shows "k \<in> process_names ss proc"
using assms
by (auto simp add: lm.correct vardict_inv_def)

lemma vardict_inv_variable_inv:
  assumes "vardict_inv ss proc v"
  and "lm.lookup k v = Some x"
  shows "variable_inv x"
using assms
by (auto simp add: lm.correct vardict_inv_def)

lemma vardict_inv_updateI:
  assumes "vardict_inv ss proc vs"
  and "x \<in> process_names ss proc"
  and "variable_inv v"
  shows "vardict_inv ss proc (lm.update x v vs)"
using assms
by (auto simp add: lm.correct vardict_inv_def)

lemma update_vardict_inv:
  assumes "vardict_inv ss proc v"
  and "lm.lookup k v = Some x"
  and "variable_inv x'"
  shows "vardict_inv ss proc (lm.update k x' v)"
using assms
by (auto intro!: vardict_inv_updateI vardict_inv_process_names)

lemma setVar'_pState_inv:
  assumes "pState_inv prog p"
  shows "pState_inv prog (snd (setVar' gl v idx val g p))"
unfolding setVar'_def using assms
by (auto split: if_splits option.splits 
         simp add: pState_inv_def
         intro: update_vardict_inv editVar_variable_inv vardict_inv_variable_inv)

lemma setVar'_cl_inv:
  assumes "cl_inv (g,p)"
  shows "cl_inv (setVar' gl v idx val g p)"
unfolding setVar'_def using assms
by (auto split: if_splits option.splits)

definition withVar' 
  :: "bool \<Rightarrow> String.literal \<Rightarrow> integer option 
      \<Rightarrow> (integer \<Rightarrow> 'x) 
      \<Rightarrow> 'a gState_scheme \<Rightarrow> pState 
      \<Rightarrow> 'x"
where
  "withVar' gl v idx f g p = f (the (getVar' gl v idx g p))"

definition withChannel' 
  :: "bool \<Rightarrow> String.literal \<Rightarrow> integer option 
      \<Rightarrow> (nat \<Rightarrow> channel \<Rightarrow> 'x) 
      \<Rightarrow> 'a gState_scheme \<Rightarrow> pState 
      \<Rightarrow> 'x"
where
  "withChannel' gl v idx f g p = ( 
     let error = \<lambda>_. abortv STR ''Variable is not a channel: '' v 
                                (\<lambda>_. f 0 InvChannel) in
     let abort = \<lambda>_. abortv STR ''Channel already closed / invalid: '' v
                                (\<lambda>_. f 0 InvChannel)
     in withVar' gl v idx (\<lambda>i. let i = nat_of_integer i in 
                               if i \<ge> length (channels g) then error () 
                               else let c = channels g ! i in
                                    case c of
                                      InvChannel \<Rightarrow> abort ()
                                    | _ \<Rightarrow> f i c) g p)"

subsection \<open>Expressions\<close>

text \<open>Expressions are free of side-effects. 

This is in difference to SPIN, where @{term run} is an expression with side-effect. We treat @{term run} as a statement.\<close>

abbreviation "trivCond x \<equiv> if x then 1 else 0"

fun exprArith :: "'a gState_scheme \<Rightarrow> pState \<Rightarrow> expr \<Rightarrow> integer"
and pollCheck :: "'a gState_scheme \<Rightarrow> pState \<Rightarrow> channel \<Rightarrow> recvArg list \<Rightarrow> bool 
                   \<Rightarrow> bool"
and recvArgsCheck :: "'a gState_scheme \<Rightarrow> pState \<Rightarrow> recvArg list \<Rightarrow> integer list 
                       \<Rightarrow> bool" 
where
  "exprArith g p (ExprConst x) = x"
| "exprArith g p (ExprMConst x _) = x"

| "exprArith g p ExprTimeOut = trivCond (timeout g)"

| "exprArith g p (ExprLen (ChanRef (VarRef gl name None))) = 
     withChannel' gl name None (
       \<lambda>_ c. case c of 
                Channel _ _ q \<Rightarrow> integer_of_nat (length q) 
              | HSChannel _ \<Rightarrow> 0) g p"

| "exprArith g p (ExprLen (ChanRef (VarRef gl name (Some idx)))) = 
     withChannel' gl name (Some (exprArith g p idx)) (
      \<lambda>_ c. case c of 
              Channel _ _ q \<Rightarrow> integer_of_nat (length q) 
            | HSChannel _ \<Rightarrow> 0) g p"

| "exprArith g p (ExprEmpty (ChanRef (VarRef gl name None))) = 
     trivCond (withChannel' gl name None (
       \<lambda>_ c. case c of Channel _ _ q \<Rightarrow> (q = []) 
                     | HSChannel _ \<Rightarrow> True) g p)"

| "exprArith g p (ExprEmpty (ChanRef (VarRef gl name (Some idx)))) = 
     trivCond (withChannel' gl name (Some (exprArith g p idx)) (
       \<lambda>_ c. case c of Channel _ _ q \<Rightarrow> (q = []) 
                     | HSChannel _ \<Rightarrow> True) g p)"

| "exprArith g p (ExprFull (ChanRef(VarRef gl name None))) = 
     trivCond (withChannel' gl name None (
       \<lambda>_ c. case c of 
               Channel cap _ q \<Rightarrow> integer_of_nat (length q) \<ge> cap 
             | HSChannel _ \<Rightarrow> False) g p)"

| "exprArith g p (ExprFull (ChanRef(VarRef gl name (Some idx)))) = 
     trivCond (withChannel' gl name (Some (exprArith g p idx)) (
       \<lambda>_ c. case c of 
               Channel cap _ q \<Rightarrow> integer_of_nat (length q) \<ge> cap 
             | HSChannel _ \<Rightarrow> False) g p)"

| "exprArith g p (ExprVarRef (VarRef gl name None)) = 
     withVar' gl name None id g p"

| "exprArith g p (ExprVarRef (VarRef gl name (Some idx))) = 
     withVar' gl name (Some (exprArith g p idx)) id g p"

| "exprArith g p (ExprUnOp UnOpMinus expr) = 0 - exprArith g p expr"
| "exprArith g p (ExprUnOp UnOpNeg expr) = ((exprArith g p expr) + 1) mod 2"

| "exprArith g p (ExprBinOp BinOpAdd lexpr rexpr) = 
     (exprArith g p lexpr) + (exprArith g p rexpr)"

| "exprArith g p (ExprBinOp BinOpSub lexpr rexpr) = 
     (exprArith g p lexpr) - (exprArith g p rexpr)"

| "exprArith g p (ExprBinOp BinOpMul lexpr rexpr) = 
     (exprArith g p lexpr) * (exprArith g p rexpr)"

| "exprArith g p (ExprBinOp BinOpDiv lexpr rexpr) = 
     (exprArith g p lexpr) div (exprArith g p rexpr)"

| "exprArith g p (ExprBinOp BinOpMod lexpr rexpr) = 
     (exprArith g p lexpr) mod (exprArith g p rexpr)"

| "exprArith g p (ExprBinOp BinOpGr lexpr rexpr) = 
     trivCond (exprArith g p lexpr > exprArith g p rexpr)"

| "exprArith g p (ExprBinOp BinOpLe lexpr rexpr) = 
     trivCond (exprArith g p lexpr < exprArith g p rexpr)"

| "exprArith g p (ExprBinOp BinOpGEq lexpr rexpr) = 
     trivCond (exprArith g p lexpr \<ge> exprArith g p rexpr)"

| "exprArith g p (ExprBinOp BinOpLEq lexpr rexpr) = 
     trivCond (exprArith g p lexpr \<le> exprArith g p rexpr)"

| "exprArith g p (ExprBinOp BinOpEq lexpr rexpr) = 
     trivCond (exprArith g p lexpr = exprArith g p rexpr)"

| "exprArith g p (ExprBinOp BinOpNEq lexpr rexpr) = 
     trivCond (exprArith g p lexpr \<noteq> exprArith g p rexpr)"

| "exprArith g p (ExprBinOp BinOpAnd lexpr rexpr) = 
     trivCond (exprArith g p lexpr \<noteq> 0 \<and> exprArith g p rexpr \<noteq> 0)"

| "exprArith g p (ExprBinOp BinOpOr lexpr rexpr) = 
     trivCond (exprArith g p lexpr \<noteq> 0 \<or> exprArith g p rexpr \<noteq> 0)"

| "exprArith g p (ExprCond cexpr texpr fexpr) = 
     (if exprArith g p cexpr \<noteq> 0 then exprArith g p texpr 
      else exprArith g p fexpr)"

| "exprArith g p (ExprPoll (ChanRef (VarRef gl name None)) rs srt) = 
     trivCond (withChannel' gl name None (
       \<lambda>_ c. pollCheck g p c rs srt) g p)"

| "exprArith g p (ExprPoll (ChanRef (VarRef gl name (Some idx))) rs srt) = 
     trivCond (withChannel' gl name (Some (exprArith g p idx)) (
       \<lambda>_ c. pollCheck g p c rs srt) g p)"

| "pollCheck g p InvChannel _ _ = 
     abort STR ''Channel already closed / invalid.'' (\<lambda>_. False)"
| "pollCheck g p (HSChannel _) _ _ = False"
| "pollCheck g p (Channel _ _ q) rs srt = (
     if q = [] then False
     else if \<not> srt then recvArgsCheck g p rs (hd q)
     else List.find (recvArgsCheck g p rs) q \<noteq> None)"

| "recvArgsCheck _ _ [] [] = True"
| "recvArgsCheck _ _ _  [] = 
     abort STR ''Length mismatch on receiving.'' (\<lambda>_. False)"
| "recvArgsCheck _ _ []  _ = 
     abort STR ''Length mismatch on receiving.'' (\<lambda>_. False)"
| "recvArgsCheck g p (r#rs) (v#vs) = ((
       case r of 
          RecvArgConst c \<Rightarrow> c = v
        | RecvArgMConst c _ \<Rightarrow> c = v
        | RecvArgVar var \<Rightarrow> True
        | RecvArgEval e \<Rightarrow> exprArith g p e = v ) \<and> recvArgsCheck g p rs vs)"

text \<open>@{const getVar'} etc.\ do operate on name, index, \ldots directly. Lift them to use @{const VarRef} instead.\<close>

fun liftVar where
  "liftVar f (VarRef gl v idx) argm g p = 
      f gl v (map_option (exprArith g p) idx) argm g p"

definition "getVar v = liftVar (\<lambda>gl v idx arg. getVar' gl v idx) v ()"
definition "setVar = liftVar setVar'"
definition "withVar = liftVar withVar'"

primrec withChannel
  where "withChannel (ChanRef v) = liftVar withChannel' v"

lemma setVar_gState_progress_rel:
  assumes "gState_inv prog g"
  shows "(g, fst (setVar v val g p)) \<in> gState_progress_rel prog"
unfolding setVar_def
by (cases v) (simp add: setVar'_gState_progress_rel[OF assms])

lemmas setVar_gState_inv = 
  setVar_gState_progress_rel[THEN gState_progress_rel_gState_invI2]

lemma setVar_pState_inv:
  assumes "pState_inv prog p"
  shows "pState_inv prog (snd (setVar v val g p))"
unfolding setVar_def 
by (cases v) (auto simp add: setVar'_pState_inv assms)

lemma setVar_cl_inv:
  assumes "cl_inv (g,p)"
  shows "cl_inv (setVar v val g p)"
unfolding setVar_def 
by (cases v) (auto simp add: setVar'_cl_inv assms)

subsection \<open>Variable declaration\<close>

lemma channel_inv_code [code]:
  "channel_inv (Channel cap ts q) 
  \<longleftrightarrow> cap \<le> max_array_size 
    \<and> 0 \<le> cap 
    \<and> for_all varType_inv ts 
    \<and> length ts \<le> max_array_size 
    \<and> length q \<le> max_array_size 
    \<and> for_all (\<lambda>x. length x = length ts  
                   \<and> for_all (\<lambda>y. y \<ge> min_var_value 
                                 \<and> y \<le> max_var_value) x) q" 
  "channel_inv (HSChannel ts) 
  \<longleftrightarrow> for_all varType_inv ts \<and> length ts \<le> max_array_size"
  by (auto simp add: for_all_def) force+

primrec toVariable 
  :: "'a gState_scheme \<Rightarrow> pState \<Rightarrow> varDecl \<Rightarrow> String.literal * variable * channels" 
where
  "toVariable g p (VarDeclNum lb hb name siz init) = (
     let type = VTBounded lb hb in
     if \<not> varType_inv type then abortv STR ''Invalid var def (varType_inv failed): '' name 
                                       (\<lambda>_. (name, Var VTChan 0, []))
     else
       let 
         init = checkVarValue type (case init of 
                                      None \<Rightarrow> 0 
                                    | Some e \<Rightarrow> exprArith g p e);
         v = (case siz of 
                None \<Rightarrow> Var type init 
              | Some s \<Rightarrow> if nat_of_integer s \<le> max_array_size 
                         then VArray type (nat_of_integer s) 
                                          (IArray.tabulate (s, \<lambda>_. init))
                         else abortv STR ''Invalid var def (array too large): '' name
                                      (\<lambda>_. Var VTChan 0))
        in
           (name, v, []))"

| "toVariable g p (VarDeclChan name siz types) = (
     let 
       size = (case siz of None \<Rightarrow> 1 | Some s \<Rightarrow> nat_of_integer s);
       chans = (case types of 
                  None \<Rightarrow> []
                | Some (cap, tys) \<Rightarrow> 
                    let C = (if cap = 0 then HSChannel tys 
                             else Channel cap tys []) in
                    if \<not> channel_inv C 
                    then abortv STR ''Invalid var def (channel_inv failed): '' 
                                name (\<lambda>_. [])
                    else replicate size C);
       cidx = (case types of 
                 None \<Rightarrow> 0 
               | Some _ \<Rightarrow> integer_of_nat (length (channels g)));
       v = (case siz of 
              None \<Rightarrow> Var VTChan cidx
            | Some s \<Rightarrow> if nat_of_integer s \<le> max_array_size 
                       then VArray VTChan (nat_of_integer s) 
                                          (IArray.tabulate (s, 
                                             \<lambda>i. if cidx = 0 then 0 
                                                 else i + cidx))
                       else abortv STR ''Invalid var def (array too large): '' 
                                   name (\<lambda>_. Var VTChan 0))
     in
        (name, v, chans))"

lemma toVariable_variable_inv:
  assumes "gState_inv prog g"
  shows "variable_inv (fst (snd (toVariable g p v)))"
using assms
apply (cases v)
  apply (auto intro!: checkVarValue_Var 
              simp del: variable_inv.simps checkVarValue.simps varType_inv.simps 
              split: if_splits option.splits)
      apply (auto intro!: mod_integer_ge mod_integer_le simp add: min_var_value_def)
    apply (simp_all add: assms gState_inv_def 
               max_channels_def max_var_value_def min_var_value_def max_array_size_def)
    including integer.lifting
    apply (transfer', simp)+
done

lemma toVariable_channels_inv:
  shows "\<forall>x \<in> set (snd (snd (toVariable g p v))). channel_inv x"
by (cases v) auto

lemma toVariable_channels_inv':
  shows "toVariable g p v = (a,b,c) \<Longrightarrow> \<forall>x \<in> set c. channel_inv x"
using toVariable_channels_inv
by (metis snd_conv)

lemma toVariable_variable_inv':
  shows "gState_inv prog g \<Longrightarrow> toVariable g p v = (a,b,c) \<Longrightarrow> variable_inv b"
by (metis snd_conv fst_conv toVariable_variable_inv)

definition mkChannels 
  :: "'a gState_scheme \<Rightarrow> pState \<Rightarrow> channels \<Rightarrow> 'a gState_scheme * pState"
 where
  "mkChannels g p cs = (
     if cs = [] then (g,p) else 
     let l = length (channels g) in
     if l + length cs > max_channels 
     then abort STR ''Too much channels'' (\<lambda>_.  (g,p))
     else let
            cs\<^sub>p = map integer_of_nat [l..<l + length cs];
            g' = g\<lparr>channels := channels g @ cs\<rparr>;
            p' = p\<lparr>pState.channels := pState.channels p @ cs\<^sub>p\<rparr>
          in 
            (g', p'))"

lemma mkChannels_gState_progress_rel:
  "gState_inv prog g 
   \<Longrightarrow> set cs \<subseteq> Collect channel_inv 
   \<Longrightarrow> (g, fst (mkChannels g p cs)) \<in> gState_progress_rel prog"
unfolding mkChannels_def
by (intro gState_progress_relI) 
   (auto simp add: gState_inv_def gState.defs cl_inv_def)

lemmas mkChannels_gState_inv = 
  mkChannels_gState_progress_rel[THEN gState_progress_rel_gState_invI2]

lemma mkChannels_pState_inv:
  "pState_inv prog p 
   \<Longrightarrow> cl_inv (g,p) 
   \<Longrightarrow> pState_inv prog (snd (mkChannels g p cs))"
unfolding mkChannels_def
including integer.lifting
  apply (auto simp add: pState_inv_def pState.defs gState_inv_def dest!: cl_inv_lengthD)
    apply (transfer', simp)+
    done

lemma mkChannels_cl_inv:
  "cl_inv (g,p) \<Longrightarrow> cl_inv (mkChannels g p cs)"
unfolding mkChannels_def
by (auto simp add: pState.defs dest: cl_inv_lengthD intro!: cl_invI)

definition mkVarChannel 
  :: "varDecl 
      \<Rightarrow> ((var_dict \<Rightarrow> var_dict) \<Rightarrow> 'a gState_scheme * pState 
         \<Rightarrow> 'a gState_scheme * pState) 
      \<Rightarrow> 'a gState_scheme \<Rightarrow> pState 
      \<Rightarrow> 'a gState_scheme * pState" 
where
  "mkVarChannel v upd g p = (
         let 
             (k,v,cs) = toVariable g p v;
             (g',p') = upd (lm.update k v) (g,p)
         in
            mkChannels g' p' cs)"

lemma mkVarChannel_gState_inv:
  assumes "gState_inv prog g"
  and "\<And>k v' cs. toVariable g p v = (k,v',cs) 
                 \<Longrightarrow> gState_inv prog (fst (upd (lm.update k v') (g,p)))"
  shows "gState_inv prog (fst (mkVarChannel v upd g p))"
using assms unfolding mkVarChannel_def
by (force split: varDecl.split prod.split
          intro!: mkChannels_gState_inv
          dest: toVariable_channels_inv') 

lemma mkVarChannel_gState_progress_rel:
  assumes "gState_inv prog g"
  and "\<And>k v' cs. toVariable g p v = (k,v',cs) 
             \<Longrightarrow> (g, fst (upd (lm.update k v') (g,p))) \<in> gState_progress_rel prog"
  shows "(g, fst (mkVarChannel v upd g p)) \<in> gState_progress_rel prog"
proof -
  obtain k v' cs where 1: "toVariable g p v = (k,v',cs)" by (metis prod.exhaust)
  obtain g' p' where 2: "(g',p') = upd (lm.update k v') (g,p)" by (metis prod.exhaust)
  with 1 assms have *: "(g, g') \<in> gState_progress_rel prog" by (metis fst_conv)

  also from 1 2 have "(g', fst (mkChannels g' p' cs)) \<in> gState_progress_rel prog"
    by (force intro!: mkChannels_gState_progress_rel gState_progress_rel_gState_invI2[OF *]
              dest: toVariable_channels_inv')
  finally have "(g, fst (mkChannels g' p' cs)) \<in> gState_progress_rel prog" .
  thus ?thesis using 1 2 by (auto simp add: mkVarChannel_def split: prod.split)
qed
  
lemma mkVarChannel_pState_inv:
  assumes "pState_inv prog p"
  and "cl_inv (g,p)"
  and "\<And>k v' cs. toVariable g p v = (k,v',cs) 
                  \<Longrightarrow> cl_inv (upd (lm.update k v') (g,p))"
  and "\<And>k v' cs. toVariable g p v = (k,v',cs) 
                  \<Longrightarrow> pState_inv prog (snd (upd (lm.update k v') (g,p)))"
  shows "pState_inv prog (snd (mkVarChannel v upd g p))"
using assms unfolding mkVarChannel_def
by (force split: varDecl.split prod.split 
          intro!: mkChannels_pState_inv)

lemma mkVarChannel_cl_inv:
  assumes "cl_inv (g,p)"
  and "\<And>k v' cs. toVariable g p v = (k,v',cs) 
                 \<Longrightarrow> cl_inv (upd (lm.update k v') (g,p))"
  shows "cl_inv (mkVarChannel v upd g p)"
using assms unfolding mkVarChannel_def
by (force split: varDecl.split prod.splits 
          intro!: mkChannels_cl_inv)

definition mkVarChannelProc 
  :: "procVarDecl \<Rightarrow> 'a gState_scheme \<Rightarrow> pState \<Rightarrow> 'a gState_scheme * pState" 
where
  "mkVarChannelProc v g p = (
     let 
       v' = case v of
              ProcVarDeclNum lb hb name siz init \<Rightarrow> 
                  VarDeclNum lb hb name siz init
           | ProcVarDeclChan name siz \<Rightarrow> 
                 VarDeclChan name siz None;
       (k,v,cs) = toVariable g p v' 
     in 
       mkVarChannel v' (apsnd \<circ> pState.vars_update) g p)"

lemma mkVarChannelProc_gState_progress_rel:
  assumes "gState_inv prog g"
  shows "(g, fst (mkVarChannelProc v g p)) \<in> gState_progress_rel prog"
unfolding mkVarChannelProc_def
using assms
by (auto intro!: mkVarChannel_gState_progress_rel)

lemmas mkVarChannelProc_gState_inv = 
  mkVarChannelProc_gState_progress_rel[THEN gState_progress_rel_gState_invI2]

lemma toVariable_name:
  "toVariable g p (VarDeclNum lb hb name sz init) = (x,a,b) \<Longrightarrow> x = name"
  "toVariable g p (VarDeclChan name sz t) = (x, a, b) \<Longrightarrow> x = name"
by (auto split: if_splits)

declare toVariable.simps[simp del]

lemma statesDecls_process_names:
  assumes "v \<in> statesDecls (states prog !! (pState.idx p))"
  shows "procVarDeclName v \<in> process_names (states prog !! (pState.idx p)) 
                                           (processes prog !! (pState.idx p))"
using assms
by (cases "processes prog !! (pState.idx p)") (auto simp add: statesNames_def)

lemma mkVarChannelProc_pState_inv:
  assumes "pState_inv prog p"
  and "gState_inv prog g"
  and "cl_inv (g, p)"
  and decl: "v \<in> statesDecls (states prog !! (pState.idx p))"
  shows "pState_inv prog (snd (mkVarChannelProc v g p))"
unfolding mkVarChannelProc_def
using assms statesDecls_process_names[OF decl]
by (auto intro!: mkVarChannel_pState_inv)
   (auto dest: toVariable_name 
         split: procVarDecl.splits 
         intro: toVariable_variable_inv' vardict_inv_updateI
         simp add: pState_inv_def)

lemma mkVarChannelProc_cl_inv:
  assumes "cl_inv (g,p)"
  shows "cl_inv (mkVarChannelProc v g p)"
unfolding mkVarChannelProc_def using assms
by (auto intro!: mkVarChannel_cl_inv)

subsection \<open>Folding\<close>
text \<open>
  Fold over lists (and lists of lists) of @{typ step}/@{typ stmnt}. The folding functions are 
  doing a bit more than that, e.g.\ ensuring the offset into the program array is correct. 
\<close>

definition step_fold' where
  "step_fold' g steps (lbls :: labels) pri pos 
             (nxt :: edgeIndex) (onxt :: edgeIndex option) iB = 
     foldr (\<lambda>step (pos, nxt, lbls, es). 
              let (e,enxt,lbls) = g step (lbls, pri, pos, nxt, onxt, iB)
              in (pos + length e, enxt, lbls, es@e)
    ) steps (pos, nxt, lbls, [])"

definition step_fold where
  "step_fold g steps lbls pri pos nxt onxt iB = (
         let (_,nxt,lbls,s) = step_fold' g steps lbls pri pos nxt onxt iB
          in (s,nxt,lbls))"

lemma step_fold'_cong:
  assumes "lbls = lbls'"
  and "pri = pri'"
  and "pos = pos'"
  and "steps = steps'"
  and "nxt = nxt'"
  and "onxt = onxt'"
  and "iB = iB'"
  and "\<And>x d. x \<in> set steps \<Longrightarrow> g x d = g' x d"
  shows "step_fold' g steps lbls pri pos nxt onxt iB = 
         step_fold' g' steps' lbls' pri' pos' nxt' onxt' iB'"
unfolding step_fold'_def 
by (auto intro: foldr_cong simp add: assms)

lemma step_fold_cong[fundef_cong]:
  assumes "lbls = lbls'"
  and "pri = pri'"
  and "pos = pos'"
  and "steps = steps'"
  and "nxt = nxt'"
  and "onxt = onxt'"
  and "iB = iB'"
  and "\<And>x d. x \<in> set steps \<Longrightarrow> g x d = g' x d"
  shows "step_fold g steps lbls pri pos nxt onxt iB = 
         step_fold g' steps' lbls' pri' pos' nxt' onxt' iB'"
unfolding step_fold_def
by (auto simp: assms cong: step_fold'_cong)

fun step_foldL_step where
  "step_foldL_step _ _ _ [] (pos, nxt, lbls, es, is) = (pos, nxt, lbls, es, is)"
| "step_foldL_step g pri onxt (s#steps) (pos, nxt, lbls, es, is) = (
     let (pos', nxt', lbls', ss') = step_fold' g steps lbls pri pos nxt onxt False in 
     let (s', nxt'', lbls'') = g s (lbls',pri,pos',nxt',onxt,True) in
     let rs = butlast s'; s'' = last s' in
     (pos' + length rs, nxt, lbls'', es@ss'@rs, s''#is))"

definition step_foldL where
  "step_foldL g stepss lbls pri pos nxt onxt = 
     foldr (step_foldL_step g pri onxt) stepss (pos,nxt,lbls,[],[])"

lemma step_foldL_step_cong:
  assumes "pri = pri'"
  and "onxt = onxt'"
  and "s = s'"
  and "d = d'"
  and "\<And>x d. x \<in> set s \<Longrightarrow> g x d = g' x d"
  shows "step_foldL_step g pri onxt s d = step_foldL_step g' pri' onxt' s' d'"
using assms
by (cases d', cases s') (simp_all cong: step_fold'_cong)
  
lemma step_foldL_cong[fundef_cong]:
  assumes "lbls = lbls'"
  and "pri = pri'"
  and "pos = pos'"
  and "stepss = stepss'"
  and "nxt = nxt'"
  and "onxt = onxt'"
  and "\<And>x x' d. x \<in> set stepss \<Longrightarrow> x' \<in> set x \<Longrightarrow> g x' d = g' x' d"
  shows "step_foldL g stepss lbls pri pos nxt onxt = 
         step_foldL g' stepss' lbls' pri' pos' nxt' onxt'"
unfolding step_foldL_def
using assms
apply (cases stepss')
  apply simp
  apply (force intro!: foldr_cong step_foldL_step_cong)
done

subsection \<open>Starting processes\<close>
definition modProcArg 
  :: "(procArg * integer) \<Rightarrow> String.literal * variable" 
where
  "modProcArg x = (
     case x of 
       (ProcArg ty name, val) \<Rightarrow> if varType_inv ty 
                                then let init = checkVarValue ty val 
                                     in (name, Var ty init)
                                else abortv STR ''Invalid proc arg (varType_inv failed)'' 
                                            name (\<lambda>_. (name, Var VTChan 0)))"

definition emptyProc :: "pState"
  \<comment> \<open>The empty process.\<close>
where
  "emptyProc = \<lparr>pid = 0, vars = lm.empty (), pc = 0, channels = [], idx = 0 \<rparr>"

lemma vardict_inv_empty:
  "vardict_inv ss proc (lm.empty())"
unfolding vardict_inv_def
by (simp add: lm.correct)

lemma emptyProc_cl_inv[simp]:
  "cl_inv (g, emptyProc)"
by (simp add: cl_inv_def emptyProc_def)

lemma emptyProc_pState_inv:
  assumes "program_inv prog"
  shows "pState_inv prog emptyProc"
proof -
  from assms have "IArray.length (states prog !! 0) > 0"
    by (intro program_inv_length_states) (auto simp add: program_inv_def)
  with assms show ?thesis
    unfolding pState_inv_def program_inv_def emptyProc_def
    by (auto simp add: vardict_inv_empty)
qed

fun mkProc 
  :: "'a gState_scheme \<Rightarrow> pState
    \<Rightarrow> String.literal \<Rightarrow> expr list \<Rightarrow> process \<Rightarrow> nat 
    \<Rightarrow> 'a gState_scheme * pState" 
where
  "mkProc g p name args (sidx, start, argDecls, decls) pidN = (
     let start = case start of 
                   Index x \<Rightarrow> x
                 | _ \<Rightarrow> abortv STR ''Process start is not index: '' name (\<lambda>_. 0) 
     in
      \<comment> \<open>sanity check\<close>
      if length args \<noteq> length argDecls 
      then abortv STR ''Signature mismatch: '' name (\<lambda>_. (g,emptyProc))
      else
        let
          \<comment> \<open>evaluate args (in the context of the calling process)\<close>
          eArgs = map (exprArith g p) args;
        
          \<comment> \<open>replace the init part of \<open>argDecls\<close>\<close>
          argVars = map modProcArg (zip argDecls eArgs);
        
          \<comment> \<open>add \<open>_pid\<close> to vars\<close>
          pidI = integer_of_nat pidN;
          argVars = (STR ''_pid'', Var (VTBounded 0 pidI) pidI)#argVars;
          argVars = lm.to_map argVars;
        
          \<comment> \<open>our new process\<close>
          p = \<lparr> pid = pidN, vars = argVars, pc = start, channels = [], idx = sidx \<rparr>
        in
          \<comment> \<open>apply the declarations\<close>
          foldl (\<lambda>(g,p) d. mkVarChannel d (apsnd \<circ> pState.vars_update) g p) 
                (g,p) 
                decls)"

lemma mkProc_gState_progress_rel:
  assumes "gState_inv prog g"
  shows "(g, fst (mkProc g p name args (processes prog !! sidx) pidN)) \<in>  
          gState_progress_rel prog"
proof -
  obtain sidx' start argDecls decls  where 
    p: "processes prog !! sidx = (sidx', start, argDecls, decls)"
    by (metis prod.exhaust)

  from assms have 
    "\<And>p. (g, fst (foldl (\<lambda>(g,p) d. mkVarChannel d (apsnd \<circ> pState.vars_update) g p) 
                         (g,p) decls))
          \<in> gState_progress_rel prog"
  proof (induction decls arbitrary: g p)
    case (Cons d decls)
    obtain g' p' where 
      new: "(g',p') = (mkVarChannel d (apsnd \<circ> pState.vars_update) g p)" 
      by (metis prod.exhaust)
    hence "g' = fst ..." by (metis fst_conv)
    with Cons.prems have g_g': "(g,g') \<in> gState_progress_rel prog" 
      by (auto intro: mkVarChannel_gState_progress_rel)
    also note Cons.IH[OF g_g'[THEN gState_progress_rel_gState_invI2], of p']
    finally show ?case by (auto simp add: o_def new)
  qed simp
  thus ?thesis using assms p by auto
qed

lemmas mkProc_gState_inv = 
  mkProc_gState_progress_rel[THEN gState_progress_rel_gState_invI2]

lemma mkProc_pState_inv:
  assumes "program_inv prog"
  and "gState_inv prog g"
  and "pidN \<le> max_procs" and "pidN > 0"
  and "sidx < IArray.length (processes prog)"
  and "fst (processes prog !! sidx) = sidx"
  shows "pState_inv prog (snd (mkProc g p name args (processes prog !! sidx) pidN))"
proof -
  obtain sidx' start argDecls decls  where 
    "processes prog !! sidx = (sidx', start, argDecls, decls)"
    by (metis prod.exhaust)
  with assms have 
    p_def: "processes prog !! sidx = (sidx, start, argDecls, decls)" 
           "IArray.list_of (processes prog) ! sidx = (sidx, start, argDecls, decls)" 
    by simp_all
  with assms have "(sidx,start,argDecls,decls) \<in> set (IArray.list_of (processes prog))" 
    by (force dest: nth_mem)
  
  with assms obtain s where s: "start = Index s" "s < IArray.length (states prog !! sidx)"
    unfolding program_inv_def by auto
  
  hence P_inv: "pState_inv prog \<lparr>
                   pid = pidN,
                   vars = lm.to_map
                          ((STR ''_pid'', Var (VTBounded 0 (integer_of_nat pidN)) 
                             (integer_of_nat pidN)) 
                          # map modProcArg (zip argDecls (map (exprArith g p) args))),
                   pc = s, channels = [], idx = sidx\<rparr>"
    unfolding pState_inv_def
    using assms[unfolded program_inv_def]
    including integer.lifting
    apply (simp add: p_def)
    apply (intro lm_to_map_vardict_inv)
    apply auto
              apply (simp add: max_procs_def max_var_value_def)
              apply transfer'
              apply simp
            apply transfer'
            apply simp
          apply (simp add: min_var_value_def)
          apply transfer'
          apply simp
        apply (simp add: max_var_value_def max_procs_def)
        apply transfer'
        apply simp
      apply (drule set_zip_leftD)
      apply (force simp add: modProcArg_def 
                   split: procArg.splits if_splits 
                   intro!: image_eqI)
    apply (clarsimp simp add: modProcArg_def 
                    split: procArg.splits if_splits 
                    simp del: variable_inv.simps)
    apply (intro checkVarValue_Var)
    apply assumption
    done

  from p_def have 
    "varDeclName ` set decls \<subseteq> 
      process_names (states prog !! sidx) (processes prog !! sidx)" 
    by auto
  with \<open>gState_inv prog g\<close> have 
    F_inv: "\<And>p. \<lbrakk> pState_inv prog p; sidx = pState.idx p; cl_inv (g,p) \<rbrakk>
                \<Longrightarrow> pState_inv prog 
                   (snd (foldl (\<lambda>(g,p) d. mkVarChannel d (apsnd \<circ> pState.vars_update) g p) 
                               (g,p) decls))"
  proof (induction decls arbitrary: g p)
    case (Cons d ds) hence 
      decl: "varDeclName d \<in> process_names (states prog !! pState.idx p) 
                                           (processes prog !! pState.idx p)" 
      by simp
    
    obtain g' p' where 
      new: "(g',p') = (mkVarChannel d (apsnd \<circ> pState.vars_update) g p)" 
      by (metis prod.exhaust)
    hence p': "p' = snd ..." and g': "g' = fst ..." 
      by (metis snd_conv fst_conv)+
    with Cons.prems have "pState_inv prog p'" 
      apply (auto intro!: mkVarChannel_pState_inv)
      apply (simp add: pState_inv_def)
      apply (intro vardict_inv_updateI)
          apply simp
        apply (cases d)
          apply (force dest!: toVariable_name)
        apply (force dest!: toVariable_name)
      apply (intro toVariable_variable_inv')
        apply assumption+
      done
    moreover 
    from p' Cons.prems have "pState.idx p' = sidx" 
      by (auto simp add: mkVarChannel_def mkChannels_def split: prod.split)
    moreover 
    from new Cons.prems have "cl_inv (g',p')" 
      by (auto intro!: mkVarChannel_cl_inv)
    moreover 
    from g' Cons.prems have "gState_inv prog g'" 
      by (auto intro!: mkVarChannel_gState_inv)
    moreover 
    from Cons.prems have 
      "varDeclName ` set ds \<subseteq>
          process_names (states prog !! sidx) (processes prog !! sidx)" 
      by simp
    ultimately 
    have 
      "pState_inv prog 
         (snd (foldl (\<lambda>(g,p) d. mkVarChannel d (apsnd \<circ> pState.vars_update) g p) 
                     (g',p') ds))"
      using Cons.IH[of p' g'] by (simp add: o_def)
    with new show ?case by (simp add: o_def)
  qed simp

  show ?thesis 
    by (auto simp add: p_def s cl_inv_def 
             intro: F_inv[OF P_inv]) 
       (blast intro: emptyProc_pState_inv assms)
qed

lemma mkProc_cl_inv:
  assumes "cl_inv (g,p)"
  shows "cl_inv (mkProc g p name args (processes prog !! sidx) pidN)"
proof -
  note IArray.sub_def [simp del]
  obtain sidx' start argDecls decls  
    where [simp]: "processes prog !! sidx = (sidx', start, argDecls, decls)"
    by (metis prod.exhaust)

  have 
    P_inv: "\<And>s v. cl_inv (g, \<lparr>pid = pidN, vars = v, pc = s, channels = [], idx = sidx' \<rparr>)" 
    by (simp add: cl_inv_def)
  
  have 
    "\<And>p. cl_inv(g,p) \<Longrightarrow> 
         cl_inv (foldl (\<lambda>(g,p) d. mkVarChannel d (apsnd \<circ> pState.vars_update) g p) 
                       (g,p) decls)"
  proof (induction decls arbitrary: g p)
    case (Cons d ds)
    obtain g' p' where 
      new: "(g',p') = (mkVarChannel d (apsnd \<circ> pState.vars_update) g p)" 
      by (metis prod.exhaust)
    with Cons.prems have "cl_inv (g',p')"
      by (auto intro!: mkVarChannel_cl_inv)
    
    from Cons.IH[OF this] new show ?case by (simp add: o_def)
  qed simp
  
  from this[OF P_inv] show ?thesis by auto
qed

declare mkProc.simps[simp del]

definition runProc 
  :: "String.literal \<Rightarrow> expr list \<Rightarrow> program 
      \<Rightarrow> 'a gState_scheme \<Rightarrow> pState 
      \<Rightarrow> 'a gState_scheme * pState" 
where
  "runProc name args prog g p = (
     if length (procs g) \<ge> max_procs 
     then abort STR ''Too many processes'' (\<lambda>_. (g,p))
     else let pid = length (procs g) + 1 in
          case lm.lookup name (proc_data prog) of 
            None \<Rightarrow> abortv STR ''No such process: '' name 
                          (\<lambda>_. (g,p))
          | Some proc_idx \<Rightarrow> 
               let (g', proc) = mkProc g p name args (processes prog !! proc_idx) pid
               in (g'\<lparr>procs := procs g @ [proc]\<rparr>, p))"

lemma runProc_gState_progress_rel:
  assumes "program_inv prog"
  and "gState_inv prog g"
  and "pState_inv prog p"
  and "cl_inv (g,p)"
  shows "(g, fst (runProc name args prog g p)) \<in> gState_progress_rel prog"
proof (cases "length (procs g) < max_procs")
  note IArray.sub_def [simp del]

  case True thus ?thesis
  proof (cases "lm.lookup name (proc_data prog)")
    case (Some proc_idx)
    hence *: "proc_idx < IArray.length (processes prog)" 
             "fst (processes prog !! proc_idx) = proc_idx"
      using assms 
      by (simp_all add: lm.correct program_inv_def)
      
    obtain g' p' where 
      new: "(g',p') = mkProc g p name args (processes prog !! proc_idx) (length (procs g) + 1)"
      by (metis prod.exhaust)
    hence g': "g' = fst ..." and p': "p' = snd ..." 
      by (metis snd_conv fst_conv)+
    from assms g' have "(g, g') \<in> gState_progress_rel prog " 
      by (auto intro!: mkProc_gState_progress_rel)

    moreover 
    from * assms True p' have "pState_inv prog p'" 
      by (auto intro!: mkProc_pState_inv)
    moreover 
    from assms new have "cl_inv (g',p')" 
      by (auto intro!: mkProc_cl_inv)
    ultimately show ?thesis
      using True Some new assms
      unfolding runProc_def gState_progress_rel_def
      by (clarsimp split: prod.split) 
         (auto simp add: gState_inv_def cl_inv_def)
  next
    case None with assms show ?thesis by (auto simp add: runProc_def)
  qed
next
  case False with assms show ?thesis by (auto simp add: runProc_def)
qed

lemmas runProc_gState_inv = 
  runProc_gState_progress_rel[THEN gState_progress_rel_gState_invI2]

lemma runProc_pState_id:
  "snd (runProc name args prog g p) = p"
unfolding runProc_def
by (auto split: if_splits split: option.split prod.split)

lemma runProc_pState_inv:
  assumes "pState_inv prog p"
  shows "pState_inv prog (snd (runProc name args prog g p))"
by (simp add: assms runProc_pState_id)

lemma runProc_cl_inv:
  assumes "program_inv prog"
  and "gState_inv prog g"
  and "pState_inv prog p"
  and "cl_inv (g,p)"
  shows "cl_inv (runProc name args prog g p)"
proof -
  obtain g' p' where *: "runProc name args prog g p = (g',p')" 
    by (metis prod.exhaust)
  with runProc_gState_progress_rel[OF assms, of name args] have 
    "length (channels g) \<le> length (channels g')" 
    by (simp add: gState_progress_rel_def)
  moreover from * runProc_pState_id have "p' = p" by (metis snd_conv)
  ultimately show ?thesis by (metis \<open>cl_inv (g,p)\<close> * cl_inv_trans)
qed

subsection \<open>AST to edges\<close>

type_synonym ast = "AST.module list"

text \<open>In this section, the AST is translated into the transition system.\<close>

text \<open>
  Handling atomic blocks is non-trivial. Therefore, we do this in an extra pass:
  @{term lp} and @{term hp} are the positions of the start and the end of
  the atomic block. Every edge pointing into this range is therefore marked as 
  @{term Atomic}. If they are pointing somewhere else, they are set to @{term InAtomic},
  meaning: they start \emph{in} an atomic block, but leave it afterwards.
\<close>
definition atomize :: "nat \<Rightarrow> nat \<Rightarrow> edge list \<Rightarrow> edge list" where
  "atomize lp hp es = fold (\<lambda>e es. 
     let e' = case target e of
                 LabelJump _ None \<Rightarrow> 
                    \<comment> \<open>Labels are checked again later on, when they\<close>
                    \<comment> \<open>are going to be resolved. Hence it is safe to say\<close>
                    \<comment> \<open>\<open>atomic\<close> here, especially as the later algorithm\<close>
                    \<comment> \<open>relies on targets in atomic blocks to be marked as such.\<close>
                    e\<lparr> atomic := InAtomic \<rparr>
                | LabelJump _ (Some via) \<Rightarrow> 
                    if lp \<le> via \<and> hp \<ge> via then e\<lparr> atomic := Atomic \<rparr> 
                    else e\<lparr> atomic := InAtomic \<rparr>
                | Index p' \<Rightarrow> 
                    if lp \<le> p' \<and> hp \<ge> p' then e\<lparr> atomic := Atomic \<rparr>
                    else e\<lparr> atomic := InAtomic \<rparr>
      in e'#es) es []"

fun skip \<comment> \<open>No-(edge)\<close>
where 
  "skip (lbls, pri, pos, nxt, _) = 
  ([[\<lparr>cond = ECExpr (ExprConst 1), 
       effect = EEId, target = nxt, prio = pri, 
       atomic = NonAtomic\<rparr>]], Index pos, lbls)"

text \<open>
   The AST is walked backwards. This allows to know the next state directly.

   Parameters used:
   \begin{description}
      \item[lbls] Map of Labels
      \item[pri] Current priority
      \item[pos] Current position in the array
      \item[nxt] Next state
      \item[onxt] Previous 'next state' (where to jump after a 'do')
      \item[inBlock] Needed for certain constructs to calculate the layout of the array
   \end{description}
\<close>

fun stepToState 
  :: "step 
      \<Rightarrow> (labels * integer * nat * edgeIndex * edgeIndex option * bool) 
      \<Rightarrow> edge list list * edgeIndex * labels"
and stmntToState 
  :: "stmnt 
      \<Rightarrow> (labels * integer * nat * edgeIndex * edgeIndex option * bool) 
      \<Rightarrow> edge list list * edgeIndex * labels"
where
  "stepToState (StepStmnt s None) data = stmntToState s data"
| "stepToState (StepStmnt s (Some u)) (lbls, pri, pos, nxt, onxt, _) = (
     let
        \<comment> \<open>the \<open>unless\<close> part\<close>
        (ues,_,lbls') = stmntToState u (lbls, pri, pos, nxt, onxt, True);
        u = last ues; ues = butlast ues;
        pos' = pos + length ues;
    
        \<comment> \<open>find minimal current priority\<close>
        pri = min_prio u pri;

        \<comment> \<open>the guarded part --\<close>
        \<comment> \<open>priority is decreased, because there is now a new unless part with\<close>
        \<comment> \<open>higher prio\<close>
        (ses,spos,lbls'') = stmntToState s (lbls', pri - 1, pos', nxt, onxt, False);
 
        \<comment> \<open>add an edge to the unless part for each generated state\<close>
        ses = map (List.append u) ses
     in
        (ues@ses,spos,lbls''))"

| "stepToState (StepDecl decls) (lbls, pri, pos, nxt, onxt, _) = ( 
     let edgeF = \<lambda>d (lbls,pri,pos,nxt,_). 
        ([[\<lparr>cond = ECTrue, effect = EEDecl d, target = nxt, 
             prio = pri, atomic = NonAtomic\<rparr>]], Index pos, lbls)
     in 
        step_fold edgeF decls lbls pri pos nxt onxt False)"

| "stepToState StepSkip (lbls,_,_,nxt,_) = ([],nxt,lbls)"

| "stmntToState (StmntAtomic steps) (lbls, pri, pos, nxt, onxt, inBlock) = (
    let (es,pos',lbls') = step_fold stepToState steps lbls pri pos nxt onxt inBlock in
    let es' = map (atomize pos (pos + length es)) es in
    (es', pos', lbls'))"

| "stmntToState (StmntLabeled l s) (lbls, pri, pos, d) = (
     let 
         (es, pos', lbls) = stmntToState s (lbls, pri, pos, d);
         
         \<comment> \<open>We don't resolve goto-chains. If the labeled stmnt returns only a jump,\<close>
         \<comment> \<open>use this goto state.\<close>
         lpos = case pos' of Index p \<Rightarrow> p | _ \<Rightarrow> pos;
         lbls' = add_label l lbls lpos
     in
       (es, pos', lbls'))"

| "stmntToState (StmntDo stepss) (lbls, pri, pos, nxt, onxt, inBlock) = (
    let
       \<comment> \<open>construct the different branches\<close>
       \<comment> \<open>\<open>nxt\<close> in those branches points current pos (it is a loop after all)\<close>
       \<comment> \<open>\<open>onxt\<close> then is the current \<open>nxt\<close> (needed for break, f.ex.)\<close>
       (_,_,lbls,es,is) = step_foldL stepToState stepss lbls pri 
                                     (pos+1) (Index pos) (Some nxt);

       \<comment> \<open>put the branch starting points (\<open>is\<close>) into the array\<close>
       es' = concat is # es
    in
      if inBlock then 
           \<comment> \<open>inside another DO or IF or UNLESS\<close>
           \<comment> \<open>\<open>\<longrightarrow>\<close> append branches again, so they can be consumed\<close>
           (es' @ [concat is], Index pos, lbls)
      else 
          (es', Index pos, lbls)
   )"

| "stmntToState (StmntIf stepss) (lbls, pri, pos, nxt, onxt, _) = (
     let (pos,_,lbls,es,is) = step_foldL stepToState stepss lbls pri pos nxt onxt 
     in (es @ [concat is], Index pos, lbls))"

| "stmntToState (StmntSeq steps) (lbls, pri, pos, nxt, onxt, inBlock) = 
     step_fold stepToState steps lbls pri pos nxt onxt inBlock"


| "stmntToState (StmntAssign v e) (lbls, pri, pos, nxt, _) = 
   ([[\<lparr>cond = ECTrue, effect = EEAssign v e, target = nxt, prio = pri, 
        atomic = NonAtomic\<rparr>]], Index pos, lbls)"

| "stmntToState (StmntAssert e) (lbls, pri, pos, nxt, _) =
   ([[\<lparr>cond = ECTrue, effect = EEAssert e, target = nxt, prio = pri, 
        atomic = NonAtomic\<rparr>]], Index pos, lbls)"

| "stmntToState (StmntCond e) (lbls, pri, pos, nxt, _) = 
   ([[\<lparr>cond = ECExpr e, effect = EEId, target = nxt, prio = pri, 
        atomic = NonAtomic\<rparr>]], Index pos, lbls)"

| "stmntToState StmntElse (lbls, pri, pos, nxt, _) =
   ([[\<lparr>cond = ECElse, effect = EEId, target = nxt, prio = pri, 
        atomic = NonAtomic \<rparr>]], Index pos, lbls)"

| "stmntToState StmntBreak (lbls,pri,_,_,Some onxt,_) = 
   ([[\<lparr>cond = ECTrue, effect = EEGoto, target = onxt, prio = pri, 
        atomic = NonAtomic \<rparr>]], onxt, lbls)"
| "stmntToState StmntBreak (_,_,_,_,None,_) = 
   abort STR ''Misplaced break'' (\<lambda>_. ([],Index 0,lm.empty()))"

| "stmntToState (StmntRun n args) (lbls, pri, pos, nxt, onxt, _) =
   ([[\<lparr>cond = ECRun n, effect = EERun n args, target = nxt, prio = pri, 
        atomic = NonAtomic \<rparr>]], Index pos,lbls)"

| "stmntToState (StmntGoTo l) (lbls, pri, pos, _) = 
   ([[\<lparr>cond = ECTrue, effect = EEGoto, target = LabelJump l None, prio = pri, 
        atomic = NonAtomic \<rparr>]], LabelJump l (Some pos), lbls)"

| "stmntToState (StmntSend v e srt) (lbls, pri, pos, nxt, _) =
   ([[\<lparr>cond = ECSend v, effect = EESend v e srt, target = nxt, prio = pri, 
        atomic = NonAtomic \<rparr>]], Index pos, lbls)"

| "stmntToState (StmntRecv v r srt rem) (lbls, pri, pos, nxt, _) =
   ([[\<lparr>cond = ECRecv v r srt, effect = EERecv v r srt rem, target = nxt, prio = pri, 
        atomic = NonAtomic \<rparr>]], Index pos, lbls)"

| "stmntToState StmntSkip d = skip d"

subsubsection \<open>Setup\<close>
definition endState :: "edge list" where
  \<comment> \<open>An extra state added to each process marking its end.\<close>
  "endState = [\<lparr> cond = ECFalse, effect = EEEnd, target = Index 0, prio = 0, 
                  atomic = NonAtomic\<rparr>]"

definition resolveLabel :: "String.literal \<Rightarrow> labels \<Rightarrow> nat" where
  "resolveLabel l lbls = (
     case lm.lookup l lbls of 
       None \<Rightarrow> abortv STR ''Unresolved label: '' l (\<lambda>_. 0)
     | Some pos \<Rightarrow> pos)"

primrec resolveLabels :: "edge list list \<Rightarrow> labels \<Rightarrow> edge list \<Rightarrow> edge list" where
  "resolveLabels _ _ [] = []"
| "resolveLabels edges lbls (e#es) = (
    let check_atomic = \<lambda>pos. fold (\<lambda>e a. a \<and> inAtomic e) (edges ! pos) True in
    case target e of 
      Index _ \<Rightarrow> e 
    | LabelJump l None \<Rightarrow> 
         let pos = resolveLabel l lbls in
           e\<lparr>target := Index pos, 
              atomic := if inAtomic e then
                           if check_atomic pos then Atomic 
                           else InAtomic
                        else NonAtomic \<rparr>
     | LabelJump l (Some via) \<Rightarrow> 
          let pos = resolveLabel l lbls in
            e\<lparr>target := Index pos,
               \<comment> \<open>NB: \<open>isAtomic\<close> instead of \<open>inAtomic\<close>, cf \<open>atomize()\<close>\<close>
               atomic := if isAtomic e then
                            if check_atomic pos \<and> check_atomic via then Atomic
                            else InAtomic
                         else atomic e \<rparr>
   ) # (resolveLabels edges lbls es)"

definition calculatePrios :: "edge list list \<Rightarrow> (integer * edge list) list" where
  "calculatePrios ess = map (\<lambda>es. (min_prio es 0, es)) ess"

definition toStates :: "step list \<Rightarrow> states * edgeIndex * labels" where
  "toStates steps = (
    let 
       (states,pos,lbls) = step_fold stepToState steps (lm.empty()) 
                                     0 1 (Index 0) None False;
       pos = (case pos of 
                Index _ \<Rightarrow> pos 
              | LabelJump l _ \<Rightarrow> Index (resolveLabel l lbls));
       states = endState # states;
       states = map (resolveLabels states lbls) states;
       states = calculatePrios states
    in
    case pos of Index s \<Rightarrow> 
          if s < length states then (IArray states, pos, lbls)
          else abort STR ''Start index out of bounds'' (\<lambda>_. (IArray states, Index 0, lbls)))"

lemma toStates_inv:
  assumes "toStates steps = (ss,start,lbls)"
  shows "\<exists>s. start = Index s \<and> s < IArray.length ss"
    and "IArray.length ss > 0"
  using assms
  unfolding toStates_def calculatePrios_def
  by (auto split: prod.splits edgeIndex.splits if_splits)

(* returns: states * is_active * name * labels * process *)
primrec toProcess 
  :: "nat \<Rightarrow> proc \<Rightarrow> states * nat * String.literal * (labels * process)"
 where
  "toProcess sidx (ProcType act name args decls steps) = (
     let
       (states, start, lbls) = toStates steps;
       act = (case act of 
                None \<Rightarrow> 0 
              | Some None \<Rightarrow> 1 
              | Some (Some x) \<Rightarrow> nat_of_integer x)
     in
        (states, act, name, lbls, sidx, start, args, decls))"
| "toProcess sidx (Init decls steps) = (
      let (states, start, lbls) = toStates steps in 
      (states, 1, STR '':init:'', lbls, sidx, start, [], decls))"

lemma toProcess_sidx:
  "toProcess sidx p = (ss,a,n,l,idx,r) \<Longrightarrow> idx = sidx"
by (cases p) (simp_all split: prod.splits)

lemma toProcess_states_nonempty:
  "toProcess sidx p = (ss,a,n,l,idx,r) \<Longrightarrow> IArray.length ss > 0"
by (cases p) (force split: prod.splits dest: toStates_inv(2))+

lemma toProcess_start:
  "toProcess sidx p = (ss,a,n,l,idx,start,r) 
   \<Longrightarrow> \<exists>s. start = Index s \<and> s < IArray.length ss"
by (cases p) (force split: prod.splits dest: toStates_inv(1))+


lemma toProcess_startE:
  assumes "toProcess sidx p = (ss,a,n,l,idx,start,r)"
  obtains s where "start = Index s" "s < IArray.length ss"
  using toProcess_start[OF assms]
  by blast

text \<open>
  The main construction function. Takes an AST 
  and returns  an initial state, 
  and the program (= transition system).
\<close>

definition setUp :: "ast \<Rightarrow> program \<times> gState" where
  "setUp ast = (
      let
       (decls, procs, _) = preprocess ast;
       assertVar = Var (VTBounded 0 1) 0;
 
       pre_procs = map (case_prod toProcess) (List.enumerate 1 procs);

       procs = IArray ((0, Index 0, [], []) # map (\<lambda>(_,_,_,_,p). p) pre_procs);
       labels = IArray (lm.empty() # map (\<lambda>(_,_,_,l,_). l) pre_procs);
       states = IArray (IArray [(0,[])] # map (\<lambda>(s,_). s) pre_procs);
       names = IArray (STR ''invalid'' # map (\<lambda>(_,_,n,_). n) pre_procs);

       proc_data = lm.to_map (map (\<lambda>(_,_,n,_,idx,_). (n,idx)) pre_procs);
       
       prog = \<lparr> processes = procs, labels = labels, states = states, 
                 proc_names = names, proc_data = proc_data \<rparr>;
     
       g = \<lparr> vars = lm.sng (STR ''__assert__'') assertVar, 
              channels = [InvChannel], timeout = False, procs = [] \<rparr>;
       g' = foldl (\<lambda>g d. 
                    fst (mkVarChannel d (apfst \<circ> gState.vars_update) g emptyProc)
                  ) g decls;
       g'' = foldl (\<lambda>g (_,a,name,_). 
                    foldl (\<lambda>g name. 
                              fst (runProc name [] prog g emptyProc)
                          ) g (replicate a name)
                   ) g' pre_procs
      in
       (prog, g''))"

lemma setUp_program_inv':
  "program_inv (fst (setUp ast))"
proof (rule program_invI, goal_cases)
  case 1 show ?case by (simp add: setUp_def split: prod.split)
next
  case 2 show ?case by (simp add: setUp_def split: prod.split)
next
  case 3 thus ?case
    by (auto simp add: setUp_def o_def  
             split: prod.splits 
             dest!: toProcess_states_nonempty)
next
  case 4 thus ?case
    unfolding setUp_def
    by (auto simp add: lm.correct o_def in_set_enumerate_eq nth_enumerate_eq 
            dest!: subsetD[OF Misc.ran_map_of] toProcess_sidx 
            split: prod.splits)
  (* TODO: Change name Misc.ran_map_of \<longrightarrow> ran_map_of_ss, as it collides 
      with AList.ran_map_of *)
next
  case 5 thus ?case
    apply (auto simp add: setUp_def o_def split: prod.splits)
    apply (frule toProcess_sidx)
    apply (frule toProcess_start)
    apply (auto simp: in_set_enumerate_eq nth_enumerate_eq)
    done
qed

lemma setUp_program_inv:
  assumes "setUp ast = (prog,g)"
  shows "program_inv prog"
using assms setUp_program_inv' 
by (metis fst_conv)

lemma setUp_gState_inv:
  assumes "setUp ast = (prog, g)"
  shows "gState_inv prog g"
proof -
  from assms have p_INV: "program_inv prog" by (fact setUp_program_inv)

  {
    fix prog :: program
    assume *: "program_inv prog"
    let ?g = "\<lparr> vars = lm.sng (STR ''__assert__'') (Var (VTBounded 0 1) 0), 
                 channels = [InvChannel], timeout = False, procs = [] \<rparr>"

    have g1: "gState_inv prog ?g"
      by (simp add: gState_inv_def max_channels_def lm_correct max_var_value_def)
    {
      fix g decls
      assume "gState_inv prog g"
      hence "gState_inv prog (foldl (\<lambda>g d.  
                   fst (mkVarChannel d (apfst \<circ> gState.vars_update) g emptyProc)
                  ) g decls)"
        apply (rule foldl_rule)
        apply (intro mkVarChannel_gState_inv)
          apply simp
        apply (frule_tac g=\<sigma> in toVariable_variable_inv')
          apply assumption
        apply (auto simp add: gState_inv_def lm.correct)
        done
    }
    note g2 = this[OF g1]

    {
      fix g :: "'a gState_scheme" and pre_procs
      assume "gState_inv prog g"
      hence "gState_inv prog (foldl (\<lambda>g (_,a,name,_). 
                 foldl (\<lambda>g name. 
                         fst (runProc name [] prog g emptyProc)
                       ) g (replicate a name)
              ) g pre_procs)"
        apply (rule foldl_rule)
        apply (clarsimp split: prod.splits)
        apply (rule foldl_rule)
          apply (auto intro!: runProc_gState_inv emptyProc_pState_inv *)
        done
    }
    note this[OF g2]
  } note g_INV = this

  from assms p_INV show ?thesis
    unfolding setUp_def
    by (auto split: prod.splits intro!: g_INV)
qed


subsection \<open>Semantic Engine\<close>

text \<open>
  After constructing the transition system, we are missing the final part:
  The successor function on this system. We use SPIN-nomenclature and call it
  \emph{semantic engine}.
\<close>

definition "assertVar \<equiv> VarRef True (STR ''__assert__'') None"

subsubsection \<open>Evaluation of Edges\<close>

fun evalRecvArgs 
  :: "recvArg list \<Rightarrow> integer list \<Rightarrow> gState\<^sub>I \<Rightarrow> pState \<Rightarrow> gState\<^sub>I * pState"
where
  "evalRecvArgs [] [] g l = (g,l)"
| "evalRecvArgs _  [] g l = 
     abort STR ''Length mismatch on receiving.'' (\<lambda>_. (g,l))"
| "evalRecvArgs []  _ g l = 
     abort STR ''Length mismatch on receiving.'' (\<lambda>_. (g,l))"
| "evalRecvArgs (r#rs) (v#vs) g l = (
     let (g,l) =
       case r of 
          RecvArgVar var \<Rightarrow> setVar var v g l
        | _ \<Rightarrow> (g,l)
     in evalRecvArgs rs vs g l)"

primrec evalCond 
  :: "edgeCond \<Rightarrow> gState\<^sub>I \<Rightarrow> pState \<Rightarrow> bool"
where
  "evalCond ECTrue _ _ \<longleftrightarrow> True"
| "evalCond ECFalse _ _ \<longleftrightarrow> False"
| "evalCond (ECExpr e) g l \<longleftrightarrow> exprArith g l e \<noteq> 0"
| "evalCond (ECRun _) g l \<longleftrightarrow> length (procs g) < 255"
| "evalCond ECElse g l \<longleftrightarrow> gState\<^sub>I.else g"
| "evalCond (ECSend v) g l \<longleftrightarrow> 
     withChannel v (\<lambda>_ c.
       case c of 
         Channel cap _ q \<Rightarrow> integer_of_nat (length q) < cap 
       | HSChannel _ \<Rightarrow> True) g l"
| "evalCond (ECRecv v rs srt) g l \<longleftrightarrow> 
     withChannel v (\<lambda>i c. 
       case c of
         HSChannel _ \<Rightarrow> handshake g \<noteq> 0 \<and> recvArgsCheck g l rs (hsdata g)
       | _ \<Rightarrow> pollCheck g l c rs srt) g l"

fun evalHandshake 
  :: "edgeCond \<Rightarrow> nat \<Rightarrow>  gState\<^sub>I \<Rightarrow> pState \<Rightarrow> bool"
where
  "evalHandshake (ECRecv v _ _) h g l 
    \<longleftrightarrow> h = 0 
     \<or> withChannel v (\<lambda>i c. case c of 
                             HSChannel _ \<Rightarrow> i = h 
                           | Channel _ _ _ \<Rightarrow> False) g l"
| "evalHandshake _ h _ _ \<longleftrightarrow> h = 0"

primrec evalEffect 
  :: "edgeEffect \<Rightarrow> program \<Rightarrow> gState\<^sub>I \<Rightarrow> pState \<Rightarrow> gState\<^sub>I * pState"
where
  "evalEffect EEEnd _ g l = (g,l)"
| "evalEffect EEId _ g l = (g,l)"
| "evalEffect EEGoto _ g l = (g,l)"
| "evalEffect (EEAssign v e) _ g l = setVar v (exprArith g l e) g l"
| "evalEffect (EEDecl d) _ g l = mkVarChannelProc d g l"
| "evalEffect (EERun name args) prog g l = runProc name args prog g l"
| "evalEffect (EEAssert e) _ g l = (
     if exprArith g l e = 0 
     then setVar assertVar 1 g l 
     else (g,l))"
| "evalEffect (EESend v es srt) _ g l = withChannel v (\<lambda>i c. 
     let 
       ab = \<lambda>_. abort STR ''Length mismatch on sending.'' (\<lambda>_. (g,l));
       es = map (exprArith g l) es
     in
       if \<not> for_all (\<lambda>x. x \<ge> min_var_value \<and> x \<le> max_var_value) es 
       then abort STR ''Invalid Channel'' (\<lambda>_. (g,l))
       else
          case c of 
            Channel cap ts q \<Rightarrow> 
              if length ts \<noteq> length es \<or> \<not> (length q < max_array_size) 
              then ab()
              else let
                     q' = if \<not> srt then q@[es]
                          else let
                            q = map lexlist q;
                            q' = insort (lexlist es) q
                          in map unlex q';
                     g = gState.channels_update (\<lambda>cs. 
                              cs[ i := Channel cap ts q' ]) g
                   in (g,l)
          | HSChannel ts \<Rightarrow>
              if length ts \<noteq> length es then ab()
              else (g\<lparr>hsdata := es, handshake := i\<rparr>, l)
          | InvChannel \<Rightarrow> abort STR ''Trying to send on invalid channel'' (\<lambda>_. (g,l))
    ) g l"
| "evalEffect (EERecv v rs srt rem) _ g l = withChannel v (\<lambda>i c. 
     case c of 
       Channel cap ts qs \<Rightarrow>
          if qs = [] then abort STR ''Recv from empty channel'' (\<lambda>_. (g,l))
          else
             let
               (q', qs') = if \<not> srt then (hd qs, tl qs)
                           else apfst the (find_remove (recvArgsCheck g l rs) qs);
               (g,l) = evalRecvArgs rs q' g l;
               g = if rem 
                   then gState.channels_update (\<lambda>cs. cs[ i := Channel cap ts qs']) g
                   else g
                     \<comment> \<open>messages are not removed -- so no need to update anything\<close>
             in (g,l)
      | HSChannel _ \<Rightarrow> 
             let (g,l) = evalRecvArgs rs (hsdata g) g l in
             let g = g\<lparr> handshake := 0, hsdata := [] \<rparr>
             in (g,l)
      | InvChannel \<Rightarrow> abort STR ''Receiving on invalid channel'' (\<lambda>_. (g,l))
   ) g l"

lemma statesDecls_effect:
  assumes "ef \<in> effect ` edgeSet ss"
  and "ef = EEDecl d"
  shows "d \<in> statesDecls ss"
proof -
  from assms obtain e where "e \<in> edgeSet ss" "ef = effect e" by auto
  thus ?thesis  using assms
    unfolding statesDecls_def
    by (auto simp add: edgeDecls_def 
             intro!: bexI[where x = e] 
             split: edgeEffect.split)
qed

lemma evalRecvArgs_pState_inv:
  assumes "pState_inv prog p"
  shows "pState_inv prog (snd (evalRecvArgs rargs xs g p))"
  using assms
proof (induction rargs xs arbitrary: p g rule: list_induct2')
  case (4 r rs x xs) thus ?case
  proof (cases r)
    case (RecvArgVar v)
    obtain g' p' where  new: "setVar v x g p = (g',p')" by (metis prod.exhaust)
    hence "p' = snd (setVar v x g p)" by simp
    with "4" have "pState_inv prog p'" by (auto intro!: setVar_pState_inv)
    from "4.IH"[OF this] RecvArgVar new show ?thesis by simp
  qed simp_all
qed simp_all

lemma evalRecvArgs_pState_inv':
  assumes "evalRecvArgs rargs xs g p = (g', p')"
  and "pState_inv prog p"
  shows "pState_inv prog p'"
using assms evalRecvArgs_pState_inv 
by (metis snd_conv)

lemma evalRecvArgs_gState_progress_rel:
  assumes "gState_inv prog g"
  shows "(g, fst (evalRecvArgs rargs xs g p)) \<in> gState_progress_rel prog"
  using assms
proof (induction rargs xs arbitrary: p g rule: list_induct2')
  case (4 r rs x xs) thus ?case
  proof (cases r)
    case (RecvArgVar v)
    obtain g' p' where new: "setVar v x g p = (g',p')" by (metis prod.exhaust)
    hence "g' = fst (setVar v x g p)" by simp
    with "4" have "(g, g') \<in> gState_progress_rel prog" 
      by (auto intro!: setVar_gState_progress_rel)
    also hence "gState_inv prog g'" 
      by (rule gState_progress_rel_gState_invI2)
    note "4.IH"[OF this, of p']
    finally show ?thesis using RecvArgVar new by simp
  qed simp_all
qed simp_all

lemmas evalRecvArgs_gState_inv = 
  evalRecvArgs_gState_progress_rel[THEN gState_progress_rel_gState_invI2]

lemma evalRecvArgs_cl_inv:
  assumes "cl_inv (g,p)"
  shows "cl_inv (evalRecvArgs rargs xs g p)"
  using assms
proof (induction rargs xs arbitrary: p g rule: list_induct2')
  case (4 r rs x xs) thus ?case
  proof (cases r)
    case (RecvArgVar v) 
    with 4 have "cl_inv (setVar v x g p)" 
      by (auto intro!: setVar_cl_inv)
    with "4.IH" RecvArgVar show ?thesis 
      by (auto split: prod.splits)
  qed simp_all
qed simp_all

lemma evalEffect_pState_inv:
  assumes "pState_inv prog p"
  and "gState_inv prog g"
  and "cl_inv (g,p)"
  and "e \<in> effect ` edgeSet (states prog !! pState.idx p)"
  shows "pState_inv prog (snd (evalEffect e prog g p))"
  using assms
proof (cases e)
  case (EEDecl d) 
  with assms have "d \<in> statesDecls (states prog !! pState.idx p)"
    using statesDecls_effect 
    by simp
  with assms EEDecl show ?thesis
    by (auto simp del: IArray.sub_def 
             intro!: mkVarChannelProc_pState_inv)
next
  case (EESend c es srt) 
  then obtain v where "ChanRef v = c" by (cases c) simp
  with EESend assms show ?thesis
    by (cases v) (auto simp add: withChannel'_def withVar'_def split: channel.split)
next
  case (EERecv c es srt) 
  then obtain v where "ChanRef v = c" by (cases c) simp
  with EERecv assms show ?thesis
    by (cases v)  
       (auto simp: withChannel'_def withVar'_def 
             split: prod.splits channel.split 
             dest: evalRecvArgs_pState_inv')
qed (clarsimp_all intro!: setVar_pState_inv runProc_pState_inv)

lemma evalEffect_gState_progress_rel:
  assumes "program_inv prog"
  and "gState_inv prog g"
  and "pState_inv prog p"
  and "cl_inv (g,p)"
  shows "(g, fst (evalEffect e prog g p)) \<in> gState_progress_rel prog"
using assms
proof (cases e)
  case EEAssert 
  with assms show ?thesis 
    by (auto intro: setVar_gState_progress_rel)
next
  case EEAssign 
  with assms show ?thesis 
    by (auto intro: setVar_gState_progress_rel)
next
  case EEDecl 
  with assms show ?thesis 
    by (auto intro: mkVarChannelProc_gState_progress_rel)
next
  case EERun 
  with assms show ?thesis 
    by (auto intro: runProc_gState_progress_rel)
next
  case (EESend c es srt) 
  then obtain v where v: "c = ChanRef v" by (metis chanRef.exhaust)
  obtain idx where idx: "nat_of_integer (the (getVar v g p)) = idx" by blast
  note idx' = idx[symmetric, unfolded getVar_def]
  show ?thesis
  proof (cases "idx < length (gState.channels g)")
    case True 
    note DEF = True EESend v idx' assms
    
    show ?thesis
    proof (cases "gState.channels g ! idx")
      case (Channel cap ts q) 
      with True have "Channel cap ts q \<in> set (gState.channels g)" 
        by (metis nth_mem)
      with assms have "channel_inv (Channel cap ts q)" 
        by (auto simp add: gState_inv_def simp del: channel_inv.simps)
      with Channel DEF show ?thesis
        by (cases v) 
           (auto simp add: withChannel'_def withVar'_def for_all_def
                 split: channel.split 
                 intro!: gState_progress_rel_channels_update)
    next
      case HSChannel with DEF show ?thesis 
        by (cases v) 
           (auto simp: withChannel'_def withVar'_def gState_progress_rel_def 
                       gState_inv_def
                split: channel.split)
    next
      case InvChannel with DEF show ?thesis 
        by (cases v) (auto simp add: withChannel'_def withVar'_def)
    qed
  next
    case False with EESend idx' v assms show ?thesis 
      by (cases v) (auto simp add: withChannel'_def withVar'_def)
  qed
next
  case (EERecv c rs srt rem) 
  then obtain v where v: "c = ChanRef v" by (metis chanRef.exhaust)
  obtain idx where idx: "nat_of_integer (the (getVar v g p)) = idx" by blast
  note idx' = idx[symmetric, unfolded getVar_def]
  show ?thesis
  proof (cases "idx < length (gState.channels g)")
    case True 
    note DEF = True EERecv v idx' assms
    show ?thesis
    proof (cases "gState.channels g ! idx")
      note channel_inv.simps[simp del]
      case (Channel cap ts q) 
      with True have "Channel cap ts q \<in> set (gState.channels g)" 
        by (metis nth_mem)
      with assms have c_inv: "channel_inv (Channel cap ts q)" 
        by (auto simp add: gState_inv_def simp del: channel_inv.simps)
      moreover obtain res q' where 
        "apfst the (find_remove (recvArgsCheck g p rs) q) = (res, q')" 
        by (metis prod.exhaust)
      moreover hence "q' = snd (find_remove (recvArgsCheck g p rs) q)"
        by (simp add: apfst_def map_prod_def split: prod.splits)
      with find_remove_subset find_remove_length have 
        "set q' \<subseteq> set q" "length q' \<le> length q" 
        by (metis surjective_pairing)+
      with c_inv have "channel_inv (Channel cap ts q')" 
        by (auto simp add: channel_inv.simps)
      moreover {
        assume "q \<noteq> []"
        hence "set (tl q) \<subseteq> set q" using tl_subset by auto
        with c_inv have "channel_inv (Channel cap ts (tl q))" 
          by (auto simp add: channel_inv.simps)
      } 
      moreover {
        fix res g' p'
        assume "evalRecvArgs rs res g p = (g',p')" 
        with evalRecvArgs_gState_progress_rel assms have 
          "(g,g') \<in> gState_progress_rel prog" 
          by (metis fst_conv)
        hence "length (channels g) \<le> length (channels g')" 
          by (simp add: gState_progress_rel_def)
      }
      ultimately show ?thesis using Channel DEF
        apply (cases v) 
        apply (auto simp add: withChannel'_def withVar'_def for_all_def 
                    split: channel.split prod.split
                    elim: fstE 
                    intro!: evalRecvArgs_gState_progress_rel 
                            gState_progress_rel_channels_update_step)
          apply force+
        done
    next
      case HSChannel 
      obtain g' p' where *: "evalRecvArgs rs (hsdata g) g p = (g',p')" 
        by (metis prod.exhaust)
      with assms have "(g,g') \<in> gState_progress_rel prog" 
        by (auto elim!: fstE intro!: evalRecvArgs_gState_progress_rel)
      also hence "gState_inv prog g'" by blast
      hence "(g',g'\<lparr>handshake := 0, hsdata := []\<rparr>) \<in> gState_progress_rel prog" 
        by (auto simp add: gState_progress_rel_def gState_inv_def)
      finally 
      have "(g,g'\<lparr>handshake := 0, hsdata := []\<rparr>) \<in> gState_progress_rel prog" .
      with DEF HSChannel * show ?thesis 
        by (cases v) (auto simp add: withChannel'_def withVar'_def for_all_def 
                           split: channel.split prod.split)
    next
      case InvChannel with DEF show ?thesis 
        by (cases v) (auto simp add: withChannel'_def withVar'_def)
    qed
  next
    case False with EERecv idx' v assms show ?thesis 
      by (cases v) (auto simp add: withChannel'_def withVar'_def)
  qed
qed simp_all

lemma evalEffect_cl_inv:
  assumes "cl_inv (g,p)"
  and "program_inv prog"
  and "gState_inv prog g"
  and "pState_inv prog p"
  shows "cl_inv  (evalEffect e prog g p)"
  using assms
proof (cases e)
  case EERun with assms show ?thesis by (force intro!: runProc_cl_inv)
next
  case (EESend c es srt) then obtain v where "ChanRef v = c" by (cases c) simp
  with EESend assms show ?thesis
    by (cases v)
       (auto simp add: withChannel'_def withVar'_def split: channel.split
             intro!: cl_inv_channels_update)
next
  case (EERecv c es srt) then obtain v where "ChanRef v = c" by (cases c) simp
  with EERecv assms show ?thesis
    apply (cases v)
    apply (auto simp add: withChannel'_def withVar'_def split: channel.split prod.split
                intro!: cl_inv_channels_update)
    apply (metis evalRecvArgs_cl_inv)+
    done
qed (simp_all add: setVar_cl_inv mkVarChannelProc_cl_inv)

subsubsection \<open>Executable edges\<close>

text \<open>
  To find a successor global state, we first need to find all those edges which are executable
  (\ie the condition evaluates to true).
\<close>
type_synonym choices = "(edge * pState) list"
  \<comment> \<open>A choice is an executable edge and the process it belongs to.\<close>

definition getChoices :: "gState\<^sub>I \<Rightarrow> pState \<Rightarrow> edge list \<Rightarrow> choices" where
  "getChoices g p = foldl (\<lambda>E e. 
      if evalHandshake (cond e) (handshake g) g p \<and> evalCond (cond e) g p 
      then (e,p)#E
      else E) []"

lemma getChoices_sub_edges_fst:
  "fst ` set (getChoices g p es) \<subseteq> set es"
unfolding getChoices_def
by (rule foldl_rule_aux) auto

lemma getChoices_sub_edges:
  "(a,b) \<in> set (getChoices g p es) \<Longrightarrow> a \<in> set es"
using getChoices_sub_edges_fst
by force

lemma getChoices_p_snd:
  "snd ` set (getChoices g p es) \<subseteq> {p}"
unfolding getChoices_def
by (rule foldl_rule_aux) auto

lemma getChoices_p:
  "(a,b) \<in> set (getChoices g p es) \<Longrightarrow> b = p"
using getChoices_p_snd
by force

definition sort_by_pri where
  "sort_by_pri min_pri edges = foldl (\<lambda>es e. 
      let idx = nat_of_integer (abs (prio e))
      in if idx > min_pri 
         then abort STR ''Invalid priority'' (\<lambda>_. es)
         else let ep = e # (es ! idx) in es[idx := ep]
      ) (replicate (min_pri + 1) []) edges"

lemma sort_by_pri_edges':
  assumes "set edges \<subseteq> A"
  shows "set (sort_by_pri min_pri edges) \<subseteq> {xs. set xs \<subseteq> A}"
using assms
unfolding sort_by_pri_def
apply (rule_tac I="\<lambda>\<sigma> _. (\<forall>x \<in> set \<sigma>. set x \<subseteq> A) \<and> length \<sigma> = min_pri + 1" in foldl_rule_aux_P)
    apply simp
  apply (force dest!: subsetD[OF set_update_subset_insert] 
               split: if_splits)
apply force
done

lemma sort_by_pri_edges:
  assumes "set edges \<subseteq> A"
  and "es \<in> set (sort_by_pri min_pri edges)"
  shows "set es \<subseteq> A"
using sort_by_pri_edges'[OF assms(1)] assms
by auto

lemma sort_by_pri_length:
  "length (sort_by_pri min_pri edges) = min_pri + 1"
unfolding sort_by_pri_def
by (rule foldl_rule_aux_P [where I="\<lambda>\<sigma> _. length \<sigma> = min_pri + 1"]) 
   simp_all

definition executable 
  :: "states iarray \<Rightarrow> gState\<^sub>I \<Rightarrow> choices nres"
  \<comment> \<open>Find all executable edges\<close>
 where
  "executable ss g = (
      let procs = procs g in
      nfoldli procs (\<lambda>_. True) (\<lambda>p E.
        if (exclusive g = 0 \<or> exclusive g = pid p) then do {
            let (min_pri, edges) = (ss !! pState.idx p) !! pc p;
            ASSERT(set edges \<subseteq> edgeSet (ss !! pState.idx p));

            (E',_,_) \<leftarrow> 
               if min_pri = 0 then do {
                  WHILE\<^sub>T (\<lambda>(E,brk,_). E = [] \<and> brk = 0) (\<lambda> (_, _, ELSE). do {
                     let g = g\<lparr>gState\<^sub>I.else := ELSE\<rparr>;
                         E = getChoices g p edges
                     in
                         if E = [] then (
                            if \<not> ELSE then RETURN (E, 0::nat, True)
                            else RETURN (E, 1, False))
                         else RETURN (E, 1, ELSE) }) ([], 0::nat, False)
                } else do {
                  let min_pri = nat_of_integer (abs min_pri);
                  let pri_edges = sort_by_pri min_pri edges;
                  ASSERT (\<forall>es \<in> set pri_edges. 
                             set es \<subseteq> edgeSet (ss !! pState.idx p));
                  let pri_edges = IArray pri_edges;

                  WHILE\<^sub>T (\<lambda>(E,pri,_). E = [] \<and> pri \<le> min_pri) (\<lambda>(_, pri, ELSE). do {
                     let es = pri_edges !! pri;
                     let g = g\<lparr>gState\<^sub>I.else := ELSE\<rparr>;
                     let E = getChoices g p es;
                     if E = [] then (
                         if \<not> ELSE then RETURN (E,pri,True)
                         else RETURN (E, pri + 1, False))
                     else RETURN (E, pri, ELSE) }) ([], 0, False)
                }; 
            RETURN (E'@E)
        } else RETURN E
      ) []
 )"

definition
  "while_rel1 = 
          measure (\<lambda>x. if x = [] then 1 else 0) 
  <*lex*> measure (\<lambda>x. if x = 0 then 1 else 0) 
  <*lex*> measure (\<lambda>x. if \<not> x then 1 else 0)"

lemma wf_while_rel1: 
  "wf while_rel1"
unfolding while_rel1_def
by auto

definition
  "while_rel2 mp = 
          measure (\<lambda>x. if x = [] then 1 else 0) 
  <*lex*> measure (\<lambda>x. (mp + 1) - x) 
  <*lex*> measure (\<lambda>x. if \<not> x then 1 else 0)"

lemma wf_while_rel2: 
  "wf (while_rel2 mp)"
unfolding while_rel2_def
by auto

lemma executable_edgeSet:
  assumes "gState_inv prog g"
  and "program_inv prog"
  and "ss = states prog"
  shows "executable ss g 
    \<le> SPEC (\<lambda>cs. \<forall>(e,p) \<in> set cs. 
                    e \<in> edgeSet (ss !! pState.idx p) 
                  \<and> pState_inv prog p 
                  \<and> cl_inv (g,p))"
  unfolding executable_def
  using assms
  apply (refine_rcg refine_vcg nfoldli_rule[where 
              I="\<lambda>_ _ cs. \<forall>(e,p) \<in> set cs. 
                              e \<in> edgeSet (ss !! pState.idx p) 
                            \<and> pState_inv prog p 
                            \<and> cl_inv (g,p)"])
          apply simp
        apply (rename_tac p l1 l2 \<sigma> e p')
        apply (subgoal_tac "pState_inv prog p")
          apply (clarsimp simp add: edgeSet_def pState_inv_def)[]
          apply (rule_tac x="IArray.list_of 
                               (IArray.list_of (states prog) ! pState.idx p) ! pc p" in bexI)
            apply simp
          apply (force intro!: nth_mem)
        apply (force simp add: gState_inv_def)
      apply (refine_rcg refine_vcg wf_while_rel1 WHILET_rule[where 
                 I="\<lambda>(cs,_,_). \<forall>(e,p) \<in> set cs. 
                                  e \<in> edgeSet (ss !! pState.idx p) 
                                \<and> pState_inv prog p 
                                \<and> cl_inv (g,p)" 
                 and R=while_rel1])
        apply (vc_solve solve: asm_rl simp add: while_rel1_def)
      apply (frule getChoices_p)
      using  getChoices_sub_edges apply (force simp add: gState_inv_def)
    using sort_by_pri_edges apply fastforce
  apply (rename_tac min_pri pri_edges)
  apply (rule_tac I="\<lambda>(cs,_,_). \<forall>(e,p) \<in> set cs. 
                                  e \<in> edgeSet (ss !! pState.idx p) 
                                \<and> pState_inv prog p 
                                \<and> cl_inv (g,p)" 
              and R="while_rel2 (nat_of_integer (abs min_pri))" 
               in WHILET_rule)
        apply (simp add: wf_while_rel2)
      apply simp
    apply (refine_rcg refine_vcg)
        apply (clarsimp_all split: prod.split simp add: while_rel2_def)
      apply (metis diff_less_mono lessI)
    apply (rename_tac idx' else e p')
    apply (frule getChoices_p)
    apply (frule getChoices_sub_edges) 
    apply (subgoal_tac 
             "sort_by_pri (nat_of_integer \<bar>min_pri\<bar>) pri_edges ! idx' 
                 \<in> set (sort_by_pri (nat_of_integer \<bar>min_pri\<bar>) pri_edges)")
      apply (auto simp add: assms gState_inv_def)[]
    apply (force simp add: sort_by_pri_length)
  apply (auto simp add: assms)
  done

lemma executable_edgeSet':
  assumes "gState_inv prog g"
  and "program_inv prog"
  shows "executable (states prog) g 
  \<le> SPEC (\<lambda>cs. \<forall>(e,p) \<in> set cs. 
                  e \<in> edgeSet ((states prog) !! pState.idx p) 
                \<and> pState_inv prog p 
                \<and> cl_inv(g,p))"
using executable_edgeSet[where ss = "states prog"] assms
by simp

schematic_goal executable_refine:
  "RETURN (?ex s g) \<le> executable s g"
unfolding executable_def
by (refine_transfer)

concrete_definition executable_impl for s g uses executable_refine

subsubsection \<open>Successor calculation\<close>

function to\<^sub>I where
  "to\<^sub>I \<lparr> gState.vars = v, channels = ch, timeout = t, procs = p \<rparr> 
     = \<lparr> gState.vars = v, channels = ch, timeout = False, procs = p, 
          handshake = 0, hsdata = [], exclusive = 0, gState\<^sub>I.else = False \<rparr>"
by (metis gState.cases) (metis gState.ext_inject)
termination by lexicographic_order

function "from\<^sub>I" where
  "from\<^sub>I \<lparr> gState.vars = v, channels = ch, timeout = t, procs = p, \<dots> = m \<rparr> 
       = \<lparr> gState.vars = v, channels = ch, timeout = t, procs = p \<rparr>"
by (metis gState.surjective) (metis gState.ext_inject)
termination by lexicographic_order

function reset\<^sub>I where
  "reset\<^sub>I \<lparr> gState.vars = v, channels = ch, timeout = t, procs = p, 
             handshake = hs, hsdata = hsd, exclusive = _, gState\<^sub>I.else = _ \<rparr> 
        = \<lparr> gState.vars = v, channels = ch, timeout = False, procs = p, 
             handshake = 0, hsdata = if hs \<noteq> 0 then hsd else [], exclusive = 0, 
             gState\<^sub>I.else = False \<rparr>"
by (metis (full_types)  gState\<^sub>I.surjective unit.exhaust)
   (metis gState.select_convs gState\<^sub>I.select_convs)
termination by lexicographic_order

lemma gState_inv_to\<^sub>I:
  "gState_inv prog g = gState_inv prog (to\<^sub>I g)"
by (cases g, simp add: gState_inv_def cl_inv_def)

lemma gState_inv_from\<^sub>I:
  "gState_inv prog g = gState_inv prog (from\<^sub>I g)"
by (cases g, simp add: gState_inv_def cl_inv_def)

lemma gState_inv_reset\<^sub>I:
  "gState_inv prog g = gState_inv prog (reset\<^sub>I g)"
by (cases g, simp add: gState_inv_def cl_inv_def)

lemmas gState_inv_I_simps = 
  gState_inv_to\<^sub>I gState_inv_from\<^sub>I gState_inv_reset\<^sub>I

definition removeProcs 
  \<comment> \<open>Remove ended processes, if there is no running one with a higher pid.\<close>
where
  "removeProcs ps = foldr (\<lambda>p (dead,sd,ps,dcs). 
           if dead \<and> pc p = 0 then (True, True, ps, pState.channels p @ dcs)
           else (False, sd, p#ps, dcs)) ps (True, False, [], [])"


lemma removeProcs_subset':
  "set (fst (snd (snd (removeProcs ps)))) \<subseteq> set ps"
unfolding removeProcs_def
apply (subst foldr_conv_foldl)
apply (rule foldl_rule_aux_P[where I="\<lambda>(_,_,ps',_) _. set ps' \<subseteq> set ps"])
    apply simp
  apply (clarsimp split: if_splits)
    apply force
  apply (rename_tac p)
  apply (case_tac "p = x")
    apply (subst set_rev[symmetric])
    apply simp
  apply force
apply force
done

lemma removeProcs_length':
  "length (fst (snd (snd (removeProcs ps)))) \<le> length ps"
unfolding removeProcs_def
apply (subst foldr_conv_foldl)
apply (rule foldl_rule_aux_P[where 
        I="\<lambda>(_,_,ps',_) ps''. length ps' + length ps'' \<le> length ps"])
    apply (auto split: if_splits)
done

lemma removeProcs_subset:
  "removeProcs ps = (dead,sd,ps',dcs) \<Longrightarrow> set ps' \<subseteq> set ps"
using removeProcs_subset'
by (metis fst_conv snd_conv)

lemma removeProcs_length:
  "removeProcs ps = (dead,sd,ps',dcs) \<Longrightarrow> length ps' \<le> length ps"
using removeProcs_length'
by (metis fst_conv snd_conv)

definition cleanChans :: "integer list \<Rightarrow> channels \<Rightarrow> channels" 
  \<comment> \<open>Mark channels of closed processes as invalid.\<close>
where
  "cleanChans dchans cs = snd (foldl (\<lambda>(i,cs) c. 
       if List.member dchans i then (i + 1, cs@[InvChannel])
       else (i + 1, cs@[c])) (0, []) cs)"

lemma cleanChans_channel_inv:
  assumes "set cs \<subseteq> Collect channel_inv"
  shows "set (cleanChans dchans cs) \<subseteq> Collect channel_inv"
using assms
unfolding cleanChans_def
apply (rule_tac foldl_rule_aux)
  apply (force split: if_splits)+
done

lemma cleanChans_length:
  "length (cleanChans dchans cs) = length cs"
unfolding cleanChans_def
by (rule foldl_rule_aux_P[where 
       I="\<lambda>(_,cs') cs''. length cs' + length cs'' = length cs"]) 
   (force split: if_splits)+

definition checkDeadProcs :: "'a gState_scheme \<Rightarrow> 'a gState_scheme" where
  "checkDeadProcs g = ( 
     let (_, soDied, procs, dchans) = removeProcs (procs g) in
     if soDied then
         g\<lparr> procs := procs, channels := cleanChans dchans (channels g)\<rparr>
     else g)"

lemma checkDeadProcs_gState_progress_rel:
  assumes "gState_inv prog g"
  shows "(g, checkDeadProcs g) \<in> gState_progress_rel prog"
using assms cleanChans_length[where cs="channels g"] 
      cleanChans_channel_inv[where cs="channels g"]
unfolding checkDeadProcs_def
apply (intro gState_progress_relI)
      apply assumption
    apply (clarsimp split: if_splits prod.splits)
    apply (frule removeProcs_length)
    apply (frule removeProcs_subset)
    apply (auto simp add: gState_inv_def cl_inv_def)[]
  apply (clarsimp split: if_splits prod.splits)+
done

lemma gState_progress_rel_exclusive:
  "(g, g') \<in> gState_progress_rel prog 
   \<Longrightarrow> (g, g'\<lparr>exclusive := p\<rparr>) \<in> gState_progress_rel prog"
by (simp add:  gState_progress_rel_def gState_inv_def cl_inv_def)

definition applyEdge 
  :: "program \<Rightarrow> edge \<Rightarrow> pState \<Rightarrow> gState\<^sub>I \<Rightarrow> gState\<^sub>I nres"
 where
  "applyEdge prog e p g = do {
    
         let (g',p') = evalEffect (effect e) prog g p;
         ASSERT ((g,g') \<in> gState_progress_rel prog);
         ASSERT (pState_inv prog p'); 
         ASSERT (cl_inv (g',p'));

         let p'' = (case target e of Index t \<Rightarrow> 
                     if t < IArray.length (states prog !! pState.idx p') then p'\<lparr>pc := t\<rparr>
                     else abort STR ''Edge target out of bounds'' (\<lambda>_. p')
                   | _ \<Rightarrow>  abort STR ''Edge target not Index'' (\<lambda>_. p'));
         ASSERT (pState_inv prog p'');

         let g'' = g'\<lparr>procs := list_update (procs g') (pid p'' - 1) p''\<rparr>;
         ASSERT ((g',g'') \<in> gState_progress_rel prog);

         let g''' = (if isAtomic e \<and> handshake g'' = 0 
                     then g''\<lparr> exclusive := pid p'' \<rparr> 
                     else g'');
         ASSERT ((g',g''') \<in> gState_progress_rel prog);
         
         let g\<^sub>f = (if pc p'' = 0 then checkDeadProcs g''' else g''');
         ASSERT ((g''',g\<^sub>f) \<in> gState_progress_rel prog);
         RETURN g\<^sub>f }"

lemma applyEdge_gState_progress_rel:
  assumes "program_inv prog"
  and "gState_inv prog g"
  and "pState_inv prog p"
  and "cl_inv (g,p)"
  and "e \<in> edgeSet (states prog !! pState.idx p)"
  shows "applyEdge prog e p g \<le> SPEC (\<lambda>g'. (g,g') \<in> gState_progress_rel prog)"
using assms
unfolding applyEdge_def
apply (intro refine_vcg)

apply (force elim: fstE intro!: evalEffect_gState_progress_rel)

apply (force elim: sndE intro!: evalEffect_pState_inv)

apply (drule subst)
apply (rule evalEffect_cl_inv)
apply assumption+

apply (cases "target e")
apply (clarsimp simp add: pState_inv_def)
apply simp

apply (frule gState_progress_rel_gState_invI2)
apply (cases "target e")
  apply (clarsimp split: if_splits)
  apply (intro gState_progress_relI)
    apply assumption
    apply (auto simp add: gState_inv_def cl_inv_def  
                dest!: subsetD[OF set_update_subset_insert])[]
    apply (simp add: cl_inv_def)
    apply simp
  apply (intro gState_progress_relI)
    apply assumption
    apply (auto simp add: gState_inv_def cl_inv_def 
                dest!: subsetD[OF set_update_subset_insert])[]
    apply (simp add: cl_inv_def)
    apply simp
  apply (clarsimp split: if_splits)
  apply (intro gState_progress_relI)
    apply assumption
    apply (auto simp add: gState_inv_def cl_inv_def 
                dest!: subsetD[OF set_update_subset_insert])[]
    apply (simp add: cl_inv_def)
    apply simp

apply (auto split: if_splits intro!: gState_progress_rel_exclusive)[]

apply (force intro!: checkDeadProcs_gState_progress_rel)

apply (blast intro!: gState_progress_rel_trans)
done

schematic_goal applyEdge_refine:
  "RETURN (?ae prog e p g) \<le> applyEdge prog e p g"
unfolding applyEdge_def
by (refine_transfer)

concrete_definition applyEdge_impl for e p g uses applyEdge_refine

definition nexts 
  :: "program \<Rightarrow> gState \<Rightarrow> gState ls nres"
  \<comment> \<open>The successor function\<close>
where
  "nexts prog g = (
     let 
       f = from\<^sub>I;
       g = to\<^sub>I g
     in

        REC (\<lambda>D g. do {
          E \<leftarrow> executable (states prog) g;
          if E = [] then 
            if handshake g \<noteq> 0 then
              \<comment> \<open>HS not possible -- remove current step\<close>
              RETURN (ls.empty()) 
            else if exclusive g \<noteq> 0 then
              \<comment> \<open>Atomic blocks -- just return current state\<close>
              RETURN (ls.sng (f g)) 
            else if \<not> timeout g then
              \<comment> \<open>Set timeout\<close>
              D (g\<lparr>timeout := True\<rparr>)
            else 
              \<comment> \<open>If all else fails: stutter\<close>
              RETURN (ls.sng (f (reset\<^sub>I g)))
          else
             \<comment> \<open>Setting the internal variables (exclusive, handshake, ...) to 0\<close>
             \<comment> \<open>is safe -- they are either set by the edges, or not thought\<close>
             \<comment> \<open>to be used outside executable.\<close>
             let g = reset\<^sub>I g in
             nfoldli E (\<lambda>_. True) (\<lambda>(e,p) G.
                 applyEdge prog e p g \<bind> (\<lambda> g'.
                 if handshake g' \<noteq> 0 \<or> isAtomic e then do {
                    G\<^sub>R \<leftarrow> D g';
                    if ls.isEmpty G\<^sub>R \<and> handshake g' = 0 then
                       \<comment> \<open>this only happens if the next step is a handshake, which fails\<close>
                       \<comment> \<open>hence we stay at the current state\<close>
                       RETURN (ls.ins (f g') G)
                    else
                       RETURN (ls.union G\<^sub>R G)
                 } else RETURN (ls.ins (f g') G))) (ls.empty())
         }) g
         \<bind> (\<lambda>G. if ls.isEmpty G then RETURN (ls.sng (f g)) else RETURN G)
)"

lemma gState_progress_rel_intros:
  "(to\<^sub>I g, gI') \<in> gState_progress_rel prog 
       \<Longrightarrow> (g, from\<^sub>I gI') \<in> gState_progress_rel prog"
  "(gI, gI') \<in> gState_progress_rel prog 
       \<Longrightarrow> (gI, reset\<^sub>I gI') \<in> gState_progress_rel prog"
  "(to\<^sub>I g, gI') \<in> gState_progress_rel prog 
       \<Longrightarrow> (to\<^sub>I g, gI'\<lparr>timeout := t\<rparr>) \<in> gState_progress_rel prog"
unfolding gState_progress_rel_def
by (cases g, cases gI', cases gI, force simp add: gState_inv_def cl_inv_def)+

lemma gState_progress_rel_step_intros:
  "(to\<^sub>I g, g') \<in> gState_progress_rel prog 
      \<Longrightarrow> (reset\<^sub>I g', g'') \<in> gState_progress_rel prog 
      \<Longrightarrow> (g, from\<^sub>I g'') \<in> gState_progress_rel prog"
  "(to\<^sub>I g, g') \<in> gState_progress_rel prog 
      \<Longrightarrow> (reset\<^sub>I g', g'') \<in> gState_progress_rel prog 
      \<Longrightarrow> (to\<^sub>I g, g'') \<in> gState_progress_rel prog"
unfolding gState_progress_rel_def
by (cases g, cases g', cases g'', force simp add: gState_inv_def cl_inv_def)+

lemma cl_inv_reset\<^sub>I:
  "cl_inv(g,p) \<Longrightarrow> cl_inv(reset\<^sub>I g, p)"
  by (cases g) (simp add: cl_inv_def)

lemmas refine_helpers = 
  gState_progress_rel_intros gState_progress_rel_step_intros cl_inv_reset\<^sub>I


lemma nexts_SPEC:
  assumes "gState_inv prog g"
  and "program_inv prog"
  shows "nexts prog g \<le> SPEC (\<lambda>gs. \<forall>g' \<in> ls.\<alpha> gs. (g,g') \<in> gState_progress_rel prog)"
  using assms
  unfolding nexts_def
  apply (refine_rcg refine_vcg REC_rule[where 
           pre="\<lambda>g'. (to\<^sub>I g,g') \<in> gState_progress_rel prog"])
    apply (simp add: gState_inv_to\<^sub>I)
  apply (rule order_trans[OF executable_edgeSet'])
      apply (drule gState_progress_rel_gState_invI2)
      apply assumption
    apply assumption
  apply (refine_rcg refine_vcg nfoldli_rule[where 
             I="\<lambda>_ _ \<sigma>.  \<forall>g' \<in> ls.\<alpha> \<sigma>. (g,g') \<in> gState_progress_rel prog"] 
          order_trans[OF applyEdge_gState_progress_rel])
        apply (vc_solve intro: refine_helpers solve: asm_rl simp add: ls.correct)
  apply (rule order_trans)
    apply (rprems)
    apply (vc_solve intro: refine_helpers solve: asm_rl simp add: ls.correct)
  apply (rule order_trans)
    apply rprems
    apply (vc_solve intro: refine_helpers solve: asm_rl simp add: ls.correct)
  done

lemma RETURN_dRETURN:
  "RETURN f \<le> f' \<Longrightarrow> nres_of (dRETURN f) \<le> f'"
unfolding nres_of_def
by simp

lemma executable_dRETURN:
  "nres_of (dRETURN (executable_impl prog g)) \<le> executable prog g"
using executable_impl.refine
by (simp add: RETURN_dRETURN)

lemma applyEdge_dRETURN:
  "nres_of (dRETURN (applyEdge_impl prog e p g)) \<le> applyEdge prog e p g"
using applyEdge_impl.refine
by (simp add: RETURN_dRETURN)

schematic_goal nexts_code_aux:
  "nres_of (?nexts prog g) \<le> nexts prog g"
  unfolding nexts_def 
  by (refine_transfer the_resI executable_dRETURN applyEdge_dRETURN)

concrete_definition nexts_code_aux for prog g uses nexts_code_aux
prepare_code_thms nexts_code_aux_def

subsubsection \<open>Handle non-termination\<close>

text \<open>
  A Promela model may include non-terminating parts. Therefore we cannot guarantee, that @{const nexts} will actually terminate.
  To avoid having to deal with this in the model checker, we fail in case of non-termination.
\<close>

(* TODO: Integrate such a concept into refine_transfer! *)
definition SUCCEED_abort where
  "SUCCEED_abort msg dm m = ( 
     case m of 
       RES X \<Rightarrow> if X={} then Code.abort msg (\<lambda>_. dm) else RES X
     | _ \<Rightarrow> m)"


definition dSUCCEED_abort where
  "dSUCCEED_abort msg dm m = (
     case m of 
       dSUCCEEDi \<Rightarrow> Code.abort msg (\<lambda>_. dm)
     | _ \<Rightarrow> m)"

definition ref_succeed where 
  "ref_succeed m m' \<longleftrightarrow> m \<le> m' \<and> (m=SUCCEED \<longrightarrow> m'=SUCCEED)"

lemma dSUCCEED_abort_SUCCEED_abort:
   "\<lbrakk> RETURN dm' \<le> dm; ref_succeed (nres_of m') m \<rbrakk> 
       \<Longrightarrow> nres_of (dSUCCEED_abort msg (dRETURN dm') (m')) 
           \<le> SUCCEED_abort msg dm m"
unfolding dSUCCEED_abort_def SUCCEED_abort_def ref_succeed_def
by (auto split: dres.splits nres.splits)

text \<open>The final successor function now incorporates:
  \begin{enumerate}
    \item @{const Promela.nexts}
    \item handling of non-termination
  \end{enumerate}\<close>
definition nexts_code where 
  "nexts_code prog g = 
     the_res (dSUCCEED_abort (STR ''The Universe is broken!'') 
                             (dRETURN (ls.sng g)) 
                             (nexts_code_aux prog g))"

lemma nexts_code_SPEC:
  assumes "gState_inv prog g"
  and "program_inv prog"
  shows "g' \<in> ls.\<alpha> (nexts_code prog g) 
         \<Longrightarrow> (g,g') \<in> gState_progress_rel prog"
unfolding nexts_code_def
unfolding dSUCCEED_abort_def
using assms
using order_trans[OF nexts_code_aux.refine nexts_SPEC[OF assms(1,2)]]
by (auto split: dres.splits simp: ls.correct)

subsection \<open>Finiteness of the state space\<close>

inductive_set reachable_states
  for P :: program
  and g\<^sub>s :: gState \<comment> \<open>start state\<close>
where
"g\<^sub>s \<in> reachable_states P g\<^sub>s" |
"g \<in> reachable_states P g\<^sub>s \<Longrightarrow> x \<in> ls.\<alpha> (nexts_code P g) 
                               \<Longrightarrow> x \<in> reachable_states P g\<^sub>s"

lemmas reachable_states_induct[case_names init step] = 
  reachable_states.induct[split_format (complete)]

lemma reachable_states_finite:
  assumes "program_inv prog"
  and "gState_inv prog g"
  shows "finite (reachable_states prog g)"
proof (rule finite_subset[OF _ gStates_finite[of _ g]])
  define INV where "INV g' \<longleftrightarrow> g' \<in> (gState_progress_rel prog)\<^sup>* `` {g} \<and> gState_inv prog g'" for g'

  {
    fix g'
    have "g' \<in> reachable_states prog g \<Longrightarrow> INV g'"
    proof (induct rule: reachable_states_induct)
      case init with assms show ?case by (simp add: INV_def)
    next
      case (step g g')
      from step(2,3) have 
        "(g, g') \<in> gState_progress_rel prog"
        using nexts_code_SPEC[OF _ \<open>program_inv prog\<close>]
        unfolding INV_def by auto
      thus ?case using step(2) unfolding INV_def by auto
    qed
   }

  thus "reachable_states prog g \<subseteq> 
        (gState_progress_rel prog)\<^sup>* `` {g}"
    unfolding INV_def by auto
qed

subsection \<open>Traces\<close>

text \<open>When trying to generate a lasso, we have a problem: We only have a list of global
states. But what are the transitions to come from one to the other?

This problem shall be tackled by @{term replay}: Given two states, it generates a list of
transitions that was taken.\<close>

(* Give a list of edges that lead from g\<^sub>1 to g\<^sub>2 *)
definition replay :: "program \<Rightarrow> gState \<Rightarrow> gState \<Rightarrow> choices nres" where
  "replay prog g\<^sub>1 g\<^sub>2 = (
     let 
       g\<^sub>1 = to\<^sub>I g\<^sub>1;
       check = \<lambda>g. from\<^sub>I g = g\<^sub>2
     in
       REC\<^sub>T (\<lambda>D g. do {
       E \<leftarrow> executable (states prog) g;
       if E = [] then 
         if check g then RETURN []
         else if \<not> timeout g then D (g\<lparr>timeout := True\<rparr>)
         else abort STR ''Stuttering should not occur on replay'' 
                    (\<lambda>_. RETURN [])
       else
          let g = reset\<^sub>I g in
          nfoldli E (\<lambda>E. E = []) (\<lambda>(e,p) _.
             applyEdge prog e p g \<bind> (\<lambda>g'.
               if handshake g' \<noteq> 0 \<or> isAtomic e then do {
                 E\<^sub>R \<leftarrow> D g';
                 if E\<^sub>R = [] then
                    if check g' then RETURN [(e,p)] else RETURN []
                 else
                    RETURN ((e,p) # E\<^sub>R)
                } else if check g' then RETURN [(e,p)] else RETURN [])
             ) []
       }) g\<^sub>1
)"

lemma abort_refine[refine_transfer]:
  "nres_of (f ()) \<le> F () \<Longrightarrow> nres_of (abort s f) \<le> abort s F"
  "f() \<noteq> dSUCCEED \<Longrightarrow> abort s f \<noteq> dSUCCEED"
by auto

schematic_goal replay_code_aux:
  "RETURN (?replay prog g\<^sub>1 g\<^sub>2) \<le> replay prog g\<^sub>1 g\<^sub>2"
unfolding replay_def applyEdge_def
by (refine_transfer the_resI executable_dRETURN)

concrete_definition replay_code for prog g\<^sub>1 g\<^sub>2 uses replay_code_aux
prepare_code_thms replay_code_def

subsubsection \<open>Printing of traces\<close>
(* Might go to another theory *)

definition procDescr 
  :: "(integer \<Rightarrow> string) \<Rightarrow> program \<Rightarrow> pState \<Rightarrow> string" 
where
  "procDescr f prog p = (
     let 
        name = String.explode (proc_names prog !! pState.idx p);
        id = f (integer_of_nat (pid p))
     in
        name @ '' ('' @ id @ '')'')"

definition printInitial 
  :: "(integer \<Rightarrow> string) \<Rightarrow> program \<Rightarrow> gState \<Rightarrow> string"
where
  "printInitial f prog g\<^sub>0 = (
       let psS = printList (procDescr f prog) (procs g\<^sub>0) [] [] ''  '' in
       ''Initially running: '' @ psS)"

abbreviation "lf \<equiv> CHR 0x0A"

fun printConfig 
  :: "(integer \<Rightarrow> string) \<Rightarrow> program \<Rightarrow> gState option \<Rightarrow> gState \<Rightarrow> string" 
where
  "printConfig f prog None g\<^sub>0 = printInitial f prog g\<^sub>0"
| "printConfig f prog (Some g\<^sub>0) g\<^sub>1 = (
           let eps = replay_code prog g\<^sub>0 g\<^sub>1 in
           let print = (\<lambda>(e,p). procDescr f prog p @ '': '' @ printEdge f (pc p) e)
           in if eps = [] \<and> g\<^sub>1 = g\<^sub>0 then ''    -- stutter --''
              else printList print eps [] [] (lf#''    ''))"

definition "printConfigFromAST f \<equiv> printConfig f o fst o setUp"

subsection \<open>Code export\<close>

code_identifier
  code_module "PromelaInvariants" \<rightharpoonup> (SML) Promela
| code_module "PromelaDatastructures" \<rightharpoonup> (SML) Promela

definition "executable_triv prog g = executable_impl (snd prog) g"
definition "apply_triv prog g ep = applyEdge_impl prog (fst ep) (snd ep) (reset\<^sub>I g)"

export_code 
  setUp printProcesses printConfigFromAST nexts_code executable_triv apply_triv
  extractLTLs lookupLTL
  checking SML

export_code 
  setUp printProcesses printConfigFromAST nexts_code executable_triv apply_triv 
  extractLTLs lookupLTL
  in SML 
  file \<open>Promela.sml\<close>

end
