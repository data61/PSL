(*  Title:       Lightweight Java, the equivalence functions
    Authors:     Rok Strnisa <rok@strnisa.com>, 2006
                 Matthew Parkinson <matt@matthewp.com>, 2006
    Maintainer:  
*)

theory Lightweight_Java_Equivalence imports Lightweight_Java_Definition begin

(* BEGIN: HELPER FUNCTIONS *)

lemma map_id[simp]: "map id list = list" by (induct list) auto

lemma id_map_two[simp]: "map (\<lambda>(x,y). (x,y)) list = list" by (induct list) auto

lemma id_image_two[simp]: "(\<lambda>(x,y). (x,y)) ` set list = set list" by (induct list) auto

lemma map_fst[simp]: "map (\<lambda>(x, y). x) list = map fst list" by (induct list) auto

lemma map_snd[simp]: "map (\<lambda>(x, y). y) list = map snd list" by (induct list) auto

lemma zip_map_map_two [simp]: "zip (map fst list) (map snd list) = list"
by (induct list) auto

lemma concat_map_singlton [simp]: "concat (map (\<lambda>e. [e]) list) = list"
by (induct list) simp_all

lemma list_all_map_P [simp]: "list_all (\<lambda>b. b) (map (\<lambda>x. P x) list) = (\<forall>x \<in> set list. P x)"
by (induct list) simp_all

lemma dom_single[simp]: "a : dom (Map.empty(k \<mapsto> v)) = (a = k)"
by (simp add: dom_def)

lemma predicted_lu[rule_format, simp]:
  "x \<in> set list \<longrightarrow> map_of (map (\<lambda>key. (key, value)) list) x = Some value"
by (induct list) auto

lemma key_in_map1[simp]: "k \<notin> dom M' \<Longrightarrow> (M ++ M') k = M k"
apply (subgoal_tac "M' k = None")
apply (simp add: map_add_def, force simp add: domI)
done

lemma forall_cons [rule_format]: "(\<forall>x \<in> set (s#S). P x) \<and> y \<in> set S \<longrightarrow> P y"
by (induct_tac S) simp_all

lemma mem_cong[rule_format]:
  "x \<in> set list \<longrightarrow> (f x \<in> set (map f list))"
by (induct list) auto

lemma forall_union: "\<lbrakk>\<forall>a \<in> dom A. P (A a); \<forall>b \<in> dom B. P (B b)\<rbrakk> \<Longrightarrow> \<forall>x \<in> dom A \<union> dom B. P ((B ++ A) x)"
apply(safe)
 apply(force)
apply(drule_tac x = x in bspec, simp add: domI)
apply(case_tac "A x = None")
 apply(force simp add: map_add_def)
by (force)

(* END: HELPER FUNCTIONS *)

definition
class_name_f :: "cld \<Rightarrow> dcl"
where
"class_name_f cld =
  (case cld of cld_def dcl cl fds mds \<Rightarrow> dcl)"
lemma [simp]: "(class_name cld dcl) = (class_name_f cld = dcl)"
by (force simp add: class_name_f_def split: cld.splits
          intro: class_nameI elim: class_name.cases)

definition
superclass_name_f :: "cld \<Rightarrow> cl"
where
"superclass_name_f cld =
  (case cld of cld_def dcl cl fds mds \<Rightarrow> cl)"
lemma [simp]: "(superclass_name cld cl) = (superclass_name_f cld = cl)"
by (force simp add: superclass_name_f_def split: cld.splits
          intro: superclass_nameI elim: superclass_name.cases)

definition
class_fields_f :: "cld \<Rightarrow> fds"
where
"class_fields_f cld =
  (case cld of cld_def dcl cl fds mds \<Rightarrow> fds)"
lemma [simp]: "(class_fields cld fds) = (class_fields_f cld = fds)"
by (force simp add: class_fields_f_def split: cld.splits
          intro: class_fieldsI elim: class_fields.cases)

definition
class_methods_f :: "cld \<Rightarrow> meth_defs"
where
"class_methods_f cld =
  (case cld of cld_def dcl cl fds mds \<Rightarrow> mds)"
lemma [simp]: "(class_methods cld fds) = (class_methods_f cld = fds)"
by (force simp add: class_methods_f_def split: cld.splits
          intro: class_methodsI elim: class_methods.cases)

definition
method_name_f :: "meth_def \<Rightarrow> meth"
where
"method_name_f md =
  (case md of meth_def_def meth_sig meth_body \<Rightarrow>
  (case meth_sig of meth_sig_def cl meth vds \<Rightarrow> meth))"
lemma [simp]: "(method_name md m) = (method_name_f md = m)"
by (force simp add: method_name_f_def split: meth_def.splits meth_sig.splits
          intro: method_nameI elim: method_name.cases)

definition
distinct_names_f :: "P \<Rightarrow> bool"
where
"distinct_names_f P =
  (distinct (map class_name_f P))"
lemma distinct_names_map[rule_format]:
  "(\<forall>x\<in>set cld_dcl_list. case_prod (\<lambda>cld. (=) (class_name_f cld)) x) \<and> distinct (map snd cld_dcl_list)
      \<longrightarrow> distinct_names_f (map fst cld_dcl_list)"
apply(induct cld_dcl_list)
 apply(clarsimp simp add: distinct_names_f_def)+ apply(force)
done
lemma [simp]: "(distinct_names P) = (distinct_names_f P)"
apply(rule)
 apply(erule distinct_names.cases) apply(clarsimp simp add: distinct_names_map)
apply(simp add: distinct_names_f_def)
apply(rule_tac cld_dcl_list = "map (\<lambda>cld. (cld, class_name_f cld)) P" in dn_defI)
  apply(simp) apply(induct P) apply(simp) apply(simp)
 apply(clarsimp)
apply(clarsimp) apply(induct P) apply(simp) apply(force)
done

primrec
find_cld_f :: "P \<Rightarrow> ctx \<Rightarrow> fqn \<Rightarrow> ctxcld_opt"
where
"find_cld_f []         ctx fqn = None" |
"find_cld_f (cld#clds) ctx fqn =
  (case cld of cld_def dcl cl fds mds \<Rightarrow>
  (case fqn of fqn_def dcl' \<Rightarrow>
  (if dcl = dcl' then Some (ctx, cld) else find_cld_f clds ctx fqn)))"
lemma [simp]: "(find_cld P ctx fqn ctxcld_opt) = (find_cld_f P ctx fqn = ctxcld_opt)"
apply(rule)
 apply(induct rule: find_cld.induct) apply(simp+)
 apply(clarsimp)
apply(induct P)
 apply(simp add: fc_emptyI)
apply(case_tac fqn) apply(rename_tac cld clds dcl) apply(case_tac cld)
apply(clarsimp) apply(rename_tac dcl' cl' vds' mds') apply(rule)
apply(clarsimp) apply(rule fc_cons_trueI) apply(simp) apply(force)
apply(force intro: fc_cons_falseI[simplified])
done

lemma find_to_mem[rule_format]:
  "find_cld_f P ctx fqn = Some (ctx', cld) \<longrightarrow> cld : set P"
apply(induct P) by (clarsimp split: cld.splits fqn.splits)+

lemma find_cld_name_eq[rule_format]:
  "\<forall>ctxcld. find_cld_f P ctx (fqn_def dcl) = Some ctxcld \<longrightarrow> (\<exists>cl fds mds. (ctx, cld_def dcl cl fds mds) = ctxcld)"
apply(induct P) apply(simp) apply(clarsimp split: cld.splits fqn.splits) done

primrec
find_type_f :: "P \<Rightarrow> ctx \<Rightarrow> cl \<Rightarrow> ty_opt"
where
"find_type_f P ctx cl_object = Some ty_top" |
"find_type_f P ctx (cl_fqn fqn) =
  (case fqn of fqn_def dcl \<Rightarrow>
  (case find_cld_f P ctx fqn of None \<Rightarrow> None | Some (ctx', cld) \<Rightarrow>
     Some (ty_def ctx' dcl)))"
lemma [simp]: "(find_type P ctx cl ty_opt) = (find_type_f P ctx cl = ty_opt)"
apply(rule)
 apply(force elim: find_type.cases split: fqn.splits)
apply(case_tac cl) apply(force intro: ft_objI)
apply(rename_tac fqn)
apply(case_tac fqn) apply(clarsimp)
apply(split option.splits) apply(rule)
 apply(force intro: ft_nullI)
by (force intro: ft_dclI)

lemma mem_remove: "cld : set P \<Longrightarrow> length (remove1 cld P) < length P"
apply(induct P) by(simp, force split: if_split_asm)

lemma finite_program[rule_format, intro]:
  "\<forall>P cld. (\<exists>ctx ctx' fqn. find_cld_f P ctx fqn = Some (ctx', cld)) \<longrightarrow>
      length (remove1 cld P) < length P"
apply(clarsimp) apply(drule find_to_mem) by (simp add: mem_remove)

lemma path_length_eq[rule_format]:
  "path_length P ctx cl nn \<Longrightarrow> \<forall>nn'. path_length P ctx cl nn' \<longrightarrow> nn = nn'"
apply(erule path_length.induct)
 apply(clarsimp) apply(erule path_length.cases) apply(simp) apply(simp)
apply(rule) apply(rule)
apply(erule_tac ?a4.0 = nn' in path_length.cases) apply(clarify)
apply(clarsimp)
done

lemma fpr_termination[iff]:
  "\<forall>P cld ctx ctx' fqn. find_cld_f P ctx fqn = Some (ctx', cld) \<and> acyclic_clds P
       \<longrightarrow> The (path_length P ctx' (superclass_name_f cld)) < The (path_length P ctx (cl_fqn fqn))"
apply(clarsimp)
apply(erule acyclic_clds.cases) apply(clarsimp) apply(rename_tac P)
apply(erule_tac x = ctx in allE)
apply(erule_tac x = fqn in allE)
apply(clarsimp)
apply(rule theI2) apply(simp) apply(simp add: path_length_eq)
apply(erule path_length.cases) apply(simp) apply(clarsimp)
apply(rule theI2) apply(simp) apply(simp add: path_length_eq)
apply(drule_tac path_length_eq, simp)
apply(erule path_length.cases) apply(simp) apply(clarsimp)
apply(drule_tac path_length_eq, simp) apply(simp)
done

function
find_path_rec_f :: "P \<Rightarrow> ctx \<Rightarrow> cl \<Rightarrow> ctxclds \<Rightarrow> ctxclds_opt"
where
"find_path_rec_f P ctx  cl_object   path = Some path" |
"find_path_rec_f P ctx (cl_fqn fqn) path =
  (if ~(acyclic_clds P) then None else
  (case find_cld_f P ctx fqn of None \<Rightarrow> None | Some (ctx', cld) \<Rightarrow>
   find_path_rec_f P ctx'
                    (superclass_name_f cld) (path @ [(ctx',cld)])))"
by pat_completeness auto
termination
by (relation "measure (\<lambda>(P, ctx, cl, path). (THE nn. path_length P ctx cl nn))") auto

lemma [simp]: "(find_path_rec P ctx cl path path_opt) = (find_path_rec_f P ctx cl path = path_opt)"
apply(rule)
 apply(erule find_path_rec.induct) apply(simp)+
apply(induct rule: find_path_rec_f.induct)
 apply(clarsimp simp add: fpr_objI)
apply(clarsimp) apply(rule)
 apply(simp add: fpr_nullI)
apply(clarsimp split: option.splits)
apply(rule fpr_nullI)
 apply(simp add: fpr_nullI)
apply(rule fpr_fqnI) apply(force)+
done

definition
find_path_f :: "P \<Rightarrow> ctx \<Rightarrow> cl \<Rightarrow> ctxclds_opt"
where
"find_path_f P ctx cl = find_path_rec_f P ctx cl []"
lemma [simp]: "(find_path P ctx cl path_opt) = (find_path_f P ctx cl = path_opt)"
apply(rule)
 apply(erule find_path.cases) apply(unfold find_path_f_def) apply(simp)
apply(simp add: fp_defI)
done

primrec
find_path_ty_f :: "P \<Rightarrow> ty \<Rightarrow> ctxclds_opt"
where
"find_path_ty_f P  ty_top          = Some []" |
"find_path_ty_f P (ty_def ctx dcl) =
   find_path_f P ctx (cl_fqn (fqn_def dcl))"
lemma [simp]: "(find_path_ty P ty ctxclds_opt) = (find_path_ty_f P ty = ctxclds_opt)"
apply(rule)
 apply(force elim: find_path_ty.cases)
apply(case_tac ty)
 apply(clarsimp simp add: fpty_objI)
apply(clarsimp simp add: fpty_dclI)
done

primrec
fields_in_path_f :: "ctxclds \<Rightarrow> fs"
where
"fields_in_path_f []               = []" |
"fields_in_path_f (ctxcld#ctxclds) =
  (map (\<lambda>fd. case fd of fd_def cl f \<Rightarrow> f) (class_fields_f (snd ctxcld)))
     @ fields_in_path_f ctxclds"
lemma cl_f_list_map: "map (case_fd (\<lambda>cl f. f)) (map (\<lambda>(x, y). fd_def x y) cl_f_list) = map (\<lambda>(cl_XXX, f_XXX). f_XXX) cl_f_list"
by (induct cl_f_list, auto)

lemma fip_ind_to_f: "\<forall>fs. fields_in_path clds fs \<longrightarrow> fields_in_path_f clds = fs"
apply(induct clds)
 apply(clarsimp, erule fields_in_path.cases) apply(simp) apply(clarsimp)
apply(clarsimp)
apply(erule fields_in_path.cases) apply(simp) by(clarsimp simp add: cl_f_list_map)

lemma fd_map_split: "map (case_fd (\<lambda>cl f. f)) (map (\<lambda>(x, y). fd_def x y) list) = map (\<lambda>(cl, f). f) list"
apply(induct list) apply(simp) apply(clarsimp) done

lemma fd_map_split': "map (\<lambda>(x, y). fd_def x y) (map (case_fd Pair) list) = list"
apply(induct list) apply(simp split: fd.splits)+ done

lemma fd_map_split'': "map ((\<lambda>(x, y). fd_def x y) \<circ> case_fd Pair) list = list"
apply(induct list)  apply(simp split: fd.splits)+ done

lemma [simp]: "\<forall>fs. (fields_in_path ctxclds fs) = (fields_in_path_f ctxclds = fs)"
apply(induct ctxclds)
 apply(rule) apply(rule)
  apply(force elim: fields_in_path.cases)
 apply(simp add: fip_emptyI)
apply(clarsimp)
apply(rule)
 apply(erule fields_in_path.cases)
  apply(simp)
 apply(simp add: fip_ind_to_f fd_map_split)
apply(clarsimp)
apply(rule_tac cld = b and ctxcld_list = ctxclds
           and cl_f_list = "map (case_fd (\<lambda>cl f. (cl, f))) (class_fields_f b)" in fip_consI[simplified])
  apply(simp add: fd_map_split'')
 apply(simp add: fd_map_split')
apply(clarsimp split: fd.splits)
done

definition
fields_f :: "P \<Rightarrow> ty \<Rightarrow> fs option"
where
"fields_f P ty =
  (case find_path_ty_f P ty of None \<Rightarrow> None | Some ctxclds \<Rightarrow>
    Some (fields_in_path_f ctxclds))"
lemma [simp]: "\<forall>fs_opt. (fields P ty fs_opt) = (fields_f P ty = fs_opt)"
apply(rule) apply(rule)
 apply(case_tac fs_opt)
  apply(clarsimp) apply(erule fields.cases)
   apply(clarsimp) apply(simp add: fields_f_def)
  apply(clarsimp)
 apply(erule fields.cases)
  apply(simp)
 apply(clarsimp) apply(simp add: fields_f_def)
 apply(simp add: fields_f_def) apply(case_tac "find_path_ty_f P ty") apply(simp) apply(simp add: fields_noneI[simplified])
apply(clarsimp) apply(case_tac "find_path_ty_f P ty") apply(simp) apply(simp) apply(clarsimp)
apply(rule fields_someI) apply(simp) apply(simp)
done

primrec
methods_in_path_f :: "clds \<Rightarrow> meths"
where
"methods_in_path_f []         = []" |
"methods_in_path_f (cld#clds) =
  map (\<lambda>md. case md of meth_def_def meth_sig meth_body \<Rightarrow>
         case meth_sig of meth_sig_def cl meth vds \<Rightarrow> meth)
              (class_methods_f cld) @ methods_in_path_f clds"

lemma meth_def_map[THEN mp]:
  "(\<forall>x \<in> set list. (\<lambda>(md, cl, m, vds, mb). md = meth_def_def (meth_sig_def cl m vds) mb) x)
     \<longrightarrow> map (case_meth_def (\<lambda>ms mb. case ms of meth_sig_def cl m vds \<Rightarrow> m)) (map (\<lambda>(md, cl, m, vds, mb). md) list) = map (\<lambda>(md, cl, m, vds, mb). m) list"
by (induct list, auto)

lemma meth_def_map':
  "map ((\<lambda>(md, cl, m, vds, mb). md) \<circ> (\<lambda>md. case md of meth_def_def (meth_sig_def cl m vds) mb \<Rightarrow> (md, cl, m, vds, mb))) list = list"
apply(induct list) by (auto split: meth_def.splits meth_sig.splits)

lemma [simp]: "\<forall>meths. (methods_in_path clds meths) = (methods_in_path_f clds = meths)"
apply(induct clds)
 apply(clarsimp) apply(rule)
  apply(erule methods_in_path.cases) apply(simp) apply(clarsimp)
 apply(clarsimp) apply(rule mip_emptyI)
apply(clarsimp) apply(rule)
 apply(erule methods_in_path.cases) apply(simp)
 apply(force)

apply(rule_tac
  meth_def_cl_meth_vds_meth_body_list =
   "(case a of cld_def dcl cl fds mds \<Rightarrow>
    (map (\<lambda>md. (case md of meth_def_def ms mb \<Rightarrow>
               (case ms of meth_sig_def cl m vds \<Rightarrow> (md, cl, m, vds, mb)))) mds))" in
  mip_consI[simplified])
   apply(clarsimp) apply(case_tac a) apply(simp add: class_methods_f_def meth_def_map')
  apply(clarsimp) apply(clarsimp split: meth_def.splits meth_sig.splits)
 apply(simp)
apply(clarsimp) apply(case_tac a) apply(clarsimp simp add: class_methods_f_def split: meth_def.splits meth_sig.splits)
done

definition
methods_f :: "P \<Rightarrow> ty \<Rightarrow> meths option"
where
"methods_f P ty =
  (case find_path_ty_f P ty of None \<Rightarrow> None | Some ctxclds \<Rightarrow>
    Some (methods_in_path_f (map (\<lambda>(ctx, cld). cld) ctxclds)))"
lemma [simp]: "(methods P ty meths) = (methods_f P ty = Some meths)"
apply(rule)
 apply(erule methods.cases) apply(clarsimp simp add: methods_f_def)
apply(simp add: methods_f_def) apply(split option.splits) apply(simp)
apply(clarsimp) apply(rule methods_methodsI) apply(simp) apply(clarsimp)
done

primrec
ftype_in_fds_f :: "P \<Rightarrow> ctx \<Rightarrow> fds \<Rightarrow> f \<Rightarrow> ty_opt_bot"
where
"ftype_in_fds_f P ctx []       f = ty_opt_bot_opt None" |
"ftype_in_fds_f P ctx (fd#fds) f =
  (case fd of fd_def cl f' \<Rightarrow> (if f = f' then
  (case find_type_f P ctx cl of None \<Rightarrow> ty_opt_bot_bot | Some ty \<Rightarrow>
     ty_opt_bot_opt (Some ty)) else ftype_in_fds_f P ctx fds f))"
lemma [simp]: "(ftype_in_fds P ctx fds f ty_opt) = (ftype_in_fds_f P ctx fds f = ty_opt)"
apply(rule)
 apply(induct fds) apply(erule ftype_in_fds.cases) apply(simp) apply(simp) apply(simp) apply(simp)
 apply(erule ftype_in_fds.cases) apply(simp) apply(simp) apply(simp) apply(clarsimp)
apply(induct fds)
 apply(clarsimp) apply(rule ftif_emptyI)
apply(rename_tac fd fds) apply(case_tac fd, rename_tac cl f', clarsimp) apply(rule)
 apply(clarsimp) apply(case_tac "find_type_f P ctx cl")
  apply(simp add: ftif_cons_botI[simplified])
 apply(simp add: ftif_cons_trueI[simplified])
apply(force intro: ftif_cons_falseI[simplified])
done

primrec
ftype_in_path_f :: "P \<Rightarrow> ctxclds \<Rightarrow> f \<Rightarrow> ty_opt"
where
"ftype_in_path_f P []               f = None" |
"ftype_in_path_f P (ctxcld#ctxclds) f =
  (case ctxcld of (ctx, cld) \<Rightarrow>
  (case ftype_in_fds_f P ctx (class_fields_f cld) f of
     ty_opt_bot_bot \<Rightarrow> None | ty_opt_bot_opt ty_opt \<Rightarrow>
  (case ty_opt of Some ty \<Rightarrow> Some ty | None \<Rightarrow>
     ftype_in_path_f P ctxclds f)))"
lemma [simp]: "(ftype_in_path P ctxclds f ty_opt) = (ftype_in_path_f P ctxclds f = ty_opt)"
apply(rule)
 apply(induct rule: ftype_in_path.induct) apply(simp+)
apply(induct ctxclds) apply(simp) apply(rule ftip_emptyI)
apply(hypsubst_thin)
apply(clarsimp) apply(case_tac "ftype_in_fds_f P a (class_fields_f b) f")
 apply(rename_tac ty_opt) apply(case_tac ty_opt)
  apply(simp add: ftip_cons_falseI[simplified])
 apply(simp add: ftip_cons_trueI[simplified])
apply(simp add: ftip_cons_botI[simplified])
done

definition
ftype_f :: "P \<Rightarrow> ty \<Rightarrow> f \<Rightarrow> ty_opt"
where
"ftype_f P ty f =
  (case find_path_ty_f P ty of None \<Rightarrow> None | Some ctxclds \<Rightarrow>
     ftype_in_path_f P ctxclds f)"
lemma [simp]: "(ftype P ty f ty') = (ftype_f P ty f = Some ty')"
apply(rule)
 apply(induct rule: ftype.induct) apply(clarsimp simp add: ftype_f_def)
apply(clarsimp simp add: ftype_f_def split: option.splits) apply(rule ftypeI) apply(simp+)
done

primrec
find_meth_def_in_list_f :: "meth_defs \<Rightarrow> meth \<Rightarrow> meth_def_opt"
where
"find_meth_def_in_list_f []       m = None" |
"find_meth_def_in_list_f (md#mds) m =
  (case md of meth_def_def ms mb \<Rightarrow>
  (case ms of meth_sig_def cl m' vds \<Rightarrow>
  (if m = m' then Some md else find_meth_def_in_list_f mds m)))"
lemma [simp]: "(find_meth_def_in_list mds m md_opt) = (find_meth_def_in_list_f mds m = md_opt)"
apply(rule)
 apply(induct rule: find_meth_def_in_list.induct) apply(simp+)
apply(induct mds) apply(simp) apply(rule fmdil_emptyI)
apply(clarsimp) apply(clarsimp split: meth_def.split meth_sig.split) apply(rule)
 apply(clarsimp) apply(rule fmdil_cons_trueI[simplified]) apply(force)
apply(clarsimp) apply(rule fmdil_cons_falseI[simplified]) apply(force+)
done

primrec
find_meth_def_in_path_f :: "ctxclds \<Rightarrow> meth \<Rightarrow> ctxmeth_def_opt"
where
fmdip_empty: "find_meth_def_in_path_f []               m = None" |
fmdip_cons:  "find_meth_def_in_path_f (ctxcld#ctxclds) m =
  (case ctxcld of (ctx, cld) \<Rightarrow>
  (case find_meth_def_in_list_f (class_methods_f cld) m of
    Some md \<Rightarrow> Some (ctx, md) |
    None \<Rightarrow> find_meth_def_in_path_f ctxclds m))"
lemma [simp]: "(find_meth_def_in_path ctxclds m ctxmeth_def_opt) = (find_meth_def_in_path_f ctxclds m = ctxmeth_def_opt)"
apply(rule)
 apply(induct rule: find_meth_def_in_path.induct) apply(simp+)
apply(induct ctxclds) apply(simp) apply(rule fmdip_emptyI)
apply(clarsimp) apply(case_tac "find_meth_def_in_list_f (class_methods_f b) m") apply(clarsimp)
apply(simp add: fmdip_cons_falseI[simplified])
apply(simp add: fmdip_cons_trueI[simplified])
done

definition
find_meth_def_f :: "P \<Rightarrow> ty \<Rightarrow> meth \<Rightarrow> ctxmeth_def_opt"
where
"find_meth_def_f P ty m =
  (case find_path_ty_f P ty of None \<Rightarrow> None | Some ctxclds \<Rightarrow>
    find_meth_def_in_path_f ctxclds m)"
lemma [simp]: "(find_meth_def P ty m ctxmd_opt) = (find_meth_def_f P ty m = ctxmd_opt)"
apply(rule)
 apply(induct rule: find_meth_def.induct) apply(simp add: find_meth_def_f_def)+
apply(clarsimp simp add: find_meth_def_f_def split: option.splits)
apply(simp add: fmd_nullI)
apply(simp add: fmd_optI)
done

primrec
lift_opts :: "'a option list \<Rightarrow> 'a list option"
where
"lift_opts []         = Some []" |
"lift_opts (opt#opts) =
  (case opt of None \<Rightarrow> None | Some v \<Rightarrow>
  (case lift_opts opts of None \<Rightarrow> None | Some vs \<Rightarrow> Some (v#vs)))"

definition
mtype_f :: "P \<Rightarrow> ty \<Rightarrow> meth \<Rightarrow> mty option"
where
"mtype_f P ty m =
  (case find_meth_def_f P ty m of None \<Rightarrow> None | Some (ctx, md) \<Rightarrow>
  (case md of meth_def_def ms mb \<Rightarrow>
  (case ms of meth_sig_def cl m' vds \<Rightarrow>
  (case find_type_f P ctx cl of None \<Rightarrow> None | Some ty' \<Rightarrow>
  (case lift_opts (map (\<lambda>vd. case vd of vd_def clk vark \<Rightarrow>
    find_type_f P ctx clk) vds) of None \<Rightarrow> None | Some tys \<Rightarrow>
      Some (mty_def tys ty'))))))"

lemma lift_opts_ind[rule_format]:
  "(\<forall>x\<in>set list. (\<lambda>(cl, var, ty). find_type_f P ctx cl = Some ty) x)
       \<longrightarrow> lift_opts (map (case_vd (\<lambda>clk vark. find_type_f P ctx clk) \<circ> (\<lambda>(cl, var, ty). vd_def cl var)) list) = Some (map (\<lambda>(cl, var, ty). ty) list)"
by (induct list, auto)

lemma find_md_m_match'[rule_format]:
  "find_meth_def_in_list_f mds m = Some (meth_def_def (meth_sig_def cl m' vds) mb) \<longrightarrow> m' = m"
apply(induct mds) apply(simp) apply(clarsimp split: meth_def.splits meth_sig.splits) done

lemma find_md_m_match:
  "find_meth_def_in_path_f path m = Some (ctx, meth_def_def (meth_sig_def cl m' vds) mb) \<longrightarrow> m' = m"
apply(induct path) apply(simp) apply(clarsimp split: option.splits) by(rule find_md_m_match')

lemma vds_map_length:
  "length (map (case_vd (\<lambda>clk vark. find_type_f P ctx clk)) vds) = length vds"
by (induct vds, auto)

lemma lift_opts_length[rule_format]:
  "\<forall>tys. lift_opts ty_opts = Some tys \<longrightarrow> length ty_opts = length tys"
apply(induct ty_opts) apply(simp) by(clarsimp split: option.splits)

lemma vds_tys_length_eq[rule_format]:
  "lift_opts (map (case_vd (\<lambda>clk vark. find_type_f P ctx clk)) vds) = Some tys \<longrightarrow> length vds = length tys"
apply(rule) apply(drule lift_opts_length) apply(simp add: vds_map_length) done

lemma vds_tys_length_eq'[rule_format]:
  "\<forall>tys. length vds = length tys \<longrightarrow> vds = map (\<lambda>(cl, var, ty). vd_def cl var) (map (\<lambda>(vd, ty). case vd of vd_def cl var \<Rightarrow> (cl, var, ty)) (zip vds tys))"
apply(induct vds) apply(simp) apply(clarsimp) apply(case_tac a) apply(clarsimp)
apply(case_tac tys) apply(simp) apply(clarsimp) done

lemma vds_tys_length_eq''[rule_format]:
  "\<forall>vds. length vds = length tys \<longrightarrow> tys = map ((\<lambda>(cl, var, ty). ty) \<circ> (\<lambda>(vd, ty). case vd of vd_def cl var \<Rightarrow> (cl, var, ty))) (zip vds tys)"
apply(induct tys) apply(simp) apply(clarsimp) apply(case_tac vds) apply(clarsimp) apply(clarsimp)
apply(split vd.splits) apply(simp) done

lemma lift_opts_find_type[rule_format]:
  "\<forall>tys. lift_opts (map (case_vd (\<lambda>clk vark. find_type_f P ctx clk)) vds) = Some tys
      \<longrightarrow> (\<forall>(vd, ty) \<in> set (zip vds tys). case vd of vd_def cl var \<Rightarrow> find_type_f P ctx cl = Some ty)"
apply(induct vds) apply(simp) apply(clarsimp split: vd.splits option.splits) apply(rename_tac cl' var)
apply(drule_tac x = "(vd_def cl' var, b)" in bspec, simp) apply(force) done

lemma [simp]: "(mtype P ty m mty) = (mtype_f P ty m = Some mty)"
apply(rule)
 apply(induct rule: mtype.induct) apply(clarsimp simp add: mtype_f_def)
 apply(split option.splits) apply(rule) apply(clarsimp)
 apply(rule_tac x = "map (\<lambda>(cl, var, ty). ty) cl_var_ty_list" in exI)
 apply(simp add: lift_opts_ind) apply(clarsimp) apply(simp add: lift_opts_ind)
apply(clarsimp simp add: mtype_f_def split: option.splits meth_def.splits meth_sig.splits)
apply(rename_tac ctx mb cl m' vds ty' tys)
apply(rule_tac ctx = ctx and cl = cl and meth_body = mb and ty' = ty'
           and cl_var_ty_list = "map (\<lambda>(vd, ty). case vd of vd_def cl var \<Rightarrow> (cl, var, ty)) (zip vds tys)"
           and meth_def = "meth_def_def (meth_sig_def cl m' vds) mb" in mtypeI[simplified])
 apply(simp) apply(clarsimp) apply(rule) apply(clarsimp simp add: find_meth_def_f_def split: option.splits)
 apply(simp add: find_md_m_match) apply(drule vds_tys_length_eq) apply(frule vds_tys_length_eq') apply(clarsimp)
 apply(simp) apply(clarsimp) apply(split vd.splits) apply(clarsimp) apply(drule lift_opts_find_type) apply(simp)
 apply(clarsimp)
apply(clarsimp) apply(drule vds_tys_length_eq) apply(simp add: vds_tys_length_eq'')
done

definition
is_sty_one :: "P \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool option"
where
"is_sty_one P ty ty' =
  (case find_path_ty_f P ty of None \<Rightarrow> None | Some ctxclds \<Rightarrow>
  (case ty' of ty_top \<Rightarrow> Some True | ty_def ctx' dcl' \<Rightarrow>
    Some ((ctx', dcl') : set (map (\<lambda>(ctx, cld). (ctx, class_name_f cld)) ctxclds)) ))"

lemma class_name_mem_map[rule_format]:
"(ctx, cld, class_name_f cld) \<in> set ctx_cld_dcl_list
       \<Longrightarrow> (ctx, class_name_f cld)
          \<in> ((\<lambda>(ctx, cld). (ctx, class_name_f cld)) \<circ> (\<lambda>(ctx, cld, dcl). (ctx, cld))) `
            set ctx_cld_dcl_list"
by (induct ctx_cld_dcl_list, auto)

lemma map_map_three:
  " ctxclds = map ((\<lambda>(ctx, cld, dcl). (ctx, cld)) \<circ> (\<lambda>(ctx, cld). (ctx, cld, class_name_f cld))) ctxclds"
by (induct ctxclds, auto)

lemma mem_el_map[rule_format]:
  "(ctx, dcl) \<in> set ctxclds
       \<Longrightarrow> (ctx, class_name_f dcl)
          \<in> (\<lambda>(ctx_XXX, cld_XXX, y). (ctx_XXX, y)) `
            set (map (\<lambda>(ctx, cld). (ctx, cld, class_name_f cld)) ctxclds)"
by (induct ctxclds, auto)

lemma [simp]: "(sty_one P ty ty') = (is_sty_one P ty ty' = Some True)"
apply(rule)
 apply(induct rule: sty_one.induct)
  apply(simp add: is_sty_one_def)
 apply(clarsimp simp add: is_sty_one_def) apply(rename_tac ctx cld dcl)
 apply(drule_tac x = "(ctx, cld, dcl)" in bspec, simp) apply(clarsimp)
 apply(simp add: class_name_mem_map)
apply(clarsimp simp add: is_sty_one_def split: option.splits ty.splits)
 apply(simp add: sty_objI)
apply(rename_tac ctxclds ctx dcl)
apply(rule_tac ctx_cld_dcl_list = "map (\<lambda>(ctx, cld). (ctx, cld, class_name_f cld)) ctxclds" in sty_dclI[simplified])
  apply(clarsimp) apply(rule map_map_three)
 apply(force)
apply(rule mem_el_map, assumption)
done

lemma path_append[rule_format]:
  "find_path_rec_f P ctx cl path' = Some path \<Longrightarrow> \<exists>path''. path = path' @ path''"
apply(induct rule: find_path_rec_f.induct)
 apply(clarsimp)
apply(force split: if_split_asm option.splits)
done

lemma all_in_path_found'[rule_format]:
  "find_path_rec_f P ctx cl path' = Some path \<longrightarrow>
      (\<forall>ctxcld \<in> set path. ctxcld \<in> set path' \<or> (\<exists>ctx' fqn'. find_cld_f P ctx' fqn' = Some ctxcld))"
apply(induct rule: find_path_rec_f.induct)
 apply(clarsimp)
apply(rule)
apply(force split: if_split_asm option.splits)
done

lemma all_in_path_found:
  "\<lbrakk>find_path_f P ctx cl = Some path; ctxcld \<in> set path\<rbrakk> \<Longrightarrow> \<exists>ctx' fqn'. find_cld_f P ctx' fqn' = Some ctxcld"
by (unfold find_path_f_def, simp only: all_in_path_found'[of _ _ _ "[]", simplified])

lemma fpr_target_is_head':
  "find_path_rec_f P ctx cl path' = Some path \<longrightarrow>
     (\<forall>fqn ctxcld. cl = cl_fqn fqn \<and> find_cld_f P ctx fqn = Some ctxcld \<longrightarrow>
          (\<exists>path''. path = path' @ ctxcld # path''))"
apply(induct_tac P ctx cl path' rule: find_path_rec_f.induct)
 apply(simp)
apply(clarsimp split: if_split_asm option.splits)
apply(case_tac "superclass_name_f b") apply(clarsimp)
apply(clarsimp split: if_split_asm option.splits)
apply(force)
done

lemma fpr_target_is_head:
  "find_path_f P ctx (cl_fqn fqn) = Some path \<Longrightarrow> \<exists>ctxcld. find_cld_f P ctx fqn = Some ctxcld \<and> (\<exists>path''. path = ctxcld # path'')"
apply(unfold find_path_f_def) apply(frule fpr_target_is_head'[of _ _ _ "[]", THEN mp]) apply(clarsimp split: option.splits) done

lemma fpr_sub_path':
  "find_path_rec_f P ctx cl path' = Some path \<longrightarrow>
     (\<forall>fqn ctxcld path'' path_fqn.
         cl = cl_fqn fqn \<and> find_cld_f P ctx fqn = Some ctxcld \<and>
         find_path_rec_f P (fst ctxcld) (superclass_name_f (snd ctxcld)) path'' = Some path_fqn \<longrightarrow>
              (\<exists>path'''. path_fqn = path'' @ path''' \<and> path = path' @ ctxcld # path'''))"
apply(induct_tac P ctx cl path' rule: find_path_rec_f.induct)
 apply(simp)
apply(clarsimp split: if_split_asm option.splits)
apply(case_tac "superclass_name_f b") apply(simp add: find_path_f_def)
apply(clarsimp split: if_split_asm option.splits)
apply(frule_tac path = path in path_append) apply(clarsimp) apply(force)
done

lemma fpr_sub_path:
  "\<lbrakk>find_path_f P ctx (cl_fqn fqn) = Some path; find_cld_f P ctx fqn = Some ctxcld;
    find_path_f P (fst ctxcld) (superclass_name_f (snd ctxcld)) = Some path'\<rbrakk>
       \<Longrightarrow> path = ctxcld # path'"
by (unfold find_path_f_def, force intro: fpr_sub_path'[rule_format, of _ _ _ "[]" _ _ _ "[]", simplified])

lemma fpr_sub_path_simp:
  "\<lbrakk>find_path_rec_f P ctx (superclass_name_f cld) path'' = Some path_fqn; find_cld_f P ctx fqn = Some (ctx, cld); acyclic_clds P;
    find_path_rec_f P ctx (superclass_name_f cld) (path' @ [(ctx, cld)]) = Some path\<rbrakk>
       \<Longrightarrow> \<exists>path'''. path_fqn = path'' @ path''' \<and> path = path' @ (ctx, cld) # path'''"
apply(cut_tac P = P and ctx = ctx and cl = "cl_fqn fqn" and path' = path' and path = path in fpr_sub_path')
apply(clarsimp split: option.splits if_split_asm)
done

lemma fpr_same_suffix'[rule_format]:
  "find_path_rec_f P ctx cl prefix = Some path \<longrightarrow>
     (\<forall>suffix prefix'. path = prefix @ suffix \<longrightarrow>
          find_path_rec_f P ctx cl prefix' = Some (prefix' @ suffix))"
apply(induct_tac P ctx cl prefix rule: find_path_rec_f.induct)
 apply(clarsimp)
apply(clarsimp split: option.splits)
apply(frule path_append) apply(force)
done

lemma fpr_same_suffix:
  "find_path_rec_f P ctx cl prefix = Some path \<longrightarrow>
     (\<forall>suffix prefix' suffix'. path = prefix @ suffix \<and>
          find_path_rec_f P ctx cl prefix' = Some (prefix' @ suffix')
             \<longrightarrow> suffix = suffix')"
apply(induct_tac P ctx cl prefix rule: find_path_rec_f.induct)
 apply(clarsimp)
by (metis fpr_same_suffix' option.inject same_append_eq)

lemma fpr_mid_path'[rule_format]:
  "find_path_rec_f P ctx cl path' = Some path \<longrightarrow>
     (\<forall>ctxcld \<in> set path.
         ctxcld \<in> set path' \<or>
         (\<forall>path_fqn. find_path_rec_f P (fst ctxcld) (cl_fqn (fqn_def (class_name_f (snd ctxcld)))) path'' = Some path_fqn \<longrightarrow>
              (\<forall>path'''. path_fqn = path'' @ path''' \<longrightarrow> (\<exists>path_rest. path = path_rest @ path'''))))"
apply(induct_tac P ctx cl path' rule: find_path_rec_f.induct)
 apply(simp)
apply(clarsimp split: option.splits)
apply(frule find_cld_name_eq) apply(clarsimp)
apply(rename_tac path' ctx' cld' cld'' ctx'' path''' cl fds mds)
apply(subgoal_tac "find_path_rec_f P ctx' (superclass_name_f cld') (path' @ [(ctx', cld')]) = Some path \<longrightarrow>
              (\<forall>ctxcld\<in>set path.
                  ctxcld = (ctx', cld') \<or>
                  ctxcld \<in> set path' \<or>
                  (\<forall>path_fqn. case_option None (case_prod (\<lambda>ctx' cld. find_path_rec_f P ctx' (superclass_name_f cld) (path'' @ [(ctx', cld)])))
                               (find_cld_f P (fst ctxcld) (fqn_def (class_name_f (snd ctxcld)))) =
                              Some path_fqn \<longrightarrow>
                              (\<forall>path'''. path_fqn = path'' @ path''' \<longrightarrow> (\<exists>path_rest. path = path_rest @ path'''))))")
 apply(erule impE) apply simp
 apply(drule_tac x = "(ctx'', cld'')" in bspec, simp) apply(clarsimp)
 apply(simp add: superclass_name_f_def)
 apply(case_tac cld') apply(rename_tac dcl' cl' fds' mds') apply(clarsimp simp add: class_name_f_def)
 apply(case_tac fqn) apply(rename_tac dcl'') apply(clarsimp)
 apply(frule find_cld_name_eq) apply(clarsimp)
 apply(frule path_append) apply(frule_tac path = "path'' @ path'''" in path_append) apply(clarsimp)
 apply(rule_tac x = path' in exI) apply(clarsimp)
 apply(frule_tac suffix = path''a and prefix' = "path'' @ [(ctx', cld_def dcl' cl' fds' mds')]" and
                suffix' = path''aa in fpr_same_suffix[rule_format]) apply(simp)
 apply(force)
apply(simp)
done

lemma fpr_mid_path:
  "\<lbrakk>find_path_f P ctx cl = Some path; (ctx', cld') \<in> set path;
    find_path_f P ctx' (cl_fqn (fqn_def (class_name_f cld'))) = Some path'\<rbrakk>
       \<Longrightarrow> \<exists>path''. path = path'' @ path'"
apply(cut_tac  P = P and ctx = ctx and cl = cl and path' = "[]" and path = path and ctxcld = "(ctx', cld')" and path'' = "[]" in fpr_mid_path')
apply(unfold find_path_f_def, assumption) apply(assumption) apply(simp)
done

lemma fpr_first_in_path'[rule_format]:
  "find_path_rec_f P ctx cl path' = Some path \<longrightarrow>
      (\<forall>fqn ctxcld. cl = cl_fqn fqn \<and> find_cld_f P ctx fqn = Some ctxcld \<longrightarrow> ctxcld \<in> set path)"
apply(case_tac cl)
 apply(simp)
apply(clarsimp) apply(drule path_append) apply(force)
done

lemma fpr_first_in_path:
  "\<lbrakk>find_path_f P ctx (cl_fqn fqn) = Some path; find_cld_f P ctx fqn = Some ctxcld\<rbrakk> \<Longrightarrow> ctxcld \<in> set path"
by (unfold find_path_f_def, force intro: fpr_first_in_path'[of _ _ _ "[]", simplified])

lemma cld_for_path:
  "find_path_f P ctx (cl_fqn fqn) = Some path \<Longrightarrow> \<exists>ctxcld. find_cld_f P ctx fqn = Some ctxcld"
apply(unfold find_path_f_def) apply(clarsimp split: if_split_asm option.splits) done

lemma ctx_cld_ctx_dcl[rule_format]:
  "(ctx, cld_def dcl cl fds mds) \<in> set path \<longrightarrow> (ctx, dcl) \<in> (\<lambda>(ctx, cld). (ctx, class_name_f cld)) ` set path"
by (induct path, auto simp add: class_name_f_def)

lemma ctx_dcl_ctx_cld[rule_format]:
  "(ctx, dcl) \<in> (\<lambda>(ctx, cld). (ctx, class_name_f cld)) ` set path \<longrightarrow> (\<exists>cl fds mds. (ctx, cld_def dcl cl fds mds) \<in> set path)"
apply(induct path) apply(simp)
apply(auto) apply(case_tac b) apply(force simp add: class_name_f_def)
done

lemma ctx_dcl_mem_path:
  "find_path_f P ctx (cl_fqn (fqn_def dcl)) = Some path \<Longrightarrow> (ctx, dcl) \<in> (\<lambda>(ctx, cld). (ctx, class_name_f cld)) ` set path"
apply(frule cld_for_path) apply(erule exE)
apply(frule fpr_first_in_path) apply(assumption)
apply(frule find_cld_name_eq) apply(elim exE)
apply(clarsimp simp add: ctx_cld_ctx_dcl)
done

lemma sty_reflexiveI:
  "is_sty_one P ty ty' = Some True \<Longrightarrow> is_sty_one P ty ty = Some True"
apply(simp add: is_sty_one_def split: option.splits) apply(case_tac ty) apply(simp) apply(clarsimp)
apply(drule ctx_dcl_mem_path) apply(force)
done

lemma sty_transitiveI:
  "\<lbrakk>is_sty_one P ty ty' = Some True; is_sty_one P ty' ty'' = Some True\<rbrakk>
       \<Longrightarrow> is_sty_one P ty ty'' = Some True"
apply(clarsimp simp add: is_sty_one_def split: ty.splits option.splits)
apply(rename_tac path ctx dcl path' ctx' dcl')
apply(case_tac ty) apply(simp) apply(clarsimp) apply(rename_tac ctx dcl ctx' cld' ctx'' cld'')
apply(frule fpr_mid_path) apply(simp) apply(simp) apply(force)
done

definition
is_sty_many :: "P \<Rightarrow> tys \<Rightarrow> tys \<Rightarrow> bool option"
where
"is_sty_many P tys tys' =
  (if length tys \<noteq> length tys' then None else
  (case lift_opts (map (\<lambda>(ty, ty'). is_sty_one P ty ty') (zip tys tys'))
     of None \<Rightarrow> None | Some bools \<Rightarrow> Some (list_all id bools)))"

lemma lift_opts_exists:
  "\<forall>x\<in>set ty_ty'_list. (\<lambda>(ty, ty'). is_sty_one P ty ty' = Some True) x \<Longrightarrow> \<exists>bools. lift_opts (map (\<lambda>(ty, ty'). is_sty_one P ty ty') ty_ty'_list) = Some bools"
by (induct ty_ty'_list, auto)

lemma lift_opts_all_true[rule_format]:
  "\<forall>bools. (\<forall>x\<in>set ty_ty'_list. (\<lambda>(ty, ty'). is_sty_one P ty ty' = Some True) x) \<and>
            lift_opts (map (\<lambda>(ty, ty'). is_sty_one P ty ty') ty_ty'_list) = Some bools
                  \<longrightarrow> list_all id bools"
by (induct ty_ty'_list, auto split: option.splits)

lemma tys_tys'_list: "\<And>bools ty ty'. \<lbrakk>lift_opts (map (\<lambda>(x, y). is_sty_one P x y) tys_tys'_list) = Some bools; length tys = length tys'; list_all id bools; (ty, ty') \<in> set tys_tys'_list\<rbrakk> \<Longrightarrow> is_sty_one P ty ty' = Some True"
apply(induct tys_tys'_list)
 apply(simp)
apply(clarsimp split: option.splits)
by force

lemma [simp]: "(sty_many P tys tys') = (is_sty_many P tys tys' = Some True)"
apply(rule)
 apply(erule sty_many.cases) apply(clarsimp simp add: is_sty_many_def split: option.splits) apply(rule)
  apply(simp add: lift_opts_exists)
 apply(force intro: lift_opts_all_true)
apply(clarsimp simp add: is_sty_many_def split: option.splits if_split_asm)
apply(rule_tac ty_ty'_list = "zip tys tys'" in sty_manyI)
  apply(simp add: map_fst_zip[THEN sym])
 apply(simp add: map_snd_zip[THEN sym])
apply(clarsimp)
apply(simp add: tys_tys'_list)
done

(* TODO: here will go all the other definitions for functions equivalent to
   relations concerning well-formedness *)

definition
tr_x :: "T \<Rightarrow> x \<Rightarrow> x"
where
"tr_x T x = (case T x of None \<Rightarrow> x | Some x' \<Rightarrow> x')"

definition
tr_var :: "T \<Rightarrow> var \<Rightarrow> var"
where
"tr_var T var = (case tr_x T (x_var var) of x_this \<Rightarrow> var | x_var var' \<Rightarrow> var')"

primrec
tr_s_f  :: "T \<Rightarrow> s \<Rightarrow> s" and
tr_ss_f :: "T \<Rightarrow> s list \<Rightarrow> s list"
where
"tr_s_f T (s_block ss)        = s_block (tr_ss_f T ss)" |
"tr_s_f T (s_ass var x)       = s_ass (tr_var T var) (tr_x T x)" |
"tr_s_f T (s_read var x f)    = s_read (tr_var T var) (tr_x T x) f" |
"tr_s_f T (s_write x f y)     = s_write (tr_x T x) f (tr_x T y)" |
"tr_s_f T (s_if x y s1 s2)    = s_if (tr_x T x) (tr_x T y) (tr_s_f T s1) (tr_s_f T s2)" |
"tr_s_f T (s_call var x m ys) = s_call (tr_var T var) (tr_x T x) m (map (tr_x T) ys)" |
"tr_s_f T (s_new var ctx cl)  = s_new (tr_var T var) ctx cl" |

"tr_ss_f T [] = []" |
"tr_ss_f T (s#ss) = tr_s_f T s # tr_ss_f T ss"

lemma [simp]: "(\<forall>x\<in>set s_s'_list. case x of (s_XXX, s_') \<Rightarrow> tr_s T s_XXX s_' \<and> tr_s_f T s_XXX = s_') \<longrightarrow>
       tr_ss_f T (map fst s_s'_list) = map snd s_s'_list"
by (induct s_s'_list, auto)

lemma [simp]: "(\<forall>x\<in>set y_y'_list. case_prod (\<lambda>y_XXX. (=) (case T y_XXX of None \<Rightarrow> y_XXX | Some x' \<Rightarrow> x')) x) \<longrightarrow> map (tr_x T) (map fst y_y'_list) = map snd y_y'_list"
apply(induct y_y'_list) apply(simp) apply(clarsimp) apply(simp only: tr_x_def) done

lemma set_zip_tr[simp]: "(s, s') \<in> set (zip ss (tr_ss_f T ss)) \<longrightarrow> s' = tr_s_f T s" by (induct ss, auto)

lemma [iff]: "length ss = length (tr_ss_f T ss)" by (induct ss, auto)

lemma tr_ss_map:
  "tr_ss_f T (map fst s_s'_list) = map snd s_s'_list \<and> (\<forall>x\<in>set s_s'_list. case_prod (tr_s T) x) \<and>
   (a, b) \<in> set s_s'_list \<longrightarrow> tr_s T a (tr_s_f T a)"
apply(induct s_s'_list) by auto

lemma tr_f_to_rel: "\<forall>s'. tr_s_f T s = s' \<longrightarrow> tr_s T s s'"
apply(induct s rule: tr_s_f.induct)
apply(simp)
apply(clarsimp) apply(rule tr_s_var_assignI)
apply(clarsimp simp add: tr_x_def tr_var_def split: option.splits)
apply(simp add: tr_x_def)
apply(clarsimp) apply(rule tr_s_field_readI)
apply(clarsimp simp add: tr_x_def tr_var_def split: option.splits)
apply(simp add: tr_x_def)
apply(clarsimp) apply(rule tr_s_field_writeI)
apply(simp add: tr_x_def) apply(simp add: tr_x_def)
apply(clarsimp simp only: tr_s_f.simps) apply(rule tr_s_ifI)
apply(simp only: tr_x_def) apply(simp only: tr_x_def) apply(simp) apply(simp)
apply(clarsimp) apply(rule tr_s_newI)
apply(clarsimp simp add: tr_x_def tr_var_def split: option.splits)
apply(clarsimp)
apply(rename_tac var x m ys)
apply(cut_tac T = T and var = var and var' = "tr_var T var" and x = x and
              x' = "tr_x T x" and y_y'_list = "zip ys (map (tr_x T) ys)" and
              meth = m in tr_s_mcallI)
apply(clarsimp simp add: tr_x_def tr_var_def split: option.splits)
apply(simp only: tr_x_def) apply(clarsimp simp add: set_zip tr_x_def) apply(simp)
apply(simp)
apply(cut_tac T = T and s_s'_list = "[]" in tr_s_blockI[simplified])
 apply(simp)
apply(clarsimp)
apply(clarsimp) apply(rename_tac s ss)
apply(cut_tac T = T and s_s'_list = "zip (s # ss) (tr_s_f T s # tr_ss_f T ss)" in tr_s_blockI[simplified])
 apply(clarsimp) apply(rename_tac x x')
 apply(frule set_zip_tr[THEN mp]) apply(clarsimp)
 apply(erule in_set_zipE)
 apply(erule_tac ?a1.0="T" and ?a2.0="s_block ss" and ?a3.0="s_block (tr_ss_f T ss)" in tr_s.cases)
 apply(clarsimp)
 apply(rule tr_ss_map[THEN mp], force)
 apply(clarsimp)+
done

lemma tr_rel_f_eq: "((tr_s T s s') = (tr_s_f T s = s'))"
apply(rule)
 apply(erule tr_s.induct)
 apply(force simp add: tr_x_def tr_var_def split: option.splits)+
apply(cut_tac T = T and s = s in tr_f_to_rel) apply(simp)
done

end
