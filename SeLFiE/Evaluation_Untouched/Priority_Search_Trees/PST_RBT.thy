section \<open>Priority Search Trees on top of RBTs\<close>

theory PST_RBT
imports
  "HOL-Data_Structures.Cmp"
  "HOL-Data_Structures.Isin2"
  "HOL-Data_Structures.Lookup2"
  PST_General
begin
  
text \<open>
We obtain a priority search map based on red-black trees via the 
general priority search tree augmentation.

This theory has been derived from the standard Isabelle implementation of red 
black trees in @{session "HOL-Data_Structures"}.
\<close>

subsection \<open>Definitions\<close>

subsubsection \<open>The Code\<close>

datatype tcolor = Red | Black

type_synonym ('k,'p) rbth = "(('k\<times>'p) \<times> (tcolor \<times> ('k \<times> 'p))) tree"

abbreviation R where "R mkp l a r \<equiv> Node l (a, Red,mkp) r"
abbreviation B where "B mkp l a r \<equiv> Node l (a, Black,mkp) r"

abbreviation "mkR \<equiv> mkNode Red"
abbreviation "mkB \<equiv> mkNode Black"

fun baliL :: "('k,'p::linorder) rbth \<Rightarrow> 'k\<times>'p \<Rightarrow> ('k,'p) rbth \<Rightarrow> ('k,'p) rbth" 
  where
  "baliL (R _ (R _ t1 a1 t2) a2 t3) a3 t4 = mkR (mkB t1 a1 t2) a2 (mkB t3 a3 t4)"
| "baliL (R _ t1 a1 (R _ t2 a2 t3)) a3 t4 = mkR (mkB t1 a1 t2) a2 (mkB t3 a3 t4)"
| "baliL t1 a t2 = mkB t1 a t2"

fun baliR :: "('k,'p::linorder) rbth \<Rightarrow> 'k\<times>'p \<Rightarrow> ('k,'p) rbth \<Rightarrow> ('k,'p) rbth" 
  where
"baliR t1 a1 (R _ (R _ t2 a2 t3) a3 t4) = mkR (mkB t1 a1 t2) a2 (mkB t3 a3 t4)" |
"baliR t1 a1 (R _ t2 a2 (R _ t3 a3 t4)) = mkR (mkB t1 a1 t2) a2 (mkB t3 a3 t4)" |
"baliR t1 a t2 = mkB t1 a t2"

fun paint :: "tcolor \<Rightarrow> ('k,'p::linorder) rbth \<Rightarrow> ('k,'p::linorder) rbth" where
"paint c Leaf = Leaf" |
"paint c (Node l (a, (_,mkp)) r) = Node l (a, (c,mkp)) r"

fun baldL :: "('k,'p::linorder) rbth \<Rightarrow> 'k \<times> 'p \<Rightarrow> ('k,'p::linorder) rbth 
    \<Rightarrow> ('k,'p::linorder) rbth" 
where
"baldL (R _ t1 x t2) y t3 = mkR (mkB t1 x t2) y t3" |
"baldL bl x (B _ t1 y t2) = baliR bl x (mkR t1 y t2)" |
"baldL bl x (R _ (B _ t1 y t2) z t3) 
  = mkR (mkB bl x t1) y (baliR t2 z (paint Red t3))" |
"baldL t1 x t2 = mkR t1 x t2"

fun baldR :: "('k,'p::linorder) rbth \<Rightarrow> 'k \<times> 'p \<Rightarrow> ('k,'p::linorder) rbth 
    \<Rightarrow> ('k,'p::linorder) rbth" 
where
"baldR t1 x (R _ t2 y t3) = mkR t1 x (mkB t2 y t3)" |
"baldR (B _ t1 x t2) y t3 = baliL (mkR t1 x t2) y t3" |
"baldR (R _ t1 x (B _ t2 y t3)) z t4 
  = mkR (baliL (paint Red t1) x t2) y (mkB t3 z t4)" |
"baldR t1 x t2 = mkR t1 x t2"

fun combine :: "('k,'p::linorder) rbth \<Rightarrow> ('k,'p::linorder) rbth 
    \<Rightarrow> ('k,'p::linorder) rbth" 
where
"combine Leaf t = t" |
"combine t Leaf = t" |
"combine (R _ t1 a t2) (R _ t3 c t4) =
  (case combine t2 t3 of
     R _ u2 b u3 \<Rightarrow> (mkR (mkR t1 a u2) b (mkR u3 c t4)) |
     t23 \<Rightarrow> mkR t1 a (mkR t23 c t4))" |
"combine (B _ t1 a t2) (B _ t3 c t4) =
  (case combine t2 t3 of
     R _ t2' b t3' \<Rightarrow> mkR (mkB t1 a t2') b (mkB t3' c t4) |
     t23 \<Rightarrow> baldL t1 a (mkB t23 c t4))" |
"combine t1 (R _ t2 a t3) = mkR (combine t1 t2) a t3" |
"combine (R _ t1 a t2) t3 = mkR t1 a (combine t2 t3)"

fun color :: "('k,'p) rbth \<Rightarrow> tcolor" where
"color Leaf = Black" |
"color (Node _ (_, (c,_)) _) = c"


fun upd :: "'a::linorder \<Rightarrow> 'b::linorder \<Rightarrow> ('a,'b) rbth \<Rightarrow> ('a,'b) rbth" where
"upd x y Leaf = mkR Leaf (x,y) Leaf" |
"upd x y (B _ l (a,b) r) = (case cmp x a of
  LT \<Rightarrow> baliL (upd x y l) (a,b) r |
  GT \<Rightarrow> baliR l (a,b) (upd x y r) |
  EQ \<Rightarrow> mkB l (x,y) r)" |
"upd x y (R _ l (a,b) r) = (case cmp x a of
  LT \<Rightarrow> mkR (upd x y l) (a,b) r |
  GT \<Rightarrow> mkR l (a,b) (upd x y r) |
  EQ \<Rightarrow> mkR l (x,y) r)"

definition update :: "'a::linorder \<Rightarrow> 'b::linorder \<Rightarrow> ('a,'b) rbth \<Rightarrow> ('a,'b) rbth" 
where
"update x y t = paint Black (upd x y t)"


fun del :: "'a::linorder \<Rightarrow> ('a,'b::linorder)rbth \<Rightarrow> ('a,'b)rbth" where
"del x Leaf = Leaf" |
"del x (Node l ((a,b), (c,_)) r) = (case cmp x a of
     LT \<Rightarrow> if l \<noteq> Leaf \<and> color l = Black
           then baldL (del x l) (a,b) r else mkR (del x l) (a,b) r |
     GT \<Rightarrow> if r \<noteq> Leaf\<and> color r = Black
           then baldR l (a,b) (del x r) else mkR l (a,b) (del x r) |
  EQ \<Rightarrow> combine l r)"

definition delete :: "'a::linorder \<Rightarrow> ('a,'b::linorder) rbth \<Rightarrow> ('a,'b) rbth" where
"delete x t = paint Black (del x t)"


subsubsection \<open>Invariants\<close>

fun bheight :: "('k,'p) rbth \<Rightarrow> nat" where
"bheight Leaf = 0" |
"bheight (Node l (x, (c,_)) r) = (if c = Black then bheight l + 1 else bheight l)"

fun invc :: "('k,'p) rbth \<Rightarrow> bool" where
"invc Leaf = True" |
"invc (Node l (a, (c,_)) r) =
  (invc l \<and> invc r \<and> (c = Red \<longrightarrow> color l = Black \<and> color r = Black))"

fun invc2 :: "('k,'p) rbth \<Rightarrow> bool" \<comment> \<open>Weaker version\<close> where
"invc2 Leaf = True" |
"invc2 (Node l (a, _) r) = (invc l \<and> invc r)"

fun invh :: "('k,'p) rbth \<Rightarrow> bool" where
"invh Leaf = True" |
"invh (Node l (x, _) r) = (invh l \<and> invh r \<and> bheight l = bheight r)"

definition rbt :: "('k,'p::linorder) rbth \<Rightarrow> bool" where
"rbt t = (invc t \<and> invh t \<and> invpst t \<and> color t = Black)"


subsection \<open>Functional Correctness\<close>

lemma inorder_paint[simp]: "inorder(paint c t) = inorder t"
by(cases t) (auto)

lemma inorder_mkNode[simp]:
  "inorder (mkNode c l a r) = inorder l @ a # inorder r"
by (auto simp: mkNode_def)


lemma inorder_baliL[simp]:
  "inorder(baliL l a r) = inorder l @ a # inorder r"
by(cases "(l,a,r)" rule: baliL.cases) (auto)

lemma inorder_baliR[simp]:
  "inorder(baliR l a r) = inorder l @ a # inorder r"
by(cases "(l,a,r)" rule: baliR.cases) (auto)


lemma inorder_baldL[simp]:
  "inorder(baldL l a r) = inorder l @ a # inorder r"
by (cases "(l,a,r)" rule: baldL.cases) auto

lemma inorder_baldR[simp]:
  "inorder(baldR l a r) = inorder l @ a # inorder r"
by(cases "(l,a,r)" rule: baldR.cases) auto

lemma inorder_combine[simp]:
  "inorder(combine l r) = inorder l @ inorder r"
by (induction l r rule: combine.induct) (auto split: tree.split tcolor.split)

lemma inorder_upd:
  "sorted1(inorder t) \<Longrightarrow> inorder(upd x y t) = upd_list x y (inorder t)"
by(induction x y t rule: upd.induct)
  (auto simp: upd_list_simps)

lemma inorder_update:
  "sorted1(inorder t) \<Longrightarrow> inorder(update x y t) = upd_list x y (inorder t)"
by(simp add: update_def inorder_upd)

lemma inorder_del:
 "sorted1(inorder t) \<Longrightarrow>  inorder(del x t) = del_list x (inorder t)"
by(induction x t rule: del.induct)
  (auto simp: del_list_simps)

lemma inorder_delete:
  "sorted1(inorder t) \<Longrightarrow> inorder(delete x t) = del_list x (inorder t)"
by(simp add: delete_def inorder_del)


subsection \<open>Invariant Preservation\<close>

lemma color_paint_Black: "color (paint Black t) = Black"
by (cases t) auto

theorem rbt_Leaf: "rbt Leaf"
by (simp add: rbt_def)

lemma invc2I: "invc t \<Longrightarrow> invc2 t"
by (cases t rule: invc.cases) simp+

lemma paint_invc2: "invc2 t \<Longrightarrow> invc2 (paint c t)"
by (cases t) auto

lemma invc_paint_Black: "invc2 t \<Longrightarrow> invc (paint Black t)"
by (cases t) auto

lemma invh_paint: "invh t \<Longrightarrow> invh (paint c t)"
by (cases t) auto

lemma invc_mkRB[simp]:
  "invc (mkR l a r) \<longleftrightarrow> invc l \<and> invc r \<and> color l = Black \<and> color r = Black"
  "invc (mkB l a r) \<longleftrightarrow> invc l \<and> invc r"
by (simp_all add: mkNode_def)

lemma color_mkNode[simp]: "color (mkNode c l a r) = c"
by (simp_all add: mkNode_def)


subsubsection \<open>Update\<close>

lemma invc_baliL:
  "\<lbrakk>invc2 l; invc r\<rbrakk> \<Longrightarrow> invc (baliL l a r)"
by (induct l a r rule: baliL.induct) auto

lemma invc_baliR:
  "\<lbrakk>invc l; invc2 r\<rbrakk> \<Longrightarrow> invc (baliR l a r)"
by (induct l a r rule: baliR.induct) auto

lemma bheight_mkRB[simp]:
  "bheight (mkR l a r) = bheight l"
  "bheight (mkB l a r) = Suc (bheight l)"
  by (simp_all add: mkNode_def)

lemma bheight_baliL:
  "bheight l = bheight r \<Longrightarrow> bheight (baliL l a r) = Suc (bheight l)"
by (induct l a r rule: baliL.induct) auto

lemma bheight_baliR:
  "bheight l = bheight r \<Longrightarrow> bheight (baliR l a r) = Suc (bheight l)"
by (induct l a r rule: baliR.induct) auto

lemma invh_mkNode[simp]:
  "invh (mkNode c l a r) \<longleftrightarrow> invh l \<and> invh r \<and> bheight l = bheight r"
by (simp add: mkNode_def)

lemma invh_baliL:
  "\<lbrakk> invh l; invh r; bheight l = bheight r \<rbrakk> \<Longrightarrow> invh (baliL l a r)"
by (induct l a r rule: baliL.induct) auto

lemma invh_baliR:
  "\<lbrakk> invh l; invh r; bheight l = bheight r \<rbrakk> \<Longrightarrow> invh (baliR l a r)"
by (induct l a r rule: baliR.induct) auto


lemma invc_upd: assumes "invc t"
  shows "color t = Black \<Longrightarrow> invc (upd x y t)" "invc2 (upd x y t)"
using assms
by (induct x y t rule: upd.induct) 
   (auto simp: invc_baliL invc_baliR invc2I mkNode_def)

lemma invh_upd: assumes "invh t"
  shows "invh (upd x y t)" "bheight (upd x y t) = bheight t"
using assms
by(induct x y t rule: upd.induct)
  (auto simp: invh_baliL invh_baliR bheight_baliL bheight_baliR)


lemma invpst_paint[simp]: "invpst (paint c t) = invpst t"
by (cases "(c,t)" rule: paint.cases) auto

lemma invpst_baliR: "invpst l \<Longrightarrow> invpst r \<Longrightarrow> invpst (baliR l a r)"
by (cases "(l,a,r)" rule: baliR.cases) auto

lemma invpst_baliL: "invpst l \<Longrightarrow> invpst r \<Longrightarrow> invpst (baliL l a r)"
by (cases "(l,a,r)" rule: baliL.cases) auto

lemma invpst_upd: "invpst t \<Longrightarrow> invpst (upd x y t)"
by (induct x y t rule: upd.induct) (auto simp: invpst_baliR invpst_baliL)


theorem rbt_update: "rbt t \<Longrightarrow> rbt (update x y t)"
by (simp add: invc_upd(2) invh_upd(1) color_paint_Black invc_paint_Black 
  invh_paint rbt_def update_def invpst_upd)


subsubsection \<open>Delete\<close>

lemma bheight_paint_Red:
  "color t = Black \<Longrightarrow> bheight (paint Red t) = bheight t - 1"
by (cases t) auto

lemma invh_baldL_invc:
  "\<lbrakk> invh l;  invh r;  bheight l + 1 = bheight r;  invc r \<rbrakk>
   \<Longrightarrow> invh (baldL l a r) \<and> bheight (baldL l a r) = bheight l + 1"
by (induct l a r rule: baldL.induct)
   (auto simp: invh_baliR invh_paint bheight_baliR bheight_paint_Red)

lemma invh_baldL_Black:
  "\<lbrakk> invh l;  invh r;  bheight l + 1 = bheight r;  color r = Black \<rbrakk>
   \<Longrightarrow> invh (baldL l a r) \<and> bheight (baldL l a r) = bheight r"
by (induct l a r rule: baldL.induct) (auto simp add: invh_baliR bheight_baliR)

lemma invc_baldL: "\<lbrakk>invc2 l; invc r; color r = Black\<rbrakk> \<Longrightarrow> invc (baldL l a r)"
by (induct l a r rule: baldL.induct) (auto simp: invc_baliR invc2I mkNode_def)

lemma invc2_baldL: "\<lbrakk> invc2 l; invc r \<rbrakk> \<Longrightarrow> invc2 (baldL l a r)"
by (induct l a r rule: baldL.induct) 
   (auto simp: invc_baliR paint_invc2 invc2I mkNode_def)

lemma invh_baldR_invc:
  "\<lbrakk> invh l;  invh r;  bheight l = bheight r + 1;  invc l \<rbrakk>
  \<Longrightarrow> invh (baldR l a r) \<and> bheight (baldR l a r) = bheight l"
by(induct l a r rule: baldR.induct)
  (auto simp: invh_baliL bheight_baliL invh_paint bheight_paint_Red)

lemma invc_baldR: "\<lbrakk>invc a; invc2 b; color a = Black\<rbrakk> \<Longrightarrow> invc (baldR a x b)"
by (induct a x b rule: baldR.induct) (simp_all add: invc_baliL mkNode_def)

lemma invc2_baldR: "\<lbrakk> invc l; invc2 r \<rbrakk> \<Longrightarrow>invc2 (baldR l x r)"
by (induct l x r rule: baldR.induct) 
   (auto simp: invc_baliL paint_invc2 invc2I mkNode_def)

lemma invh_combine:
  "\<lbrakk> invh l; invh r; bheight l = bheight r \<rbrakk>
  \<Longrightarrow> invh (combine l r) \<and> bheight (combine l r) = bheight l"
by (induct l r rule: combine.induct)
   (auto simp: invh_baldL_Black split: tree.splits tcolor.splits)

lemma invc_combine:
  assumes "invc l" "invc r"
  shows "color l = Black \<Longrightarrow> color r = Black \<Longrightarrow> invc (combine l r)"
         "invc2 (combine l r)"
using assms
by (induct l r rule: combine.induct)
   (auto simp: invc_baldL invc2I mkNode_def split: tree.splits tcolor.splits)

lemma neq_LeafD: "t \<noteq> Leaf \<Longrightarrow> \<exists>l x c r. t = Node l (x,c) r"
by(cases t) auto

lemma del_invc_invh: "invh t \<Longrightarrow> invc t \<Longrightarrow> invh (del x t) \<and>
   (color t = Red \<and> bheight (del x t) = bheight t \<and> invc (del x t) \<or>
    color t = Black \<and> bheight (del x t) = bheight t - 1 \<and> invc2 (del x t))"
proof (induct x t rule: del.induct)
case (2 x _ y _ c)
  have "x = y \<or> x < y \<or> x > y" by auto
  thus ?case proof (elim disjE)
    assume "x = y"
    with 2 show ?thesis
    by (cases c) (simp_all add: invh_combine invc_combine)
  next
    assume "x < y"
    with 2 show ?thesis
      by(cases c)
        (auto 
          simp: invh_baldL_invc invc_baldL invc2_baldL mkNode_def 
          dest: neq_LeafD)
  next
    assume "y < x"
    with 2 show ?thesis
      by(cases c)
        (auto 
          simp: invh_baldR_invc invc_baldR invc2_baldR mkNode_def 
          dest: neq_LeafD)
  qed
qed auto

lemma invpst_baldR: "invpst l \<Longrightarrow> invpst r \<Longrightarrow> invpst (baldR l a r)"
by (cases "(l,a,r)" rule: baldR.cases) (auto simp: invpst_baliL)

lemma invpst_baldL: "invpst l \<Longrightarrow> invpst r \<Longrightarrow> invpst (baldL l a r)"
by (cases "(l,a,r)" rule: baldL.cases) (auto simp: invpst_baliR)

lemma invpst_combine: "invpst l \<Longrightarrow> invpst r \<Longrightarrow> invpst (combine l r)"
by(induction l r rule: combine.induct)
  (auto split: tree.splits tcolor.splits simp: invpst_baldR invpst_baldL)

lemma invpst_del: "invpst t \<Longrightarrow> invpst (del x t)"
by(induct x t rule: del.induct)
  (auto simp: invpst_baldR invpst_baldL invpst_combine)

theorem rbt_delete: "rbt t \<Longrightarrow> rbt (delete k t)"
apply (clarsimp simp: delete_def rbt_def)
apply (frule (1) del_invc_invh[where x=k])
apply (auto simp: invc_paint_Black invh_paint color_paint_Black invpst_del)
done

lemma rbt_getmin_ismin: 
  "rbt t \<Longrightarrow> t\<noteq>Leaf \<Longrightarrow> is_min2 (pst_getmin t) (set_tree t)"
unfolding rbt_def by (simp add: pst_getmin_ismin)

definition "rbt_is_empty t \<equiv> t = Leaf"

lemma rbt_is_empty: "rbt_is_empty t \<longleftrightarrow> inorder t = []"
by (cases t) (auto simp: rbt_is_empty_def)

definition empty where "empty = Leaf"


subsection \<open>Overall Correctness\<close>

interpretation PM: PrioMap_by_Ordered
where empty = empty and lookup = lookup and update = update and delete = delete
and inorder = inorder and inv = "rbt" and is_empty = rbt_is_empty 
and getmin = pst_getmin
apply standard
apply (auto simp: lookup_map_of inorder_update inorder_delete rbt_update 
                  rbt_delete rbt_Leaf rbt_is_empty empty_def 
            dest: rbt_getmin_ismin)
done

end
