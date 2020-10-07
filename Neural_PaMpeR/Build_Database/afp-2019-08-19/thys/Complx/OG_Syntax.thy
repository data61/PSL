(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
section \<open>Shallowly-embedded syntax for COMPLX programs\<close>
theory OG_Syntax
imports
  OG_Hoare
  OG_Tactics
begin

datatype ('s, 'p, 'f) ann_com =
  AnnCom "('s, 'p, 'f) ann" "('s,'p,'f) com"

fun ann where "ann (AnnCom p q) = p"
fun com where "com (AnnCom p q) = q"

lemmas ann.simps[oghoare_simps] com.simps[oghoare_simps]

syntax
  "_quote"     :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)"                ("(\<guillemotleft>_\<guillemotright>)" [0] 1000)
  "_antiquote" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b"                ("\<acute>_" [1000] 1000)
  "_Assert"    :: "'a \<Rightarrow> 'a set"                    ("(\<lbrace>_\<rbrace>)" [0] 1000)

translations
  "\<lbrace>b\<rbrace>" \<rightharpoonup> "CONST Collect \<guillemotleft>b\<guillemotright>"

parse_translation \<open>
  let
    fun quote_tr [t] = Syntax_Trans.quote_tr @{syntax_const "_antiquote"} t
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [(@{syntax_const "_quote"}, K quote_tr)] end
\<close>

syntax
  "_fst" :: "'a \<times> 'b \<Rightarrow> 'a"  ("_\<^sub>," [60] 61)
  "_snd" :: "'a \<times> 'b \<Rightarrow> 'b"  ("_\<^sub>." [60] 61)

parse_translation \<open>
  let
    fun fst_tr ((Const (@{const_syntax Pair}, _) $ p $ c)
          :: ts) = p;

    fun snd_tr ((Const (@{const_syntax Pair}, _) $ p $ c)
          :: ts) = c;
  in
   [(@{syntax_const "_fst"}, K fst_tr),
    (@{syntax_const "_snd"}, K snd_tr)]
  end
\<close>

text\<open>Syntax for commands and for assertions and boolean expressions in 
 commands \<open>com\<close> and annotated commands \<open>ann_com\<close>.\<close>

syntax
  "_Annotation" :: "('s,'p,'f) ann_com \<Rightarrow> ('s, 'p, 'f) ann"  ("_\<^sub>?" [60] 61)
  "_Command" :: "('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) com"  ("_\<^sub>!" [60] 61)

parse_translation \<open>
  let
    fun ann_tr ((Const (@{const_syntax AnnCom}, _) $ p $ c)
          :: ts) = p
      | ann_tr (p :: ts) =
          Const (@{const_syntax ann}, dummyT) $ p
      | ann_tr x = raise TERM ("ann_tr", x);

    fun com_tr ((Const (@{const_syntax AnnCom}, _) $ p $ c)
          :: ts) = c
      | com_tr (c :: ts) =
          Const (@{const_syntax com}, dummyT) $ c
      | com_tr x = raise TERM ("com_tr", x);
  in
   [(@{syntax_const "_Annotation"}, K ann_tr),
    (@{syntax_const "_Command"}, K com_tr)]
  end
\<close>

syntax
  "_Seq"  :: "('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com"
                   ("(_,,/ _)" [55, 56] 55)
  "_AnnSeq"  :: "('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com"
                   ("(_;;//_)" [55, 56] 55)

translations
  "_Seq c1 c2" \<rightharpoonup> "CONST AnnCom (CONST AnnComp (c1\<^sub>?) (c2\<^sub>?)) (CONST Seq (c1\<^sub>!) (c2\<^sub>!))"
  "_AnnSeq c1 c2" \<rightharpoonup> "CONST AnnCom (CONST AnnComp (c1\<^sub>?) (c2\<^sub>?)) (CONST Seq (c1\<^sub>!) (c2\<^sub>!))"

syntax
  "_Assign"    :: "idt \<Rightarrow> 'b \<Rightarrow> ('s,'p,'f) ann_com"
                   ("(\<acute>_ :=/ _)" [70, 65] 61)
  "_AnnAssign" :: "'s assn \<Rightarrow> idt \<Rightarrow> 'b \<Rightarrow> ('s,'p,'f) ann_com"
                   ("(_//\<acute>_ :=/ _)" [90,70,65] 61)

definition "FAKE_ANN \<equiv> UNIV"

translations
  "r \<acute>x := a" \<rightharpoonup> "CONST AnnCom (CONST AnnExpr r)
                               (CONST Basic \<guillemotleft>\<acute>(_update_name x (\<lambda>_. a))\<guillemotright>)"
  "\<acute>x := a" \<rightleftharpoons> "CONST FAKE_ANN \<acute>x := a"

abbreviation
  "update_var f S s \<equiv> (\<lambda>v. f (\<lambda>_. v) s) ` S"

abbreviation
  "fun_to_rel f \<equiv>  \<Union> ((\<lambda>s. (\<lambda>v. (s, v)) ` f s) ` UNIV)"

syntax
  "_Spec"      :: "idt \<Rightarrow> 'b \<Rightarrow> ('s,'p,'f) ann_com"
                   ("(\<acute>_ :\<in>/ _)" [70, 65] 61)
  "_AnnSpec"   :: "'a assn \<Rightarrow> idt \<Rightarrow> 'b \<Rightarrow> ('s,'p,'f) ann_com"
                   ("(_//\<acute>_ :\<in>/ _)" [90,70,65] 61)

translations
  "r \<acute>x :\<in> S" \<rightharpoonup> "CONST AnnCom (CONST AnnExpr r)
                               (CONST Spec (CONST fun_to_rel \<guillemotleft>\<acute>(CONST update_var (_update_name x) S)\<guillemotright>))"
  "\<acute>x :\<in> S" \<rightleftharpoons> "CONST FAKE_ANN \<acute>x :\<in> S"


nonterminal grds and grd

syntax
  "_AnnCond1"    :: "'s assn \<Rightarrow> 's bexp  \<Rightarrow> ('s,'p,'f) ann_com  \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(_//IF _//(2THEN/ (_))//(2ELSE/ (_))//FI)"  [90,0,0,0] 61)
  "_AnnCond2"    :: "'s assn \<Rightarrow> 's bexp  \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(_//IF _//(2THEN/ (_))//FI)"  [90,0,0] 61)
  "_AnnWhile"    :: "'s assn \<Rightarrow> 's bexp  \<Rightarrow> 's assn \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com" 
                    ("(_//WHILE _/ INV _//(2DO/ (_))//OD)"  [90,0,0,0] 61)
  "_AnnAwait"    :: "'s assn \<Rightarrow> 's bexp  \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(_//AWAIT _/ (2THEN/ (_))/ END)"  [90,0,0] 61)
  "_AnnAtom"     :: "'s assn  \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(_//\<langle>_\<rangle>)" [90,0] 61)
  "_AnnWait"     :: "'s assn \<Rightarrow> 's bexp \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(_//WAIT _/ END)" [90,0] 61)

  "_Cond"        :: "'s bexp \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com" 
                    ("(IF _//(2THEN/ (_))//(2ELSE/ (_))//FI)" [0, 0, 0] 61)
  "_Cond2"       :: "'s bexp \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(IF _//(2THEN/ (_))//FI)" [0,0] 56)
  "_While_inv"   :: "'s bexp \<Rightarrow> 's assn \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(WHILE _/ INV _//(2DO/ (_))//OD)"  [0, 0, 0] 61)
  "_While"       :: "'s bexp \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(WHILE _//(2DO/ (_))//OD)"  [0, 0] 61)
  "_Await"       :: "'s bexp  \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(AWAIT _/ (2THEN/ (_))/ END)"  [0,0] 61)
  "_Atom"        :: "('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(\<langle>_\<rangle>)" [0] 61)
  "_Wait"        :: "'s bexp \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(WAIT _/ END)" [0] 61)
  "_grd"         :: "'f \<Rightarrow> 's bexp \<Rightarrow> grd"
                    ("'(_, _')" [1000] 1000)
  "_last_grd"    :: "grd \<Rightarrow> grds"   ("_" 1000)
  "_grds"        :: "[grd, grds] \<Rightarrow> grds"
                    ("(_,/ _)" [999,1000] 1000)
  "_guards"      :: "'s assn \<Rightarrow> grds  \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(_//(2_ \<longmapsto>/ (_)))" [90, 0, 56] 61)
  "_Throw"       :: "('s,'p,'f) ann_com"
                    ("THROW" 61)
  "_AnnThrow"    :: "'s assn \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(_/ THROW)" [90] 61)
  "_Try_Catch"   :: "('s,'p,'f) ann_com \<Rightarrow>('s,'p,'f) ann_com \<Rightarrow> ('s,'p,'f) ann_com"
                    ("((2TRY/ (_))//(2CATCH/ (_))/ END)"  [0,0] 71)
  "_AnnCallX"    :: "'s assn \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> 's assn  \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('s\<Rightarrow>'s\<Rightarrow>('s,'p,'f) com) \<Rightarrow> 's assn \<Rightarrow> 's assn \<Rightarrow> 's assn \<Rightarrow> 's assn \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(_//(2CALLX/ (_)//_/ _/ _//_/ _//_/ _//_/ _))"
                      [90,1000,0,1000,0,1000,1000,0,0,0,0] 61)
  "_AnnSCall"    :: "'s assn \<Rightarrow> 'p \<Rightarrow> nat \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(_//SCALL _/ _)" [90,0,0] 61)
  "_Skip"        :: "('s,'p,'f) ann_com"
                    ("SKIP" 61)
  "_AnnSkip"     :: "'s assn \<Rightarrow> ('s,'p,'f) ann_com"
                    ("(_/ SKIP)" [90] 61)

translations
  "r IF b THEN c1 ELSE c2 FI" \<rightharpoonup>
    "CONST AnnCom (CONST AnnBin r (c1\<^sub>?) (c2\<^sub>?)) (CONST Cond \<lbrace>b\<rbrace> (c1\<^sub>!) (c2\<^sub>!))"
  "r IF b THEN c FI" \<rightharpoonup> "r IF b THEN c ELSE SKIP FI"
  "r WHILE b INV i DO c OD" \<rightharpoonup>
    "CONST AnnCom (CONST AnnWhile r i (c\<^sub>?)) (CONST While \<lbrace>b\<rbrace> (c\<^sub>!))"
  "r AWAIT b THEN c END" \<rightharpoonup>
    "CONST AnnCom (CONST AnnRec r (c\<^sub>?)) (CONST Await \<lbrace>b\<rbrace> (c\<^sub>!))"
  "r \<langle>c\<rangle>" \<rightleftharpoons> "r AWAIT CONST True THEN c END"
  "r WAIT b END" \<rightleftharpoons> "r AWAIT b THEN SKIP END"

  "IF b THEN c1 ELSE c2 FI" \<rightleftharpoons> "CONST FAKE_ANN IF b THEN c1 ELSE c2 FI"
  "IF b THEN c FI" \<rightleftharpoons> "CONST FAKE_ANN IF b THEN c ELSE SKIP FI"
  "WHILE b DO c OD" \<rightleftharpoons> "CONST FAKE_ANN WHILE b INV CONST FAKE_ANN DO c OD"
  "WHILE b INV i DO c OD" \<rightleftharpoons> "CONST FAKE_ANN WHILE b INV i DO c OD"
  "AWAIT b THEN c END" \<rightleftharpoons> "CONST FAKE_ANN AWAIT b THEN c END"
  "\<langle>c\<rangle>" \<rightleftharpoons> "CONST FAKE_ANN AWAIT CONST True THEN c END"
  "WAIT b END" \<rightleftharpoons> "AWAIT b THEN SKIP END"

  "_grd f g" \<rightharpoonup> "(f, g)"
  "_grds g gs" \<rightharpoonup> "g#gs"
  "_last_grd g" \<rightharpoonup> "[g]"
  "_guards r gs c" \<rightharpoonup>
    "CONST AnnCom (CONST ann_guards r gs (c\<^sub>?)) (CONST guards gs (c\<^sub>!))"

  "ai CALLX init r p n restore return arestoreq areturn arestorea A" \<rightharpoonup>
    "CONST AnnCom (CONST ann_call ai r n arestoreq areturn arestorea A)
                  (CONST call init p restore return)"
  "r SCALL p n" \<rightharpoonup> "CONST AnnCom (CONST AnnCall r n) (CONST Call p)"

  "r THROW" \<rightleftharpoons> "CONST AnnCom (CONST AnnExpr r) (CONST Throw)"
  "THROW" \<rightleftharpoons> "CONST FAKE_ANN THROW"
  "TRY c1 CATCH c2 END" \<rightharpoonup> "CONST AnnCom (CONST AnnComp (c1\<^sub>?) (c2\<^sub>?))
                                         (CONST Catch (c1\<^sub>!) (c2\<^sub>!))"

  "r SKIP" \<rightleftharpoons> "CONST AnnCom (CONST AnnExpr r) (CONST Skip)"
  "SKIP" \<rightleftharpoons> "CONST FAKE_ANN SKIP"

nonterminal prgs

syntax
  "_PAR" :: "prgs \<Rightarrow> 'a"              ("(COBEGIN//_//COEND)" [57] 56)
  "_prg" :: "['a, 'a, 'a] \<Rightarrow> prgs"        ("(2  _//_,/ _)" [60, 90, 90] 57)
  "_prgs" :: "['a, 'a, 'a, prgs] \<Rightarrow> prgs"  ("(2  _//_,/ _)//\<parallel>//_" [60,90,90,57] 57)

  "_prg_scheme" :: "['a, 'a, 'a, 'a, 'a, 'a] \<Rightarrow> prgs"  
                  ("  (2SCHEME [_ \<le> _ < _]//_//_,/ _)" [0,0,0,60, 90,90] 57)

translations
  "_prg c q a" \<rightharpoonup> "([((c\<^sub>?), q, a)], [(c\<^sub>!)])"
  "_prgs c q a ps" \<rightharpoonup> "(((c\<^sub>?), q, a) # (ps\<^sub>,), (c\<^sub>!) # (ps\<^sub>.))"
  "_PAR ps" \<rightharpoonup> "CONST AnnCom (CONST AnnPar (ps\<^sub>,)) (CONST Parallel (ps\<^sub>.))"

  "_prg_scheme j i k c q a" \<rightharpoonup> "(CONST map (\<lambda>i. ((c\<^sub>?), q, a)) [j..<k], CONST map (\<lambda>i. (c\<^sub>!)) [j..<k])"

syntax
  "_oghoare" :: "('s,'p,'f) body \<Rightarrow> ('s,'p,'f) proc_assns \<Rightarrow> 'f set
              \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> 's assn \<Rightarrow> 's assn \<Rightarrow> bool"  
    ("(4_),/ (4_)/ (|\<turnstile>\<^bsub>'/_\<^esub> (_//_, _))" [60,60,60,20,1000,1000]60)

  "_oghoare_seq" :: "('s,'p,'f) body \<Rightarrow> ('s,'p,'f) proc_assns \<Rightarrow> 'f set
              \<Rightarrow>'s assn \<Rightarrow> ('s,'p,'f) ann_com \<Rightarrow> 's assn \<Rightarrow> 's assn \<Rightarrow> bool"  
    ("(4_),/ (4_)/ (|\<tturnstile>\<^bsub>'/_\<^esub> (_//_//_, _))" [60,60,60,1000,20,1000,1000]60)

translations
  "_oghoare \<Gamma> \<Theta> F c Q A" \<rightharpoonup> "\<Gamma>, \<Theta> \<turnstile>\<^bsub>/F\<^esub> (c\<^sub>?) (c\<^sub>!) Q, A"
  "_oghoare_seq \<Gamma> \<Theta> F P c Q A" \<rightharpoonup> "\<Gamma>, \<Theta> \<tturnstile>\<^bsub>/F\<^esub> P (c\<^sub>?) (c\<^sub>!) Q, A"

ML \<open>val syntax_debug = false\<close>
print_translation \<open> let
  fun quote_tr' f (t :: ts) =
        Term.list_comb (f $ Syntax_Trans.quote_tr' @{syntax_const "_antiquote"} t, ts)
    | quote_tr' _ _ = raise Match;

  fun annquote_tr' f (r :: t :: ts) =
        Term.list_comb (f $ r $ Syntax_Trans.quote_tr' @{syntax_const "_antiquote"} t, ts)
    | annquote_tr' _ _ = raise Match;

  val assert_tr' = quote_tr' (Syntax.const @{syntax_const "_Assert"});

  fun annbexp_tr' name (r :: (Const (@{const_syntax Collect}, _) $ t) :: ts) =
        annquote_tr' (Syntax.const name) (r :: t :: ts)
    | annbexp_tr' name (r :: Const (@{const_syntax UNIV}, _) :: ts) =
        annquote_tr' (Syntax.const name)
                     (r :: Abs ("s", dummyT, Const (@{const_syntax True}, dummyT)) :: ts)
    | annbexp_tr' name (r :: Const (@{const_syntax Set.empty}, _) :: ts) =
        annquote_tr' (Syntax.const name)
                     (r :: Abs ("s", dummyT, Const (@{const_syntax False}, dummyT)) :: ts)
    | annbexp_tr' name x =
        let val _ = if syntax_debug then writeln ("annbexp_tr'\n " ^ @{make_string} x) else () in
        raise Match end;

  fun annassign_tr' (r :: Abs (x, _, f $ k $ Bound 0) :: ts) =
        quote_tr' (Syntax.const @{syntax_const "_AnnAssign"} $ r $ Syntax_Trans.update_name_tr' f)
          (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts)
    | annassign_tr' r = let val _ = writeln ("annassign_tr'\n " ^ @{make_string} r) in
     raise Match end;

  fun dest_list (Const (@{const_syntax Nil}, _)) = []
    | dest_list (Const (@{const_syntax Cons}, _) $ x $ xs) = x :: dest_list xs
    | dest_list _ = raise Match;

  fun guards_lst_tr' [fg] = fg
    | guards_lst_tr' (t :: ts) =
        Syntax.const @{syntax_const "_grds"} $ t $ guards_lst_tr' ts
    | guards_lst_tr' [] = raise Match;

  fun new_AnnCom r c =
    (Const (@{const_syntax AnnCom}, dummyT) $ r $ c)

  fun new_Pair a b =
    (Const (@{const_syntax Pair}, dummyT) $ a $ b)

  fun dest_prod (Const (@{const_syntax Pair}, _) $ a $ b) = (a, b)
    | dest_prod _ = raise Match;

  fun prgs_tr' f pqa c =
        let val (p, qa) = dest_prod pqa
            val (q, a) = dest_prod qa
        in [new_AnnCom (f p) (f c), f q, f a] end

  fun prgs_lst_tr' [p] [c] =
        list_comb (Syntax.const @{syntax_const "_prg"},
                   prgs_tr' I p c)
    | prgs_lst_tr' (p :: ps) (c :: cs) =
        list_comb (Syntax.const @{syntax_const "_prgs"},
                   prgs_tr' I p c) $ prgs_lst_tr' ps cs
    | prgs_lst_tr' _ _= raise Match;

  fun AnnCom_tr (Const (@{const_syntax AnnPar}, _) $
                 (Const (@{const_syntax map}, _) $
                  Abs (i, T, p) $ (Const _ $ j $ k)) ::
                 Const (@{const_syntax Parallel}, _) $
                 (Const (@{const_syntax map}, _) $
                  Abs (_, _, c) $ _) :: ts) =
        let val _ = if syntax_debug then writeln "prg_scheme" else ()
            fun dest_abs body = snd (Term.dest_abs (i, T, body)) in
          Syntax.const @{syntax_const "_PAR"} $
            list_comb (Syntax.const @{syntax_const "_prg_scheme"} $
              j $ Free (i, T) $ k, prgs_tr' dest_abs p c)
        end
    | AnnCom_tr (Const (@{const_syntax AnnPar}, _) $ ps ::
               Const (@{const_syntax Parallel}, _) $ cs :: ts) =
        let val _ = if syntax_debug then writeln "Par" else ()
            val (ps', cs') = (dest_list ps, dest_list cs)
        in Syntax.const @{syntax_const "_PAR"} $
             prgs_lst_tr' ps' cs' end
    | AnnCom_tr (Const (@{const_syntax AnnExpr}, _) $ r ::
               Const (@{const_syntax Basic}, _) $ Abs (x, _, f $ k $ Bound 0) :: ts) =
      let val _ = if syntax_debug then writeln "Basic'" else () in
        quote_tr' (Syntax.const @{syntax_const "_AnnAssign"} $ r $ Syntax_Trans.update_name_tr' f)
          (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts) end
    | AnnCom_tr (Const (@{const_syntax AnnExpr}, _) $ r ::
               Const (@{const_syntax Basic}, _) $ (f $ k) :: ts) =
      let val _ = if syntax_debug then writeln "Basic" else () in
        quote_tr' (Syntax.const @{syntax_const "_AnnAssign"} $ r $ Syntax_Trans.update_name_tr' f)
          (k :: ts) end
    | AnnCom_tr (Const (@{const_syntax AnnExpr}, _) $ r ::
               Const (@{const_syntax Spec}, _) $ (_ $ _ $ Abs (_,_, _ $ _ $ ((_ $ f) $ S $ _))) :: ts) =
      let val _ = if syntax_debug then writeln ("Spec") else () in
        (Syntax.const @{syntax_const "_AnnSpec"} $ r $
           Syntax_Trans.update_name_tr' f $
           Syntax_Trans.antiquote_tr' @{syntax_const "_antiquote"} S)
      end
    | AnnCom_tr (Const (@{const_syntax AnnComp}, _) $ r $ r' ::
               Const (@{const_syntax Seq}, _) $ c $ c' :: ts) =
      let val _ = if syntax_debug then writeln "Seq" else ()
      in Syntax.const @{syntax_const "_AnnSeq"} $
                new_AnnCom r c $ new_AnnCom r' c' end
    | AnnCom_tr (Const (@{const_syntax AnnRec}, _) $ r $ p ::
               Const (@{const_syntax Await}, _) $ b $ c :: ts) =
       let val _ = if syntax_debug then writeln "Await" else ()
          in annbexp_tr' @{syntax_const "_AnnAwait"}
                  (r :: b :: new_AnnCom p c :: ts) end
    | AnnCom_tr (Const (@{const_syntax AnnWhile}, _) $ r $ i $ p ::
               Const (@{const_syntax While}, _) $ b $ c :: ts) =
       let val _ = if syntax_debug then writeln "While" else ()
          in annbexp_tr' @{syntax_const "_AnnWhile"}
                  (r :: b :: i :: new_AnnCom p c :: ts) end
    | AnnCom_tr (Const (@{const_syntax AnnBin}, _) $ r $ p $ p' ::
               Const (@{const_syntax Cond}, _) $ b $ c $ c':: ts) =
       let val _ = if syntax_debug then writeln "Cond" else ()
          in annbexp_tr' @{syntax_const "_AnnCond1"}
                  (r :: b :: new_AnnCom p c :: new_AnnCom p' c' :: ts) end
    | AnnCom_tr (Const (@{const_syntax ann_guards}, _) $ r $ gs $ p ::
               Const (@{const_syntax guards}, _) $ _ $ c :: ts) =
       let val _ = if syntax_debug then writeln "guards" else ()
          in Syntax.const @{syntax_const "_guards"} $ r $
                guards_lst_tr' (dest_list gs) $ new_AnnCom p c end
    | AnnCom_tr (Const (@{const_syntax AnnRec}, _) $ r $ p ::
               Const (@{const_syntax Guard}, _) $ f $ g $ c :: ts) =
       let val _ = if syntax_debug then writeln "guards'" else ()
          in Syntax.const @{syntax_const "_guards"} $ r $
                new_Pair f g $ new_AnnCom p c end
    | AnnCom_tr (Const (@{const_syntax AnnCall}, _) $ r $ n ::
               Const (@{const_syntax Call}, _) $ p :: ts) =
       let val _ = if syntax_debug then writeln "SCall" else ()
          in Syntax.const @{syntax_const "_AnnSCall"} $ r $ p $ n end
    | AnnCom_tr (Const (@{const_syntax ann_call}, _) $
                   ai $ r $ n $ arestoreq $ areturn $ arestorea $ A ::
               Const (@{const_syntax call}, _) $
                   init $ p $ restore $ return :: ts) =
       let val _ = if syntax_debug then writeln "CallX" else ()
          in Syntax.const @{syntax_const "_AnnCallX"} $ ai $ init $
                  r $ p $ n $ restore $ return $ arestoreq $ areturn $
                  arestorea $ A end
    | AnnCom_tr (Const (@{const_syntax AnnComp}, _) $ r $ r' ::
               Const (@{const_syntax Catch}, _) $ c $ c' :: ts) =
      let val _ = if syntax_debug then writeln "Catch" else ()
      in Syntax.const @{syntax_const "_Try_Catch"} $
                new_AnnCom r c $ new_AnnCom r' c' end
    | AnnCom_tr (Const (@{const_syntax ann}, _) $ p ::
               Const (@{const_syntax com}, _) $ p' :: ts) =
       let val _ = if syntax_debug then writeln "ann_com" else ()
          in if p = p' then p else raise Match end
    | AnnCom_tr x = let val _ = if syntax_debug then writeln ("AnnCom_tr\n " ^ @{make_string} x) else ()
          in raise Match end;

    fun oghoare_tr (gamma :: sigma :: F :: r :: c :: Q :: A :: ts) =
        let val _ = if syntax_debug then writeln "oghoare" else ()
          in Syntax.const @{syntax_const "_oghoare"} $
               gamma $ sigma $ F $ new_AnnCom r c $ Q $ A
          end
      | oghoare_tr x = let val _ = writeln ("oghoare_tr\n " ^ @{make_string} x)
            in raise Match end;

    fun oghoare_seq_tr (gamma :: sigma :: F :: P :: r :: c :: Q :: A :: ts) =
        let val _ = if syntax_debug then writeln "oghoare_seq" else ()
          in Syntax.const @{syntax_const "_oghoare_seq"} $
               gamma $ sigma $ F $ P $ new_AnnCom r c $ Q $ A
          end
      | oghoare_seq_tr x = let val _ = writeln ("oghoare_seq_tr\n " ^ @{make_string} x)
            in raise Match end;

  in
   [(@{const_syntax Collect}, K assert_tr'),
    (@{const_syntax AnnCom}, K AnnCom_tr),
    (@{const_syntax oghoare}, K oghoare_tr),
    (@{const_syntax oghoare_seq}, K oghoare_seq_tr)]

  end
\<close>

end
