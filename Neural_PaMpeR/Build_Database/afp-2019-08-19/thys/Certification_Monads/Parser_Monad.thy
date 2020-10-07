(* Title:     Parser_Monad
   Author:    Christian Sternagel
   Author:    René Thiemann
*)

section \<open>Monadic Parser Combinators\<close>

theory Parser_Monad
imports
  Error_Monad
  Show.Show
begin

(*It might be nice to be able to enter things like CHR ''\t'', ... directly.*)
abbreviation (input) "tab \<equiv> CHR 0x09"
abbreviation (input) "carriage_return \<equiv> CHR 0x0D"
abbreviation (input) "wspace \<equiv> [CHR '' '', CHR ''\<newline>'', tab, carriage_return]"

definition trim :: "string \<Rightarrow> string"
  where "trim = dropWhile (\<lambda>c. c \<in> set wspace)"

lemma trim:
  "\<exists>w. s = w @ trim s"
  by (unfold trim_def) (metis takeWhile_dropWhile_id)

text \<open>
  A parser takes a list of tokes and returns either an error message or
  a result together with the remaining tokens.
\<close>
type_synonym
  ('t, 'a) gen_parser = "'t list \<Rightarrow> string + ('a \<times> 't list)"

type_synonym
  'a parser = "(char, 'a) gen_parser"

subsection \<open>Monad-Setup for Parsers\<close>

definition return :: "'a \<Rightarrow> ('t, 'a) gen_parser"
where
  "return x = (\<lambda>ts. Error_Monad.return (x, ts))"

definition error :: "string \<Rightarrow> ('t, 'a) gen_parser"
where
  "error e = (\<lambda>_. Error_Monad.error e)"

definition bind :: "('t, 'a) gen_parser \<Rightarrow> ('a \<Rightarrow> ('t, 'b) gen_parser) \<Rightarrow> ('t, 'b) gen_parser"
where
  "bind m f ts = do {
    (x, ts') \<leftarrow> m ts;
    f x ts'
  }"

adhoc_overloading
  Monad_Syntax.bind bind

lemma bind_cong [fundef_cong]:
  fixes m1 :: "('t, 'a) gen_parser"
  assumes "m1 ts2 = m2 ts2"
    and "\<And> y ts. m2 ts2 = Inr (y, ts) \<Longrightarrow> f1 y ts = f2 y ts"
    and "ts1 = ts2"
  shows "((m1 \<bind> f1) ts1) = ((m2 \<bind> f2) ts2)"
  using assms unfolding bind_def by (cases "m1 ts1") auto

definition update_tokens :: "('t list \<Rightarrow> 't list) \<Rightarrow> ('t, 't list) gen_parser"
where
  "update_tokens f ts = Error_Monad.return (ts, f ts)"

definition get_tokens :: "('t, 't list) gen_parser"
where
  "get_tokens = update_tokens (\<lambda>x. x)"

definition set_tokens :: "'t list \<Rightarrow> ('t, unit) gen_parser"
where
  [code_unfold]: "set_tokens ts = update_tokens (\<lambda>_. ts) \<then> return ()"

definition err_expecting :: "string \<Rightarrow> ('t::show, 'a) gen_parser"
where
  "err_expecting msg ts = Error_Monad.error
    (''expecting '' @ msg @ '', but found: '' @ shows_quote (shows (take 30 ts)) [])"

fun eoi :: "('t :: show, unit) gen_parser"
where
  "eoi [] = Error_Monad.return ((), [])" |
  "eoi ts = err_expecting ''end of input'' ts"

fun exactly_aux :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string parser"
where
  "exactly_aux s i (x # xs) (y # ys) =
    (if x = y then exactly_aux s i xs ys
    else err_expecting (''\"'' @ s @ ''\"'') i)" |
  "exactly_aux s i [] xs = Error_Monad.return (s, trim xs)" |
  "exactly_aux s i (x # xs) [] = err_expecting (''\"'' @ s @ ''\"'') i"

fun oneof_aux :: "string list \<Rightarrow> string list \<Rightarrow> string parser"
where
  "oneof_aux allowed (x # xs) ts =
    (if map snd (zip x ts) = x then Error_Monad.return (x, trim (List.drop (length x) ts))
    else oneof_aux allowed xs ts)" |
  "oneof_aux allowed [] ts = err_expecting (''one of '' @ shows_list allowed []) ts"

definition is_parser :: "'a parser \<Rightarrow> bool" where
  "is_parser p \<longleftrightarrow> (\<forall>s r x. p s = Inr (x, r) \<longrightarrow> length s \<ge> length r)"

lemma is_parserI [intro]:
  assumes "\<And>s r x. p s = Inr (x, r) \<Longrightarrow> length s \<ge> length r"
  shows "is_parser p"
  using assms unfolding is_parser_def by blast

lemma is_parserE [elim]:
  assumes "is_parser p"
    and "(\<And>s r x. p s = Inr (x, r) \<Longrightarrow> length s \<ge> length r) \<Longrightarrow> P"
  shows "P"
  using assms by (auto simp: is_parser_def)

lemma is_parser_length:
  assumes "is_parser p" and "p s = Inr (x, r)"
  shows "length s \<ge> length r"
  using assms by blast

text \<open>A \emph{consuming parser} (cparser for short) consumes at least one token of input.\<close>
definition is_cparser :: "'a parser \<Rightarrow> bool"
where
  "is_cparser p \<longleftrightarrow> (\<forall>s r x. p s = Inr (x, r) \<longrightarrow> length s > length r)"

lemma is_cparserI [intro]:
  assumes "\<And>s r x. p s = Inr (x, r) \<Longrightarrow> length s > length r"
  shows "is_cparser p"
  using assms unfolding is_cparser_def by blast

lemma is_cparserE [elim]:
  assumes "is_cparser p"
    and "(\<And>s r x. p s = Inr (x, r) \<Longrightarrow> length s > length r) \<Longrightarrow> P"
  shows "P"
  using assms by (auto simp: is_cparser_def)

lemma is_cparser_length:
  assumes "is_cparser p" and "p s = Inr (x, r)"
  shows "length s > length r"
  using assms by blast

lemma is_parser_bind [intro, simp]:
  assumes p: "is_parser p" and q: "\<And> x. is_parser (q x)" 
  shows "is_parser (p \<bind> q)"
proof
  fix s r x
  assume "(p \<bind> q) s = Inr (x, r)"
  then obtain y t
    where P: "p s = Inr (y, t)" and Q: "q y t = Inr (x, r)"
    unfolding bind_def by (cases "p s") auto
  have "length r \<le> length t" using q and Q by (auto simp: is_parser_def)
  also have "\<dots> \<le> length s" using p and P by (auto simp: is_parser_def)
  finally show "length r \<le> length s" .
qed
  
definition oneof :: "string list \<Rightarrow> string parser"
where
  "oneof xs = oneof_aux xs xs"

lemma oneof_result:
  assumes "oneof xs s = Inr (y, r)" 
  shows "\<exists> w. s = y @ w @ r \<and> y \<in> set xs"
proof -
  {
    fix ys
    assume "oneof_aux ys xs s = Inr (y,r)"
    hence "\<exists> w. s = y @ w @ r \<and> y \<in> set xs"
    proof (induct xs)
      case Nil thus ?case by (simp add: err_expecting_def)
    next
      case (Cons z zs)
      thus ?case 
      proof (cases "map snd (zip z s) = z")
        case False with Cons show ?thesis by simp
      next
        case True
        hence s: "s = z @ drop (length z) s"          
        proof (induct z arbitrary: s)
          case (Cons a zz)
          thus ?case 
            by (cases s, auto)
        qed simp
        from trim[of "drop (length z) s"] obtain w where "drop (length z) s = w @ trim (drop (length z) s)" by blast
        with s have s: "s = z @ w @ trim (drop (length z) s)" by auto
        from True Cons(2) have yz: "y = z" and r: "r = trim (drop (length y) s)" by auto
        show ?thesis
          by (simp add: yz r, rule exI, rule s)
      qed
    qed
  }  
  from this [OF assms [unfolded oneof_def]]
    show ?thesis .
qed

definition exactly :: "string \<Rightarrow> string parser"
where 
  "exactly s x = exactly_aux s x s x"

lemma exactly_result:
  assumes "exactly x s = Inr (y, r)"
  shows "\<exists> w. s = x @ w @ r \<and> y = x"
proof -
  { 
    fix a b
    assume "exactly_aux a b x s = Inr (y,r)"
    hence "\<exists> w. s = x @ w @ r \<and> y = a"
    proof (induct x arbitrary: s)
      case Nil 
      thus ?case using trim[of s] by auto
    next
      case (Cons c xs) note xs = this
      show ?case 
      proof (cases s)
        case Nil
        with xs show ?thesis by (auto simp: err_expecting_def)
      next
        case (Cons d ss)
        note xs = xs[unfolded Cons]
        from xs(2) have "exactly_aux a b xs ss = Inr (y, r) \<and> c = d"
          by (cases "c = d") (auto simp: err_expecting_def)
        hence res: "exactly_aux a b xs ss = Inr (y, r)" and c: "c = d" by auto
        from xs(1)[OF res]
        show ?thesis unfolding Cons c by auto
      qed
    qed
  }
  from this[OF assms [unfolded exactly_def]] show ?thesis .
qed

hide_const oneof_aux exactly_aux
 
lemma oneof_length: 
  assumes "oneof xs s = Inr (y, r)"
  shows "length s \<ge> length y + length r \<and> y \<in> set xs"
proof -
  from oneof_result [OF assms]
  obtain w where "s = y @ w @ r \<and> y \<in> set xs" ..
  thus ?thesis  by auto
qed

lemma is_parser_oneof [intro]:
  "is_parser (oneof ts)"
proof
  fix s r x
  assume "oneof ts s = Inr (x ,r)"
  from oneof_length [OF this] show " length s \<ge> length r" by auto
qed

lemma is_cparser_oneof [intro, simp]:
  assumes "\<forall>x\<in>set ts. length x \<ge> 1"
  shows "is_cparser (oneof ts)"
proof
  fix s r x
  assume "oneof ts s = Inr (x ,r)"
  from oneof_length [OF this] assms
    show " length s > length r" by auto
qed

lemma exactly_length: 
  assumes "exactly x s = Inr (y, r)"
  shows "length s \<ge> length x + length r"
proof -
  from exactly_result [OF assms]
  obtain w where "s = x @ w @ r" by auto
  thus ?thesis  by auto
qed

lemma is_parser_exactly [intro]:
  "is_parser (exactly xs)"
proof
  fix s r x
  assume "exactly xs s = Inr (x ,r)"
  from exactly_length [OF this]
    show "length s \<ge> length r" by auto
qed

lemma is_cparser_exactly [intro]:
  assumes "length xs \<ge> 1"
  shows "is_cparser (exactly xs)"
proof
  fix s r x
  assume "exactly xs s = Inr (x, r)"
  from exactly_length [OF this]
    show "length s > length r" using assms by auto
qed

fun many :: "(char \<Rightarrow> bool) \<Rightarrow> (char list) parser"
where
  "many P (t # ts) =
    (if P t then do {
      (rs, ts') \<leftarrow> many P ts;
      Error_Monad.return (t # rs, ts')
    } else Error_Monad.return ([], t # ts))" |
  "many P [] = Error_Monad.return ([], [])"

lemma is_parser_many [intro]:
  "is_parser (many P)" 
proof
  fix s r x
  assume "many P s = Inr (x, r)"
  thus "length r \<le> length s"
  proof (induct s arbitrary: x r)
    case (Cons t ts)
    thus ?case by (cases "P t", cases "many P ts") force+
  qed simp
qed

definition manyof :: "char list \<Rightarrow> (char list) parser"
where
  [code_unfold]: "manyof cs = many (\<lambda>c. c \<in> set cs)"

lemma is_parser_manyof [intro]:
  "is_parser (manyof cs)"
  unfolding manyof_def by blast

definition spaces :: "unit parser"
where
  [code_unfold]: "spaces = manyof wspace \<then> return ()"

lemma is_parser_return [intro]:
  "is_parser (return x)"
  by (auto simp: is_parser_def return_def)

lemma is_parser_error [intro]:
  "is_parser (error x)"
  by (auto simp: is_parser_def error_def)

lemma is_parser_If [intro!]:
  assumes "is_parser p" and "is_parser q"
  shows "is_parser (if b then p else q)"
  using assms by (cases b) auto

lemma is_parser_Let [intro!]:
  assumes "is_parser (f y)"
  shows "is_parser (let x = y in f x)"
  using assms by auto

lemma is_parser_spaces [intro]:
  "is_parser spaces"
  unfolding spaces_def by blast

fun scan_upto :: "string \<Rightarrow> string parser"
where
  "scan_upto end (t # ts) =
    (if map snd (zip end (t # ts)) = end then do {
       Error_Monad.return (end, List.drop (length end) (t # ts))
    } else do {
      (res, ts') \<leftarrow> scan_upto end ts;
      Error_Monad.return (t # res, ts')
    })" |
  "scan_upto end [] = Error_Monad.error (''did not find end-marker '' @ shows_quote (shows end) [])"

lemma scan_upto_length: 
  assumes "scan_upto end s = Inr (y, r)"
  shows "length s \<ge> length end + length r"
using assms
proof (induct s arbitrary: y r)
  case (Cons t ts)
  show ?case 
  proof (cases "map snd (zip end (t # ts)) = end")
    case True
    then obtain tss where tss: "tss = t # ts" and map: "map snd (zip end tss) = end" by auto
    from map have len: "length tss \<ge> length end"
    proof (induct "end" arbitrary: tss)
      case (Cons e en)
      thus ?case by (cases tss, auto)
    qed simp
    from True tss Cons(2) have y: "y = end" and r: "r = List.drop (length end) tss" by auto
    show ?thesis by (simp only: tss[symmetric], simp add: y r, auto simp: len)
  next
    case False
    with Cons obtain res ts'
      where "scan_upto end ts = Inr (res,ts')" by (cases "scan_upto end ts") (auto)
    from Cons(1)[OF this] Cons(2) False this show ?thesis by auto
  qed
qed simp

lemma is_parser_scan_upto [intro]:
  "is_parser (scan_upto end)"
  unfolding is_parser_def using scan_upto_length [of "end"] by force

lemma is_cparser_scan_upto [intro]:
  "is_cparser (scan_upto (e # end))"
  unfolding is_cparser_def using scan_upto_length [of "e # end"] by force

end

