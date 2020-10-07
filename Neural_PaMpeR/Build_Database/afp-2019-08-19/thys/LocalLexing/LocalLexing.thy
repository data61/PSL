theory LocalLexing
imports CFG
begin

typedecl character

type_synonym lexer = "character list \<Rightarrow> nat \<Rightarrow> nat set"  

type_synonym token = "symbol \<times> character list" 

type_synonym tokens = "token list"

definition terminal_of_token :: "token \<Rightarrow> symbol"
where
  "terminal_of_token t = fst t"

definition terminals :: "tokens \<Rightarrow> sentence"
where
  "terminals ts = map terminal_of_token ts"

definition chars_of_token :: "token \<Rightarrow> character list"
where
  "chars_of_token t = snd t"

fun chars :: "tokens \<Rightarrow> character list"
where
  "chars [] = []"
| "chars (t#ts) = (chars_of_token t) @ (chars ts)"

fun charslength :: "tokens \<Rightarrow> nat"
where
  "charslength cs = length (chars cs)"

definition is_lexer :: "lexer \<Rightarrow> bool"
where
  "is_lexer lexer = 
    (\<forall> D p l. (p \<le> length D \<and> l \<in> lexer D p \<longrightarrow> p + l \<le> length D) \<and>
              (p > length D \<longrightarrow> lexer D p = {}))"

type_synonym selector = "token set \<Rightarrow> token set \<Rightarrow> token set"

definition is_selector :: "selector \<Rightarrow> bool"
where
  "is_selector sel = (\<forall> A B. A \<subseteq> B \<longrightarrow> (A \<subseteq> sel A B \<and> sel A B \<subseteq> B))" 

fun by_length :: "nat \<Rightarrow> tokens set \<Rightarrow> tokens set"
where
  "by_length l tss = { ts . ts \<in> tss \<and> length (chars ts) = l }" 

fun funpower :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a)"
where
  "funpower f 0 x = x"
| "funpower f (Suc n) x = f (funpower f n x)"

definition natUnion :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
where
  "natUnion f = \<Union> { f n | n. True }"

definition limit  :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'a set"
where
  "limit f x = natUnion (\<lambda> n. funpower f n x)"

locale LocalLexing = CFG +
  fixes Lex :: "symbol \<Rightarrow> lexer"
  fixes Sel :: "selector"
  assumes Lex_is_lexer: "\<forall> t \<in> \<TT>. is_lexer (Lex t)"
  assumes Sel_is_selector: "is_selector Sel"
  fixes Doc :: "character list"
begin

definition admissible :: "tokens \<Rightarrow> bool"
where
  "admissible ts = (terminals ts \<in> \<L>\<^sub>P)" 

definition Append :: "token set \<Rightarrow> nat \<Rightarrow> tokens set \<Rightarrow> tokens set"
where
  "Append Z k P = P \<union> 
    { p @ [t] | p t. p \<in> by_length k P \<and> t \<in> Z \<and> admissible (p @ [t])}"

definition \<X> :: "nat \<Rightarrow> token set"
where
  "\<X> k = {(t, \<omega>) | t l \<omega>. t \<in> \<TT> \<and> l \<in> Lex t Doc k \<and> \<omega> = take l (drop k Doc)}"

definition \<W> :: "tokens set \<Rightarrow> nat \<Rightarrow> token set"
where
  "\<W> P k =  { u. u \<in> \<X> k \<and> (\<exists> p \<in> by_length k P. admissible (p@[u])) }"

definition \<Y> :: "token set \<Rightarrow> tokens set \<Rightarrow> nat \<Rightarrow> token set"
where
  "\<Y> T P k = Sel T (\<W> P k)" 

fun \<P> :: "nat \<Rightarrow> nat \<Rightarrow> tokens set"
and \<Q> :: "nat \<Rightarrow> tokens set"
and \<Z> :: "nat \<Rightarrow> nat \<Rightarrow> token set"
where
  "\<P> 0 0 = {[]}"
| "\<P> k (Suc u) = limit (Append (\<Z> k (Suc u)) k) (\<P> k u)"
| "\<P> (Suc k) 0 = \<Q> k"
| "\<Z> k 0 = {}"
| "\<Z> k (Suc u) = \<Y> (\<Z> k u) (\<P> k u) k"
| "\<Q> k = natUnion (\<P> k)"

definition \<PP> :: "tokens set"
where
  "\<PP> = \<Q> (length Doc)"

definition ll :: "tokens set"
where 
  "ll = { p . p \<in> \<PP> \<and> charslength p = length Doc \<and> terminals p \<in> \<L> }"

end

end
