theory LLEarleyParsing 
imports LocalLexing
begin

datatype item = 
  Item 
    (item_rule: rule) 
    (item_dot : nat) 
    (item_origin : nat)
    (item_end : nat)

type_synonym items = "item set"

definition item_nonterminal :: "item \<Rightarrow> symbol"
where
  "item_nonterminal x = fst (item_rule x)"

definition item_rhs :: "item \<Rightarrow> sentence"
where
  "item_rhs x = snd (item_rule x)"

definition item_\<alpha> :: "item \<Rightarrow> sentence"
where
  "item_\<alpha> x = take (item_dot x) (item_rhs x)"

definition item_\<beta> :: "item \<Rightarrow> sentence"
where 
  "item_\<beta> x = drop (item_dot x) (item_rhs x)"

definition init_item :: "rule \<Rightarrow> nat \<Rightarrow> item"
where
  "init_item r k = Item r 0 k k"

definition is_complete :: "item \<Rightarrow> bool"
where
  "is_complete x = (item_dot x \<ge> length (item_rhs x))"

definition next_symbol :: "item \<Rightarrow> symbol option"
where
  "next_symbol x = (if is_complete x then None else Some ((item_rhs x) ! (item_dot x)))"

definition inc_item :: "item \<Rightarrow> nat \<Rightarrow> item"
where
  "inc_item x k = Item (item_rule x) (item_dot x + 1) (item_origin x) k"

definition bin :: "items \<Rightarrow> nat \<Rightarrow> items"
where
  "bin I k = { x . x \<in> I \<and> item_end x = k }"

context LocalLexing begin

definition Init :: "items"
where
  "Init = { init_item r 0 | r. r \<in> \<RR> \<and> fst r = \<SS> }"

definition Predict :: "nat \<Rightarrow> items \<Rightarrow> items"
where
  "Predict k I = I \<union>  
     { init_item r k | r x. r \<in> \<RR> \<and> x \<in> bin I k \<and> 
       next_symbol x = Some(fst r) }"

definition Complete :: "nat \<Rightarrow> items \<Rightarrow> items"
where
  "Complete k I = I \<union> { inc_item x k | x y. 
     x \<in> bin I (item_origin y) \<and> y \<in> bin I k \<and> is_complete y \<and> 
     next_symbol x = Some (item_nonterminal y) }"

definition TokensAt :: "nat \<Rightarrow> items \<Rightarrow> token set"
where
  "TokensAt k I = { (t, s) | t s x l. x \<in> bin I k \<and> 
     next_symbol x = Some t \<and> is_terminal t \<and> 
     l \<in> Lex t Doc k \<and> s = take l (drop k Doc) }"

definition Tokens :: "nat \<Rightarrow> token set \<Rightarrow> items \<Rightarrow> token set"
where
  "Tokens k T I = Sel T (TokensAt k I)"

definition Scan :: "token set \<Rightarrow> nat \<Rightarrow> items \<Rightarrow> items"
where
  "Scan T k I = I \<union>
     { inc_item x (k + length c) | x t c. x \<in> bin I k \<and> (t, c) \<in> T \<and>
       next_symbol x = Some t }"
      
definition \<pi> :: "nat \<Rightarrow> token set \<Rightarrow> items \<Rightarrow> items"
where
  "\<pi> k T I = 
     limit (\<lambda> I. Scan T k (Complete k (Predict k I))) I"

fun \<J> :: "nat \<Rightarrow> nat \<Rightarrow> items"
and \<I> :: "nat \<Rightarrow> items"
and \<T> :: "nat \<Rightarrow> nat \<Rightarrow> token set"
where
  "\<J> 0 0 = \<pi> 0 {} Init"
| "\<J> k (Suc u) = \<pi> k (\<T> k (Suc u)) (\<J> k u)"
| "\<J> (Suc k) 0 = \<pi> (Suc k) {} (\<I> k)"
| "\<T> k 0 = {}"
| "\<T> k (Suc u) = Tokens k (\<T> k u) (\<J> k u)"
| "\<I> k = natUnion (\<J> k)"

definition \<II> :: "items"
where
  "\<II> = \<I> (length Doc)"

definition is_finished :: "item \<Rightarrow> bool" where
  "is_finished x = (item_nonterminal x = \<SS> \<and> item_origin x = 0 \<and> item_end x = length Doc \<and> 
    is_complete x)"

definition earley_recognised :: "bool"
where
  "earley_recognised = (\<exists> x \<in> \<II>. is_finished x)"

end

end 
