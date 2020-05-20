section \<open>Address Graph\<close>

theory Graph
imports Main
begin

text \<open>
This theory introduces the graph to be marked as a relation next on
nodes (addresses). We assume that we have a special node nil (the
null address). We have a node root from which we start marking the graph. 
We also assume that nil is not related by next to any node and any node is 
not related by next to nil.
\<close>

locale node = 
  fixes nil    :: "'node"
  fixes root   :: "'node"

locale graph = node +
  fixes "next" :: "('node \<times> 'node) set"
  assumes next_not_nil_left: "(!! x . (nil, x) \<notin> next)" 
  assumes next_not_nil_right: "(!! x . (x, nil) \<notin> next)"
begin

text \<open>
On lists of nodes we introduce two operations similar to
existing hd and tl for getting the head and the tail of
a list. The new function head applied to a nonempty list
returns the head of the list, and it reurns nil when
applied to the empty list. The function tail returns the
tail of the list when applied to a non-empty list, and
it returns the empty list otherwise.
\<close>
  definition
    "head S \<equiv> (if S = [] then nil else (hd S))"
    
  definition
    "tail (S::'a list) \<equiv> (if S = [] then [] else (tl S))"

  lemma [simp]: "((nil, x) \<in> next) = False"
    by (simp add: next_not_nil_left)
  
  lemma [simp]: "((x, nil) \<in> next) = False"
    by (simp add: next_not_nil_right)


  theorem head_not_nil [simp]:
    "(head S \<noteq> nil) = (head S = hd S \<and> tail S = tl S \<and> hd S \<noteq> nil \<and> S \<noteq> [])"
    by (simp add: head_def tail_def)
  
  theorem nonempty_head [simp]:
    "head (x # S) = x"
    by (simp add: head_def)

  theorem nonempty_tail [simp]:
    "tail (x # S) = S"
    by (simp add: tail_def)

  definition (in graph)
    "reach x \<equiv> {y . (x, y) \<in> next\<^sup>* \<and> y \<noteq> nil}"

  theorem (in graph) reach_nil [simp]: "reach nil = {}"
    apply (simp add: reach_def, safe)
    apply (drule rtrancl_induct)
    by auto

  theorem (in graph)  reach_next: "b \<in> reach a \<Longrightarrow> (b, c) \<in> next \<Longrightarrow> c \<in> reach a"
    apply (simp add: reach_def)
    by auto

  definition (in graph) 
    "path S mrk \<equiv> {x . (\<exists> s . s \<in> S \<and> (s, x) \<in> next O (next \<inter> ((-mrk)\<times>(-mrk)))\<^sup>* )}"
  end
  
end
