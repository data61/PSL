(* Title:     Xml
   Author:    Christian Sternagel
   Author:    René Thiemann
*)

section \<open>XML Transformers for Extracting Data from XML Nodes\<close>

theory Xmlt
imports
  Xml
  Certification_Monads.Strict_Sum
  HOL.Rat
begin

type_synonym
  tag = string

text \<open>The type of transformers on xml nodes.\<close>
type_synonym
  'a xmlt = "xml \<Rightarrow> string +\<^sub>\<bottom> 'a"

definition map :: "(xml \<Rightarrow> ('e +\<^sub>\<bottom> 'a)) \<Rightarrow> xml list \<Rightarrow> 'e +\<^sub>\<bottom> 'a list"
where
  [code_unfold]: "map = map_sum_bot"

lemma map_mono [partial_function_mono]:
  fixes C :: "xml \<Rightarrow> ('b \<Rightarrow> ('e +\<^sub>\<bottom> 'c)) \<Rightarrow> 'e +\<^sub>\<bottom> 'd"
  assumes C: "\<And>y. y \<in> set B \<Longrightarrow> mono_sum_bot (C y)"
  shows "mono_sum_bot (\<lambda>f. map (\<lambda>y. C y f) B)" 
  unfolding map_def by (auto intro: partial_function_mono C)

hide_const (open) map

fun "text" :: "tag \<Rightarrow> string xmlt"
where
  "text tag (XML n atts [XML_text t]) = 
    (if n = tag \<and> atts = [] then return t
    else error (concat
      [''could not extract text for '', tag,'' from '', ''\<newline>'', show (XML n atts [XML_text t])]))"
| "text tag xml = error (concat [''could not extract text for '', tag,'' from '', ''\<newline>'', show xml])"
hide_const (open) "text"

definition bool_of_string :: "string \<Rightarrow> string +\<^sub>\<bottom> bool"
where
  "bool_of_string s =
    (if s = ''true'' then return True
    else if s = ''false'' then return False
    else error (''cannot convert '' @ s @ '' into Boolean''))"

fun bool :: "tag \<Rightarrow> bool xmlt"
where
  "bool tag node = Xmlt.text tag node \<bind> bool_of_string"
hide_const (open) bool

definition fail :: "tag \<Rightarrow> 'a xmlt"
where
  "fail tag xml =
    error (concat
      [''could not transform the following xml element (expected '', tag, '')'', ''\<newline>'', show xml])"
hide_const (open) fail

definition guard :: "(xml \<Rightarrow> bool) \<Rightarrow> 'a xmlt \<Rightarrow> 'a xmlt \<Rightarrow> 'a xmlt"
where
  "guard p p1 p2 x = (if p x then p1 x else p2 x)"
hide_const (open) guard

lemma guard_mono [partial_function_mono]:
  assumes p1: "\<And>y. mono_sum_bot (p1 y)"
    and p2: "\<And>y. mono_sum_bot (p2 y)"
  shows "mono_sum_bot (\<lambda>g. Xmlt.guard p (\<lambda>y. p1 y g) (\<lambda>y. p2 y g) x)" 
  by (cases x) (auto intro!: partial_function_mono p1 p2 simp: Xmlt.guard_def)

fun leaf :: "tag \<Rightarrow> 'a \<Rightarrow> 'a xmlt"
where
  "leaf tag x (XML name atts cs) = 
    (if name = tag \<and> atts = [] \<and> cs = [] then return x 
    else Xmlt.fail tag (XML name atts cs))" |
  "leaf tag x xml = Xmlt.fail tag xml"
hide_const (open) leaf

fun list1element :: "'a list \<Rightarrow> 'a option"
where
  "list1element [x] = Some x" |
  "list1element _ = None"

fun singleton :: "tag \<Rightarrow> 'a xmlt \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b xmlt"
where
  "singleton tag p1 f xml =
    (case xml of
      XML name atts cs \<Rightarrow>
      (if name = tag \<and> atts = [] then
        (case list1element cs of 
          Some (cs1) \<Rightarrow> p1 cs1 \<bind> return \<circ> f
        | None \<Rightarrow> Xmlt.fail tag xml)
      else Xmlt.fail tag xml)
    | _ \<Rightarrow> Xmlt.fail tag xml)"
hide_const (open) singleton

lemma singleton_mono [partial_function_mono]:
  assumes p: "\<And>y. mono_sum_bot (p1 y)"
  shows "mono_sum_bot (\<lambda>g. Xmlt.singleton t (\<lambda>y. p1 y g) f x)" 
    by (cases x, cases "list1element (Xml.children x)") (auto intro!: partial_function_mono p)

fun list2elements :: "'a list \<Rightarrow> ('a \<times> 'a) option"
where
  "list2elements [x, y] = Some (x, y)" |
  "list2elements _ = None"

fun pair :: "tag \<Rightarrow> 'a xmlt \<Rightarrow> 'b xmlt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'c xmlt"
where
  "pair tag p1 p2 f xml =
    (case xml of
      XML name atts cs \<Rightarrow>
      (if name = tag \<and> atts = [] then
        (case list2elements cs of 
          Some (cs1, cs2) \<Rightarrow>
          do {
            a \<leftarrow> p1 cs1;
            b \<leftarrow> p2 cs2;
            return (f a b)
          }
        | None \<Rightarrow> Xmlt.fail tag xml)
      else Xmlt.fail tag xml)
    | _ \<Rightarrow> Xmlt.fail tag xml)"
hide_const (open) pair

lemma pair_mono [partial_function_mono]:
  assumes "\<And>y. mono_sum_bot (p1 y)"
    and "\<And>y. mono_sum_bot (p2 y)"
  shows "mono_sum_bot (\<lambda>g. Xmlt.pair t (\<lambda>y. p1 y g) (\<lambda> y. p2 y g) f x)"
  using assms
  by (cases x, cases "list2elements (Xml.children x)") (auto intro!: partial_function_mono)

fun list3elements :: "'a list \<Rightarrow> ('a \<times> 'a \<times> 'a) option"
where
  "list3elements [x, y, z] = Some (x, y, z)" |
  "list3elements _ = None"

fun triple :: "string \<Rightarrow> 'a xmlt \<Rightarrow> 'b xmlt \<Rightarrow> 'c xmlt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'd xmlt"
where
  "triple tag p1 p2 p3 f xml = (case xml of XML name atts cs \<Rightarrow>
    (if name = tag \<and> atts = [] then
      (case list3elements cs of 
        Some (cs1, cs2, cs3) \<Rightarrow>
        do {
          a \<leftarrow> p1 cs1;
          b \<leftarrow> p2 cs2;
          c \<leftarrow> p3 cs3;
          return (f a b c)
        }
      | None \<Rightarrow> Xmlt.fail tag xml)
    else Xmlt.fail tag xml)
  | _ \<Rightarrow> Xmlt.fail tag xml)"

lemma triple_mono [partial_function_mono]:
  assumes "\<And>y. mono_sum_bot (p1 y)"
    and "\<And>y. mono_sum_bot (p2 y)"
    and "\<And>y. mono_sum_bot (p3 y)"
  shows "mono_sum_bot (\<lambda>g. Xmlt.triple t (\<lambda>y. p1 y g) (\<lambda> y. p2 y g) (\<lambda> y. p3 y g) f x)"
  using assms
  by (cases x, cases "list3elements (Xml.children x)", auto intro!: partial_function_mono)

fun list4elements :: "'a list \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a) option"
where
  "list4elements [x, y, z, u] = Some (x, y, z, u)" |
  "list4elements _ = None"

fun
  tuple4 ::
    "string \<Rightarrow> 'a xmlt \<Rightarrow> 'b xmlt \<Rightarrow> 'c xmlt \<Rightarrow> 'd xmlt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 'e xmlt"
where
  "tuple4 tag p1 p2 p3 p4 f xml =
    (case xml of
      XML name atts cs \<Rightarrow>
        (if name = tag \<and> atts = [] then
          (case list4elements cs of 
            Some (cs1, cs2, cs3, cs4) \<Rightarrow>
            do {
              a \<leftarrow> p1 cs1;
              b \<leftarrow> p2 cs2;
              c \<leftarrow> p3 cs3;
              d \<leftarrow> p4 cs4;
              return (f a b c d)
            }
          | None \<Rightarrow> Xmlt.fail tag xml)
        else Xmlt.fail tag xml)
   | _ \<Rightarrow> Xmlt.fail tag xml)"

lemma tuple4_mono [partial_function_mono]:
  assumes "\<And>y. mono_sum_bot (p1 y)"
    and "\<And>y. mono_sum_bot (p2 y)"
    and "\<And>y. mono_sum_bot (p3 y)"
    and"\<And>y. mono_sum_bot (p4 y)"
  shows "mono_sum_bot (\<lambda>g. Xmlt.tuple4 t (\<lambda>y. p1 y g) (\<lambda> y. p2 y g) (\<lambda> y. p3 y g) (\<lambda> y. p4 y g) f x)"
  using assms
  by (cases x, cases "list4elements (Xml.children x)") (auto intro!: partial_function_mono)

fun list5elements :: "'a list \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a) option"
where
  "list5elements [x, y, z, u, v] = Some (x, y, z, u, v)" |
  "list5elements _ = None"

fun
  tuple5 ::
    "string \<Rightarrow> 'a xmlt \<Rightarrow> 'b xmlt \<Rightarrow> 'c xmlt \<Rightarrow> 'd xmlt \<Rightarrow> 'e xmlt \<Rightarrow>
      ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f) \<Rightarrow> 'f xmlt"
where
  "tuple5 tag p1 p2 p3 p4 p5 f xml =
    (case xml of
      XML name atts cs \<Rightarrow>
        (if name = tag \<and> atts = [] then
          (case list5elements cs of 
            Some (cs1,cs2,cs3,cs4,cs5) \<Rightarrow>
            do {
              a \<leftarrow> p1 cs1;
              b \<leftarrow> p2 cs2;
              c \<leftarrow> p3 cs3;
              d \<leftarrow> p4 cs4;
              e \<leftarrow> p5 cs5;
              return (f a b c d e)
            }
          | None \<Rightarrow> Xmlt.fail tag xml)
        else Xmlt.fail tag xml)
    | _ \<Rightarrow> Xmlt.fail tag xml)"

lemma tuple5_mono [partial_function_mono]:
  assumes "\<And>y. mono_sum_bot (p1 y)"
    and "\<And>y. mono_sum_bot (p2 y)"
    and "\<And>y. mono_sum_bot (p3 y)"
    and "\<And>y. mono_sum_bot (p4 y)"
    and "\<And>y. mono_sum_bot (p5 y)"
  shows "mono_sum_bot (\<lambda>g. Xmlt.tuple5 t (\<lambda>y. p1 y g) (\<lambda> y. p2 y g) (\<lambda> y. p3 y g) (\<lambda> y. p4 y g) (\<lambda> y. p5 y g) f x)"
  using assms
  by (cases x, cases "list5elements (Xml.children x)") (auto intro!: partial_function_mono)

fun list6elements :: "'a list \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a) option"
where
  "list6elements [x, y, z, u, v, w] = Some (x, y, z, u, v, w)" |
  "list6elements _ = None"

fun
  tuple6 ::
    "string \<Rightarrow> 'a xmlt \<Rightarrow> 'b xmlt \<Rightarrow> 'c xmlt \<Rightarrow> 'd xmlt \<Rightarrow> 'e xmlt \<Rightarrow> 'f xmlt \<Rightarrow>
      ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g) \<Rightarrow> 'g xmlt"
where
  "tuple6 tag p1 p2 p3 p4 p5 p6 f xml =
    (case xml of
      XML name atts cs  \<Rightarrow>
        (if name = tag \<and> atts = [] then
          (case list6elements cs of 
            Some (cs1,cs2,cs3,cs4,cs5,cs6) \<Rightarrow>
            do {
              a \<leftarrow> p1 cs1;
              b \<leftarrow> p2 cs2;
              c \<leftarrow> p3 cs3;
              d \<leftarrow> p4 cs4;
              e \<leftarrow> p5 cs5;
              ff \<leftarrow> p6 cs6;
              return (f a b c d e ff)
            }
          | None \<Rightarrow> Xmlt.fail tag xml)
        else Xmlt.fail tag xml)
    | _ \<Rightarrow> Xmlt.fail tag xml)"

lemma tuple6_mono [partial_function_mono]:
  assumes "\<And>y. mono_sum_bot (p1 y)"
    and "\<And>y. mono_sum_bot (p2 y)"
    and "\<And>y. mono_sum_bot (p3 y)"
    and "\<And>y. mono_sum_bot (p4 y)"
    and "\<And>y. mono_sum_bot (p5 y)"
    and "\<And>y. mono_sum_bot (p6 y)"
  shows "mono_sum_bot (\<lambda>g. Xmlt.tuple6 t (\<lambda>y. p1 y g) (\<lambda> y. p2 y g) (\<lambda> y. p3 y g) (\<lambda> y. p4 y g) (\<lambda> y. p5 y g) (\<lambda> y. p6 y g) f x)"
  using assms
  by (cases x, cases "list6elements (Xml.children x)") (auto intro!: partial_function_mono)

fun optional :: "tag \<Rightarrow> 'a xmlt \<Rightarrow> ('a option \<Rightarrow> 'b) \<Rightarrow> 'b xmlt"
where
  "optional tag p1 f (XML name atts cs) =
    (let l = length cs in
    (if name = tag \<and> atts = [] \<and> l \<ge> 0 \<and> l \<le> 1 then do {
      if l = 1 then do {
        x1 \<leftarrow> p1 (cs ! 0);
        return (f (Some x1))
      } else return (f None)
    } else Xmlt.fail tag (XML name atts cs)))" |
  "optional tag p1 f xml = Xmlt.fail tag xml"

lemma optional_mono [partial_function_mono]:
  assumes "\<And>y. mono_sum_bot (p1 y)"
  shows "mono_sum_bot (\<lambda>g. Xmlt.optional t (\<lambda>y. p1 y g) f x)" 
  using assms by (cases x) (auto intro!: partial_function_mono)

fun xml1to2elements :: "string \<Rightarrow> 'a xmlt \<Rightarrow> 'b xmlt \<Rightarrow> ('a \<Rightarrow> 'b option \<Rightarrow> 'c) \<Rightarrow> 'c xmlt"
where
  "xml1to2elements tag p1 p2 f (XML name atts cs) = (
     let l = length cs in
     (if name = tag \<and> atts = [] \<and> l \<ge> 1 \<and> l \<le> 2
       then do {
         x1 \<leftarrow> p1 (cs ! 0);
         (if l = 2
           then do {
             x2 \<leftarrow> p2 (cs ! 1);
             return (f x1 (Some x2))
           } else return (f x1 None))
       } else Xmlt.fail tag (XML name atts cs)))" |
  "xml1to2elements tag p1 p2 f xml = Xmlt.fail tag xml"

lemma xml1to2elements_mono[partial_function_mono]:
  assumes p1: "\<And>y. mono_sum_bot (p1 y)"
              "\<And>y. mono_sum_bot (p2 y)"
  shows "mono_sum_bot (\<lambda>g. xml1to2elements t (\<lambda>y. p1 y g) (\<lambda>y. p2 y g) f x)" 
  by (cases x, auto intro!: partial_function_mono p1)

text \<open>
  Apply the first transformer to the first child-node, then check the second child-node,
  which is must be a Boolean. If the Boolean is true, then apply the second transformer
  to the last child-node.
\<close>
fun xml2nd_choice :: "tag \<Rightarrow> 'a xmlt \<Rightarrow> tag \<Rightarrow> 'b xmlt \<Rightarrow> ('a \<Rightarrow> 'b option \<Rightarrow> 'c) \<Rightarrow> 'c xmlt"
where
  "xml2nd_choice tag p1 cn p2 f (XML name atts cs) = (
    let l = length cs in
    (if name = tag \<and> atts = [] \<and> l \<ge> 2 then do {
      x1 \<leftarrow> p1 (cs ! 0);
      b \<leftarrow> Xmlt.bool cn (cs ! 1);
      (if b then do {
        x2 \<leftarrow> p2 (cs ! (l - 1));
        return (f x1 (Some x2))
      } else return (f x1 None))
    } else Xmlt.fail tag (XML name atts cs)))" |
  "xml2nd_choice tag p1 cn p2 f xml = Xmlt.fail tag xml"

lemma xml2nd_choice_mono [partial_function_mono]:
  assumes p1: "\<And>y. mono_sum_bot (p1 y)"
              "\<And>y. mono_sum_bot (p2 y)"
  shows "mono_sum_bot (\<lambda>g. xml2nd_choice t (\<lambda>y. p1 y g) h (\<lambda>y. p2 y g) f x)" 
  by (cases x, auto intro!: partial_function_mono p1)

fun
  xml2to3elements ::
    "string \<Rightarrow> 'a xmlt \<Rightarrow> 'b xmlt \<Rightarrow> 'c xmlt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c option \<Rightarrow> 'd) \<Rightarrow> 'd xmlt"
where
  "xml2to3elements tag p1 p2 p3 f (XML name atts cs) = (
     let l = length cs in
     (if name = tag \<and> atts = [] \<and> l \<ge> 2 \<and> l \<le> 3 then do {
       x1 \<leftarrow> p1 (cs ! 0);
       x2 \<leftarrow> p2 (cs ! 1);
       (if l = 3 then do {
         x3 \<leftarrow> p3 (cs ! 2);
         return (f x1 x2 (Some x3))
       } else return (f x1 x2 None))
     } else Xmlt.fail tag (XML name atts cs)))" |
  "xml2to3elements tag p1 p2 p3 f xml = Xmlt.fail tag xml"

lemma xml2to3elements_mono [partial_function_mono]:
  assumes p1: "\<And>y. mono_sum_bot (p1 y)"
              "\<And>y. mono_sum_bot (p2 y)"
              "\<And>y. mono_sum_bot (p3 y)"
  shows "mono_sum_bot (\<lambda>g. xml2to3elements t (\<lambda>y. p1 y g) (\<lambda>y. p2 y g) (\<lambda>y. p3 y g) f x)" 
  by (cases x, auto intro!: partial_function_mono p1)

fun
  xml3to4elements ::
    "string \<Rightarrow> 'a xmlt \<Rightarrow> 'b xmlt \<Rightarrow> 'c xmlt \<Rightarrow> 'd xmlt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c option \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow>
      'e xmlt"
where
  "xml3to4elements tag p1 p2 p3 p4 f (XML name atts cs) = (
     let l = length cs in
     (if name = tag \<and> atts = [] \<and> l \<ge> 3 \<and> l \<le> 4 then do {
       x1 \<leftarrow> p1 (cs ! 0);
       x2 \<leftarrow> p2 (cs ! 1);
       (if l = 4 then do {
         x3 \<leftarrow> p3 (cs ! 2);
         x4 \<leftarrow> p4 (cs ! 3);
         return (f x1 x2 (Some x3) x4)
       } else do {
         x4 \<leftarrow> p4 (cs ! 2);
         return (f x1 x2 None x4)
       } )
     } else Xmlt.fail tag (XML name atts cs)))" |
  "xml3to4elements tag p1 p2 p3 p4 f xml = Xmlt.fail tag xml"

lemma xml3to4elements_mono [partial_function_mono]:
  assumes p1: "\<And>y. mono_sum_bot (p1 y)"
              "\<And>y. mono_sum_bot (p2 y)"
              "\<And>y. mono_sum_bot (p3 y)"
              "\<And>y. mono_sum_bot (p4 y)"
  shows "mono_sum_bot (\<lambda>g. xml3to4elements t (\<lambda>y. p1 y g) (\<lambda>y. p2 y g) (\<lambda>y. p3 y g) (\<lambda>y. p4 y g) f x)" 
  by (cases x, auto intro!: partial_function_mono p1)

fun many :: "tag \<Rightarrow> 'a xmlt \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> 'b xmlt"
where
  "many tag p f (XML name atts cs) =
    (if name = tag \<and> atts = [] then (Xmlt.map p cs \<bind> (return \<circ> f))
    else Xmlt.fail tag (XML name atts cs))" |
  "many tag p f xml = Xmlt.fail tag xml"
hide_const (open) many

lemma many_mono [partial_function_mono]:
  fixes p1 :: "xml \<Rightarrow> ('b \<Rightarrow> (string +\<^sub>\<bottom> 'c)) \<Rightarrow> string +\<^sub>\<bottom> 'd"
  assumes "\<And>y. y \<in> set (Xml.children x) \<Longrightarrow> mono_sum_bot (p1 y)"
  shows "mono_sum_bot (\<lambda>g. Xmlt.many t (\<lambda>y. p1 y g) f x)" 
  using assms by (cases x) (auto intro!: partial_function_mono)

fun many1_gen :: "tag \<Rightarrow> 'a xmlt \<Rightarrow> ('a \<Rightarrow> 'b xmlt) \<Rightarrow> ('a \<Rightarrow> 'b list \<Rightarrow> 'c) \<Rightarrow> 'c xmlt"
where
  "many1_gen tag p1 p2 f (XML name atts cs) =
    (if name = tag \<and> atts = [] \<and> cs \<noteq> [] then
      (case cs of h # t \<Rightarrow> do {
        x \<leftarrow> p1 h;
        xs \<leftarrow> Xmlt.map (p2 x) t;
        return (f x xs)
      })
    else Xmlt.fail tag (XML name atts cs))" |
  "many1_gen tag p1 p2 f xml = Xmlt.fail tag xml"

(* TODO 
lemma Xmlt.many1_gen_mono[partial_function_mono]:
  fixes p1 :: "xml \<Rightarrow> ('b \<Rightarrow> 'c sum_bot) \<Rightarrow> 'd sum_bot"
  assumes p1: "\<And>y. mono_sum_bot (p1 y)"
              "\<And>y. mono_sum_bot (p2 y)"
  shows "mono_sum_bot (\<lambda>g. Xmlt.many1_gen t (\<lambda>y. p1 y g) (\<lambda>y. p2 y g) f x)" 
  by (cases x, auto intro!: partial_function_mono p1)
*)

definition many1 :: "string \<Rightarrow> 'a xmlt \<Rightarrow> 'b xmlt \<Rightarrow> ('a \<Rightarrow> 'b list \<Rightarrow> 'c) \<Rightarrow> 'c xmlt"
where
  "many1 tag p1 p2 = Xmlt.many1_gen tag p1 (\<lambda>_. p2)"
hide_const (open) many1

lemma many1_mono [partial_function_mono]:
  fixes p1 :: "xml \<Rightarrow> ('b \<Rightarrow> (string +\<^sub>\<bottom> 'c)) \<Rightarrow> string +\<^sub>\<bottom> 'd"
  assumes "\<And>y. mono_sum_bot (p1 y)"
    and "\<And>y. y \<in> set (tl (Xml.children x)) \<Longrightarrow> mono_sum_bot (p2 y)"
  shows "mono_sum_bot (\<lambda>g. Xmlt.many1 t (\<lambda>y. p1 y g) (\<lambda>y. p2 y g) f x)" 
  unfolding Xmlt.many1_def using assms
  by (cases x, cases "Xml.children x") (auto intro!: partial_function_mono)

fun length_ge_2 :: "'a list \<Rightarrow> bool"
where 
  "length_ge_2 (_ # _ # _) = True" |
  "length_ge_2 _ = False"

fun many2 :: "tag \<Rightarrow> 'a xmlt \<Rightarrow> 'b xmlt \<Rightarrow> 'c xmlt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c list \<Rightarrow> 'd) \<Rightarrow> 'd xmlt"
where
  "many2 tag p1 p2 p3 f (XML name atts cs) =
    (if name = tag \<and> atts = [] \<and> length_ge_2 cs then
      (case cs of cs0 # cs1 # t \<Rightarrow> do {
        x \<leftarrow> p1 cs0;
        y \<leftarrow> p2 cs1;
        xs \<leftarrow> Xmlt.map p3 t;
        return (f x y xs)
      })
    else Xmlt.fail tag (XML name atts cs))" |
  "many2 tag p1 p2 p3 f xml = Xmlt.fail tag xml"

lemma many2_mono [partial_function_mono]:
  fixes p1 :: "xml \<Rightarrow> ('b \<Rightarrow> (string +\<^sub>\<bottom> 'c)) \<Rightarrow> string +\<^sub>\<bottom> 'd"
  assumes "\<And>y. mono_sum_bot (p1 y)"
    and "\<And>y. mono_sum_bot (p2 y)"
    and "\<And>y. mono_sum_bot (p3 y)"
  shows "mono_sum_bot (\<lambda>g. Xmlt.many2 t (\<lambda>y. p1 y g) (\<lambda>y. p2 y g) (\<lambda>y. p3 y g) f x)"
  using assms
  by (cases x, cases "Xml.children x", (auto intro!: partial_function_mono)[1], cases "tl (Xml.children x)", auto intro!: partial_function_mono)

fun
  xml1or2many_elements ::
    "string \<Rightarrow> 'a xmlt \<Rightarrow> 'b xmlt \<Rightarrow> 'c xmlt \<Rightarrow> ('a \<Rightarrow> 'b option \<Rightarrow> 'c list \<Rightarrow> 'd) \<Rightarrow> 'd xmlt"
where
  "xml1or2many_elements tag p1 p2 p3 f (XML name atts cs) =
    (if name = tag \<and> atts = [] \<and> cs \<noteq> [] then
      (case cs of
        cs0 # tt \<Rightarrow>
        do { 
          x \<leftarrow> p1 cs0;
          (case tt of
            cs1 # t \<Rightarrow>
            do {
              try do {
                y \<leftarrow> p2 cs1;
                xs \<leftarrow> Xmlt.map p3 t;
                return (f x (Some y) xs)
              } catch (\<lambda> _. do {
                xs \<leftarrow> Xmlt.map p3 tt;
                return (f x None xs)
              })
            }
          | [] \<Rightarrow> return (f x None []))}) 
     else Xmlt.fail tag (XML name atts cs))" |
  "xml1or2many_elements tag p1 p2 p3 f  xml = Xmlt.fail tag xml"

fun
  xml1many2elements_gen ::
    "string \<Rightarrow> 'a xmlt \<Rightarrow> ('a \<Rightarrow> 'b xmlt) \<Rightarrow> 'c xmlt \<Rightarrow> 'd xmlt \<Rightarrow>
      ('a \<Rightarrow> 'b list \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> 'e xmlt"
where
  "xml1many2elements_gen tag p1 p2 p3 p4 f (XML name atts cs) = (
     let ds = List.rev cs; l = length cs in
     (if name = tag \<and> atts = [] \<and> l \<ge> 3 then do {
       x \<leftarrow> p1 (cs ! 0);
       xs \<leftarrow> Xmlt.map (p2 x) (tl (take (l - 2) cs));
       y \<leftarrow> p3 (ds ! 1);
       z \<leftarrow> p4 (ds ! 0);
       return (f x xs y z)
     } else Xmlt.fail tag (XML name atts cs)))" |
  "xml1many2elements_gen tag p1 p2 p3 p4 f xml = Xmlt.fail tag xml"

lemma xml1many2elements_gen_mono [partial_function_mono]:
  fixes p1 :: "xml \<Rightarrow> ('b \<Rightarrow> (string +\<^sub>\<bottom> 'c)) \<Rightarrow> string +\<^sub>\<bottom> 'd"
  assumes p1: "\<And>y. mono_sum_bot (p1 y)"
              "\<And>y. mono_sum_bot (p3 y)"
              "\<And>y. mono_sum_bot (p4 y)"
  shows "mono_sum_bot (\<lambda>g. xml1many2elements_gen t (\<lambda>y. p1 y g) p2 (\<lambda>y. p3 y g) (\<lambda>y. p4 y g) f x)" 
  by (cases x, auto intro!: partial_function_mono p1)

fun
  xml1many2elements ::
    "string \<Rightarrow> 'a xmlt \<Rightarrow> 'b xmlt \<Rightarrow> 'c xmlt \<Rightarrow> 'd xmlt \<Rightarrow> ('a \<Rightarrow> 'b list \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow>
      'e xmlt"
where
  "xml1many2elements tag p1 p2 = xml1many2elements_gen tag p1 (\<lambda>_. p2)"

fun
  xml_many2elements ::
    "string \<Rightarrow> 'a xmlt \<Rightarrow> 'b xmlt \<Rightarrow> 'c xmlt \<Rightarrow> ('a list \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'd xmlt"
where
  "xml_many2elements tag p1 p2 p3 f (XML name atts cs) = (
     let ds = List.rev cs in
     (if name = tag \<and> atts = [] \<and> length_ge_2 cs then do {
       xs \<leftarrow> Xmlt.map p1 (List.rev (tl (tl ds)));
       y \<leftarrow> p2 (ds ! 1);
       z \<leftarrow> p3 (ds ! 0);
       return (f xs y z)
     } else Xmlt.fail tag (XML name atts cs)))" |
  "xml_many2elements tag p1 p2 p3 f xml = Xmlt.fail tag xml"

definition options :: "(string \<times> 'a xmlt) list \<Rightarrow> 'a xmlt"
where
  "options ps x =
    (case map_of ps (Xml.tag x) of 
      None \<Rightarrow> error (concat
        [''expected one of: '', concat (map (\<lambda>p. fst p @ '' '') ps), ''\<newline>'', ''but found'', ''\<newline>'', show x])
    | Some p \<Rightarrow> p x)"
hide_const (open) options

lemma options_mono_gen [partial_function_mono]:
  assumes p: "\<And> k p. (k, p) \<in> set ps \<Longrightarrow> mono_sum_bot (p x)"
  shows "mono_sum_bot (\<lambda> g. Xmlt.options (map (\<lambda> (k, p). (k, (\<lambda> y. p y g))) ps) x)"
proof -
  {
    fix g
    have "(map (\<lambda>p. fst p @ '' '') (map (\<lambda>(k, p). (k, \<lambda>y. p y g)) ps)) = 
      map (\<lambda>p. fst p @ '' '') ps"
      by (induct ps) (auto)
  } note id = this
  {
    fix z
    have "mono_sum_bot
      (\<lambda>g. case map_of (map (\<lambda>(k, p). (k, \<lambda>y. p y g)) ps) (Xml.tag x) of
        None \<Rightarrow> z
      | Some p \<Rightarrow> p x)"
      using p
    proof (induct ps)
      case Nil
      show ?case by (auto intro: partial_function_mono)
    next
      case (Cons kp ps)
      obtain k p where kp: "kp = (k,p)" by force
      note Cons = Cons[unfolded kp]
      from Cons(2) have monop: "mono_sum_bot (p x)" and mono: "\<And> k p. (k,p) \<in> set ps \<Longrightarrow> mono_sum_bot (p x)" by auto
      show ?case 
      proof (cases "Xml.tag x = k")
        case True
        thus ?thesis unfolding kp using monop by auto
      next
        case False
        thus ?thesis using Cons(1) mono unfolding kp by auto
      qed
    qed
  } note main = this
  show ?thesis unfolding Xmlt.options_def 
    unfolding id
    by (rule main)
qed

(* instantiate this lemma to have the monotonicity lemmas for lists of variable lengths which
   are then applicable, e.g., for lists of length 3 it would be

mono_sum_bot (p1 x) \<Longrightarrow> mono_sum_bot (p2 x) \<Longrightarrow> mono_sum_bot (p3 x) 
\<Longrightarrow> mono_sum_bot (\<lambda>g. Xmlt.options [(k1, \<lambda>y. p1 y g), (k2, \<lambda>y. p2 y g), (k3, \<lambda>y. p3 y g)] x)

*)
local_setup \<open>fn lthy => 
  let
    val N = 30 (* we require monotonicity lemmas for xml-options for lists up to length N *) 
    val thy = Proof_Context.theory_of lthy
    val options = @{term "Xmlt.options :: (string \<times> (xml \<Rightarrow> (string +\<^sub>\<bottom> 'd))) list \<Rightarrow> xml \<Rightarrow> string +\<^sub>\<bottom> 'd"}
    val mono_sum_bot = @{term "mono_sum_bot :: (('a \<Rightarrow> ('b +\<^sub>\<bottom> 'c)) \<Rightarrow> string +\<^sub>\<bottom> 'd) \<Rightarrow> bool"}
    val ktyp = @{typ string}
    val x = @{term "x :: xml"}
    val y = @{term "y :: xml"}
    val g = @{term "g :: 'a \<Rightarrow> 'b +\<^sub>\<bottom> 'c"}
    val ptyp = @{typ "xml \<Rightarrow> ('a \<Rightarrow> ('b +\<^sub>\<bottom> 'c)) \<Rightarrow> string +\<^sub>\<bottom> 'd"}
    fun k i = Free ("k" ^ string_of_int i,ktyp)
    fun p i = Free ("p" ^ string_of_int i,ptyp)
    fun prem i = HOLogic.mk_Trueprop (mono_sum_bot $ (p i $ x))
    fun prems n = 1 upto n |> map prem
    fun pair i = HOLogic.mk_prod (k i, lambda y (p i $ y $ g))
    fun pair2 i = HOLogic.mk_prod (k i, p i)
    fun list n = 1 upto n |> map pair |> HOLogic.mk_list @{typ "(string \<times> (xml \<Rightarrow> string +\<^sub>\<bottom> 'd))"}
    fun list2 n = 1 upto n |> map pair2 |> HOLogic.mk_list (HOLogic.mk_prodT (ktyp,ptyp))
    fun concl n = HOLogic.mk_Trueprop (mono_sum_bot $ lambda g (options $ (list n) $ x))
    fun xs n = x :: (1 upto n |> map (fn i => [p i, k i]) |> List.concat)
       |> map (fst o dest_Free)
    fun tac n pc =
      let
        val {prems = prems, context = ctxt} = pc
        val mono_thm = Thm.instantiate' 
            (map (SOME o Thm.ctyp_of ctxt) [@{typ 'a},@{typ 'b},@{typ 'c},@{typ 'd}]) 
            (map (SOME o Thm.cterm_of ctxt) [list2 n,x]) @{thm Xmlt.options_mono_gen}
      in 
        Method.insert_tac ctxt (mono_thm :: prems) 1 THEN force_tac ctxt 1
      end
    fun thm n = Goal.prove lthy (xs n) (prems n) (concl n) (tac n)
    val thms = map thm (0 upto N)
  in Local_Theory.note ((@{binding "options_mono_thms"}, []), thms) lthy |> snd end
\<close>

declare Xmlt.options_mono_thms [partial_function_mono]

fun choice :: "string \<Rightarrow> 'a xmlt list \<Rightarrow> 'a xmlt"
where
  "choice e [] x = error (concat [''error in parsing choice for '', e, ''\<newline>'', show x])" |
  "choice e (p # ps) x = (try p x catch (\<lambda>_. choice e ps x))"
hide_const (open) choice

lemma choice_mono_2 [partial_function_mono]:
  assumes p: "mono_sum_bot (p1 x)"
             "mono_sum_bot (p2 x)"
  shows "mono_sum_bot (\<lambda> g. Xmlt.choice e [(\<lambda> y. p1 y g), (\<lambda> y. p2 y g)] x)"
  using p by (auto intro!: partial_function_mono) 

lemma choice_mono_3 [partial_function_mono]:
  assumes p: "mono_sum_bot (p1 x)"
             "mono_sum_bot (p2 x)"
             "mono_sum_bot (p3 x)"
  shows "mono_sum_bot (\<lambda> g. Xmlt.choice e [(\<lambda> y. p1 y g), (\<lambda> y. p2 y g), (\<lambda> y. p3 y g)] x)"
  using p by (auto intro!: partial_function_mono) 

fun change :: "'a xmlt \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b xmlt"
where
  "change p f x = p x \<bind> return \<circ> f"
hide_const (open) change

lemma change_mono [partial_function_mono]:
  assumes p: "\<And>y. mono_sum_bot (p1 y)"
  shows "mono_sum_bot (\<lambda>g. Xmlt.change (\<lambda>y. p1 y g) f x)" 
  by (cases x, insert p, auto intro!: partial_function_mono)

fun int_of_digit :: "char \<Rightarrow> string +\<^sub>\<bottom> int"
where
  "int_of_digit x =
    (if x = CHR ''0'' then return 0
    else if x = CHR ''1'' then return 1
    else if x = CHR ''2'' then return 2
    else if x = CHR ''3'' then return 3
    else if x = CHR ''4'' then return 4
    else if x = CHR ''5'' then return 5
    else if x = CHR ''6'' then return 6
    else if x = CHR ''7'' then return 7
    else if x = CHR ''8'' then return 8
    else if x = CHR ''9'' then return 9
    else error (x # '' is not a digit''))"

fun int_of_string_aux :: "int \<Rightarrow> string \<Rightarrow> string +\<^sub>\<bottom> int"
where
  "int_of_string_aux n [] = return n" |
  "int_of_string_aux n (d # s) = (int_of_digit d \<bind> (\<lambda>m. int_of_string_aux (10 * n + m) s))"

definition int_of_string :: "string \<Rightarrow> string +\<^sub>\<bottom> int"
where
  "int_of_string s =
    (if s = [] then error ''cannot convert empty string into number'' 
    else if take 1 s = ''-'' then int_of_string_aux 0 (tl s) \<bind> (\<lambda> i. return (0 - i))
    else int_of_string_aux 0 s)"

hide_const int_of_string_aux

fun int :: "tag \<Rightarrow> int xmlt"
where
  "int tag x = (Xmlt.text tag x \<bind> int_of_string)"
hide_const (open) int

fun nat :: "tag \<Rightarrow> nat xmlt"
where
  "nat tag x = do {
    txt \<leftarrow> Xmlt.text tag x;
    i \<leftarrow> int_of_string txt;
    return (Int.nat i)
  }"
hide_const (open) nat

definition rat :: "rat xmlt"
where
  "rat = Xmlt.options [
    (''integer'', Xmlt.change (Xmlt.int ''integer'') of_int),
    (''rational'',
      Xmlt.pair ''rational'' (Xmlt.int ''numerator'') (Xmlt.int ''denominator'')
        (\<lambda> x y. of_int x / of_int y))]"
hide_const (open) rat

end

