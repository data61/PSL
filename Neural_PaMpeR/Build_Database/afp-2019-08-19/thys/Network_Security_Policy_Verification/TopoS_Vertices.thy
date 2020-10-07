theory TopoS_Vertices
imports Main 
"HOL-Library.Char_ord" (*order on char*)
"HOL-Library.List_Lexorder" (*order on strings*)
begin


section\<open>A type for vertices\<close>

text\<open>
This theory makes extensive use of graphs.
We define a typeclass \<open>vertex\<close> for the vertices we will use in our theory.
The vertices will correspond to network or policy entities.

Later, we will conduct some proves by providing counterexamples.
Therefore, we say that the type of a vertex has at least three pairwise distinct members.

For example, the types @{typ "string"}, @{typ nat}, @{typ "bool \<times> bool"} and many other fulfill this assumption. 
The type @{typ "bool"} alone does not fulfill this assumption, because it only has two elements.

This is only a constraint over the type, of course, a policy with less than three entities can also be verified.

TL;DR: We define @{typ "'a"} \<open>vertex\<close>, which is as good as @{typ "'a"}.
\<close>


\<comment> \<open>We need at least some vertices available for a graph ...\<close>
class vertex =
  fixes vertex_1 :: "'a"
  fixes vertex_2 :: "'a"
  fixes vertex_3 :: "'a"
  assumes distinct_vertices: "distinct [vertex_1, vertex_2, vertex_3]"
begin
  lemma distinct_vertices12[simp]: "vertex_1 \<noteq> vertex_2" using distinct_vertices by(simp)
  lemma distinct_vertices13[simp]: "vertex_1 \<noteq> vertex_3" using distinct_vertices by(simp)
  lemma distinct_vertices23[simp]: "vertex_2 \<noteq> vertex_3" using distinct_vertices by(simp)
  
  lemmas distinct_vertices_sym = distinct_vertices12[symmetric] distinct_vertices13[symmetric]
          distinct_vertices23[symmetric]
  declare distinct_vertices_sym[simp]
end


text \<open>Numbers, chars and strings are good candidates for vertices.\<close>

instantiation nat::vertex
begin
  definition "vertex_1_nat" ::nat where "vertex_1 \<equiv> (1::nat)"
  definition "vertex_2_nat" ::nat where "vertex_2 \<equiv> (2::nat)"
  definition "vertex_3_nat" ::nat where "vertex_3 \<equiv> (3::nat)"
instance proof qed(simp add: vertex_1_nat_def vertex_2_nat_def vertex_3_nat_def)
end
value "vertex_1::nat"

instantiation int::vertex
begin
  definition "vertex_1_int" ::int where "vertex_1 \<equiv> (1::int)"
  definition "vertex_2_int" ::int where "vertex_2 \<equiv> (2::int)"
  definition "vertex_3_int" ::int where "vertex_3 \<equiv> (3::int)"
instance proof qed(simp add: vertex_1_int_def vertex_2_int_def vertex_3_int_def)
end

instantiation char::vertex
begin
  definition "vertex_1_char" ::char where "vertex_1 \<equiv> CHR ''A''"
  definition "vertex_2_char" ::char where "vertex_2 \<equiv> CHR ''B''"
  definition "vertex_3_char" ::char where "vertex_3 \<equiv> CHR ''C''"
instance proof(intro_classes) qed(simp add: vertex_1_char_def  vertex_2_char_def vertex_3_char_def)
end
value "vertex_1::char"


instantiation list :: ("vertex") vertex
begin
  definition "vertex_1_list" where "vertex_1 \<equiv> []"
  definition "vertex_2_list" where "vertex_2 \<equiv> [vertex_1]"
  definition "vertex_3_list" where "vertex_3 \<equiv> [vertex_1, vertex_1]"
instance proof qed(simp add: vertex_1_list_def vertex_2_list_def vertex_3_list_def)
end

\<comment> \<open>for the ML graphviz visualizer\<close>
ML \<open>
fun tune_string_vertex_format (t: term) (s: string) : string = 
    if fastype_of t = @{typ string} then
      if String.isPrefix "''" s then
        String.substring (s, (size "''"), (size s - (size "''''")))
      else let val _ = writeln ("no tune_string_vertex_format for \""^s^"\"") in s end
    else s
    handle Subscript => let val _ = writeln ("tune_string_vertex_format Subscript excpetion") in s end;
\<close>


  
end
