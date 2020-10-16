section \<open>Performance Test\<close>
theory Test
  imports Dijkstra_Impl_Adet
begin
text \<open>
  In this theory, we test our implementation of Dijkstra's algorithm for larger,
  randomly generated graphs.
\<close>

text "Simple linear congruence generator for (low-quality) random numbers:"
definition "lcg_next s = ((81::nat)*s + 173) mod 268435456" 

text "Generate a complete graph over the given number of vertices,
    with random weights:"
definition ran_graph :: "nat \<Rightarrow> nat \<Rightarrow> (nat list\<times>(nat \<times> nat \<times> nat) list)" where
  "ran_graph vertices seed == 
    ([0::nat..<vertices],fst 
     (while (\<lambda> (g,v,s). v < vertices)
     (\<lambda> (g,v,s). 
     let (g'',v'',s'') = (while (\<lambda> (g',v',s'). v' < vertices)
      (\<lambda> (g',v',s'). ((v,s',v')#g',v'+1,lcg_next s'))
      (g,0,s))
     in (g'',v+1,s''))
     ([],0,lcg_next seed)))"


text \<open>
  To experiment with the exported code, we fix the node type to natural numbers,
  and add a from-list conversion:
\<close>
type_synonym nat_res = "(nat,((nat,nat) path \<times> nat)) rm"
type_synonym nat_list_res = "(nat \<times> (nat,nat) path \<times> nat) list"

definition nat_dijkstra :: "(nat,nat) hlg \<Rightarrow> nat \<Rightarrow> nat_res" where
  "nat_dijkstra \<equiv> hrfn_dijkstra"

definition hlg_from_list_nat :: "(nat,nat) adj_list \<Rightarrow>(nat,nat) hlg" where 
  "hlg_from_list_nat \<equiv> hlg.from_list"

definition 
  nat_res_to_list :: "nat_res \<Rightarrow> nat_list_res" 
  where "nat_res_to_list \<equiv> rm.to_list"

value "nat_res_to_list (nat_dijkstra (hlg_from_list_nat (ran_graph 4 8912)) 0)"

ML_val \<open>
let
  (* Configuration of test: *)
  val vertices = @{code nat_of_integer} 1000; (* Number of vertices *)
  val seed = @{code nat_of_integer} 123454; (* Seed for random number generator *)
  val cfg_print_paths = true; (* Whether to output complete paths *)
  val cfg_print_res = true; (* Whether to output result at all *)

  (* Internals *)
  fun string_of_edge (u,(w,v)) = let
    val u = @{code integer_of_nat} u;
    val w = @{code integer_of_nat} w;
    val v = @{code integer_of_nat} v;
  in
    "(" ^ string_of_int u ^ "," ^ string_of_int w ^ "," ^ string_of_int v ^ ")"
  end

  fun print_entry (dest,(path,weight)) = let
    val dest = @{code integer_of_nat} dest;
    val weight = @{code integer_of_nat} weight;
  in
    writeln (string_of_int dest ^ ": " ^ string_of_int weight ^
      ( if cfg_print_paths then 
          " via [" ^ commas (map string_of_edge (rev path)) ^ "]"
        else ""
      )
    )
  end

  fun print_res [] = ()
    | print_res (a::l) = let val _ = print_entry a in print_res l end;

  val start = Time.now();
  val graph = @{code hlg_from_list_nat} (@{code ran_graph} vertices seed);
  val rt1 = Time.toMilliseconds (Time.now() - start);

  val start = Time.now();
  val res = @{code nat_dijkstra} graph (@{code nat_of_integer} 0);
  val rt2 = Time.toMilliseconds (Time.now() - start);
in
  writeln (string_of_int (@{code integer_of_nat} vertices) ^ " vertices: " 
  ^ string_of_int rt2 ^ " ms + "
  ^ string_of_int rt1 ^ " ms to create graph = " 
  ^ string_of_int (rt1+rt2) ^ " ms");

  if cfg_print_res then
    print_res (@{code nat_res_to_list} res)
  else ()
end;
\<close>

end
