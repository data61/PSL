(*  Author: Tobias Nipkow  *)  (* FIXME dead code!? *)

theory ArchStat
imports TameEnum ArchCompAux
begin

definition stat :: "nat fgraph list \<Rightarrow> nat * nat * nat * nat * nat" where
"stat A =
 (length A,
  foldl (\<lambda>x y. if x<y then y else x) 0 (map length A),
  foldl (+) 0 (map length A),
  foldl (\<lambda>x y. if x<y then y else x)  0 (map nof_vertices A),
  foldl (+) 0 (map nof_vertices A)
 )"

value "stat Tri"
value "stat Quad"
value "stat Pent"
value "stat Hex"

(* nof graphs, max nof faces, total nof faces, max nof vertices, total nof vertices *)
(* NEW
3: (9, 26, 212, 15, 124)
4: (1105, 25, 21787, 15, 15015)
5: (15991, 24, 294921, 15, 221421)
6: (1657, 23, 31169, 15, 23071)
*)
(* OLD *)
(* 3: (  20, 32,   440, 18,   260) *)
(* 4: ( 923, 29, 16533, 18, 11444) *)
(* 5: (1545, 26, 27223, 17, 19668) *)
(* 6: ( 238, 24,  4045, 16,  2970) *)
(* 7: (  23, 18,   357, 13,   278) *)
(* 8: (  22, 19,   333, 14,   266) *)

type_synonym config = "(nat,nat fgraph)tries * nat * nat"
fun insert_mod :: "graph \<Rightarrow> config \<Rightarrow> config" where
"insert_mod x (t,tot,fins) =
 (if final x
  then
    let
      fg = fgraph x; h = hash fg; ys = Tries.lookup t h;
      t' = if (\<exists>y:set ys. iso_test fg y) then t else Tries.update t h (fg#ys)
    in (t', tot+1, fins+1)
  else (t,tot+1,fins))"

definition worklist_collect_aux ::
  "(graph \<Rightarrow> graph list) \<Rightarrow> graph list \<Rightarrow> config \<Rightarrow> config option"
where
"worklist_collect_aux succs = worklist_dfs succs insert_mod"

fun stat_of_tries where
"stat_of_tries(Tries vs al) =
   (if vs=[] then [] else [length vs]) @
   concat(map (\<lambda>(a,t). stat_of_tries t) al)"

definition "avgmax ns = (listsum ns, length ns, max_list ns)"

definition count where
"count p =
 (case worklist_collect_aux (next_tame p) [Seed p] (Tries [] [],1,0) of
  None \<Rightarrow> None |
  Some(t,n,f) \<Rightarrow> Some(avgmax(stat_of_tries t),n,f))"


(* (total number of entries, number of leaves, max number of enries per leaf),
   total number of graphs, number of final graphs
*)
value "count 0" (* (9, 6, 3), 312764, 501 *)
value "count 1" (* (1105, 418, 17), 134291356, 27050 *)
value "count 2" (* (15991, 5189, 97), 1401437009, 301560 *)
value "count 3" (* (1657, 498, 35), 334466383, 19120 *)
(* 11 hours *)
end
(* OLD *)
(* 3:    (58021,   793) *)
(* 4:  (5631754, 17486) in 30 *)
(* 5: (11444023, 15746) in 50 *)
(* 6:  (3728798,  2499) in 15 *)
(* 7:   (766463,   273) in  3 *)
(* 8:  (1402944,   234) in  6 *)
(* sum: 23069034 *)

