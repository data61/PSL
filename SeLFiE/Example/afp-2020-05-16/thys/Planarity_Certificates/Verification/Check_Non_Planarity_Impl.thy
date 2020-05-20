section \<open>Implementation of a Non-Planarity Checker\<close>

theory Check_Non_Planarity_Impl
imports
  Simpl.Vcg
  Simpl_Anno
  Graph_Theory.Graph_Theory
begin

subsection \<open>An abstract graph datatype\<close>

type_synonym ig_vertex = nat
type_synonym ig_edge = "ig_vertex \<times> ig_vertex"

typedef IGraph = "{(vs :: ig_vertex list, es :: ig_edge list). distinct vs}"
  by auto

definition ig_verts :: "IGraph \<Rightarrow> ig_vertex list" where
  "ig_verts G \<equiv> fst (Rep_IGraph G)"

definition ig_arcs :: "IGraph \<Rightarrow> ig_edge list" where
  "ig_arcs G \<equiv> snd (Rep_IGraph G)"

definition ig_verts_cnt :: "IGraph \<Rightarrow> nat"
  where "ig_verts_cnt G \<equiv> length (ig_verts G)"

definition ig_arcs_cnt :: "IGraph \<Rightarrow> nat"
  where "ig_arcs_cnt G \<equiv> length (ig_arcs G)"

declare ig_verts_cnt_def[simp]
declare ig_arcs_cnt_def[simp]

definition IGraph_inv :: "IGraph \<Rightarrow> bool" where
  "IGraph_inv G \<equiv> (\<forall>e \<in> set (ig_arcs G). fst e \<in> set (ig_verts G) \<and> snd e \<in> set (ig_verts G))"

definition ig_empty :: "IGraph" where
  "ig_empty \<equiv> Abs_IGraph ([],[])"

definition ig_add_v :: "IGraph \<Rightarrow> ig_vertex \<Rightarrow> IGraph" where
  "ig_add_v G v = (if v \<in> set (ig_verts G) then G else Abs_IGraph (ig_verts G @ [v], ig_arcs G ))"

definition ig_add_e :: "IGraph \<Rightarrow> ig_vertex \<Rightarrow> ig_vertex \<Rightarrow> IGraph" where
  "ig_add_e G u v \<equiv> Abs_IGraph (ig_verts G, ig_arcs G @ [(u,v)])"

definition ig_in_out_arcs :: "IGraph \<Rightarrow> ig_vertex \<Rightarrow> ig_edge list" where
  "ig_in_out_arcs G u \<equiv> filter (\<lambda>e. fst e = u \<or> snd e = u) (ig_arcs G)"

definition ig_opposite :: "IGraph \<Rightarrow> ig_edge \<Rightarrow> ig_vertex \<Rightarrow> ig_vertex" where
  "ig_opposite G e u = (if fst e = u then snd e else fst e)"

definition ig_neighbors :: "IGraph => ig_vertex => ig_vertex set" where
  "ig_neighbors G u \<equiv> {v \<in> set (ig_verts G). (u,v) \<in> set (ig_arcs G) \<or> (v,u) \<in> set (ig_arcs G)}"



subsection \<open>Code\<close>

procedures is_subgraph (G :: IGraph, H :: IGraph | R :: bool)
  where
    i :: nat
    v :: "ig_vertex"
    ends :: "ig_edge"
  in "
    TRY
      \<acute>i :== 0 ;;
      WHILE \<acute>i < ig_verts_cnt \<acute>G INV named_loop ''verts''
      DO
        \<acute>v :== ig_verts \<acute>G ! \<acute>i ;;
        IF \<acute>v \<notin> set (ig_verts \<acute>H) THEN
          RAISE \<acute>R :== False
        FI ;;
        \<acute>i :== \<acute>i + 1
      OD ;;

      \<acute>i :== 0 ;;
      WHILE \<acute>i < ig_arcs_cnt \<acute>G INV named_loop ''arcs''
      DO
        \<acute>ends :== ig_arcs \<acute>G ! \<acute>i ;;
        IF \<acute>ends \<notin> set (ig_arcs \<acute>H) \<and> (snd \<acute>ends, fst \<acute>ends) \<notin> set (ig_arcs \<acute>H) THEN
          RAISE \<acute>R :== False
        FI ;;
        IF fst \<acute>ends \<notin> set (ig_verts \<acute>G) \<or> snd \<acute>ends \<notin> set (ig_verts \<acute>G) THEN
          RAISE \<acute>R :== False
        FI ;;
        \<acute>i :== \<acute>i + 1
      OD ;;
      \<acute>R :== True
    CATCH SKIP END
  "

procedures is_loopfree (G :: IGraph | R :: bool)
  where
    i :: nat
    ends :: "ig_edge"
    edge_map :: "ig_edge \<Rightarrow> bool"
  in "
    TRY
      \<acute>i :== 0 ;;
      WHILE \<acute>i < ig_arcs_cnt \<acute>G INV named_loop ''loop''
      DO
        \<acute>ends :== ig_arcs \<acute>G ! \<acute>i ;;
        IF fst \<acute>ends = snd \<acute>ends THEN
          RAISE \<acute>R :== False
        FI ;;
        \<acute>i :== \<acute>i + 1
      OD ;;
      \<acute>R :== True
    CATCH SKIP END
  "


procedures select_nodes (G :: IGraph | R :: IGraph)
  where
    i :: nat
    v :: ig_vertex
  in "
    \<acute>R :== ig_empty ;;

    \<acute>i :== 0 ;;
    WHILE \<acute>i < ig_verts_cnt \<acute>G
    INV named_loop ''loop''
    DO
      \<acute>v :== ig_verts \<acute>G ! \<acute>i ;;
      IF 2 < card (ig_neighbors \<acute>G \<acute>v) THEN
        \<acute>R :== ig_add_v \<acute>R \<acute>v
      FI ;;
      \<acute>i :== \<acute>i + 1
    OD
  "

procedures find_endpoint (G :: IGraph, H :: IGraph,  v_tail :: ig_vertex, v_next :: ig_vertex | R :: "ig_vertex option")
  where
    found :: bool
    i :: nat
    len :: nat
    io_arcs :: "ig_edge list"
    v0 :: ig_vertex
    v1 :: ig_vertex
    vt :: ig_vertex
  in "
    TRY
      IF \<acute>v_tail = \<acute>v_next THEN RAISE \<acute>R :== None FI ;;
      \<acute>v0 :== \<acute>v_tail ;;
      \<acute>v1 :== \<acute>v_next ;;
      \<acute>len :== 1 ;;
      WHILE \<acute>v1 \<notin> set (ig_verts \<acute>H)
      INV named_loop ''path''
      DO
        \<acute>io_arcs :== ig_in_out_arcs \<acute>G \<acute>v1 ;;
        \<acute>i :== 0 ;;
        \<acute>found :== False ;;
        WHILE \<acute>found = False \<and> \<acute>i < length \<acute>io_arcs
        INV named_loop ''arcs''
        DO
          \<acute>vt :== ig_opposite \<acute>G (\<acute>io_arcs ! \<acute>i) \<acute>v1 ;;
          IF \<acute>vt \<noteq> \<acute>v0 THEN
            \<acute>found :== True ;;
            \<acute>v0 :== \<acute>v1 ;;
            \<acute>v1 :== \<acute>vt
          FI ;;
          \<acute>i :== \<acute>i + 1
        OD ;;
        \<acute>len :== \<acute>len + 1 ;;
        IF \<not> \<acute>found THEN RAISE \<acute>R :== None FI
      OD ;;
      IF \<acute>v1 = \<acute>v_tail THEN RAISE \<acute>R :== None FI ;;
      \<acute>R :== Some \<acute>v1
    CATCH SKIP END
  "

procedures contract (G :: IGraph, H :: IGraph | R :: "IGraph")
  where
    i :: nat
    j :: nat
    u :: ig_vertex
    v :: ig_vertex
    vo :: "ig_vertex option"
    io_arcs :: "ig_edge list"
  in "
    \<acute>i :== 0 ;;
    WHILE \<acute>i < ig_verts_cnt \<acute>H
    INV named_loop ''iter_nodes''
    DO
      \<acute>u :== ig_verts \<acute>H ! \<acute>i ;;
      \<acute>io_arcs :== ig_in_out_arcs \<acute>G \<acute>u ;;

      \<acute>j :== 0 ;;
      WHILE \<acute>j < length \<acute>io_arcs
      INV named_loop ''iter_adj''
      DO
        \<acute>v :== ig_opposite \<acute>G (\<acute>io_arcs ! \<acute>j) \<acute>u ;;
        \<acute>vo :== CALL find_endpoint(\<acute>G, \<acute>H, \<acute>u, \<acute>v) ;;
        IF \<acute>vo \<noteq> None THEN
          \<acute>H :== ig_add_e \<acute>H \<acute>u (the \<acute>vo)
        FI ;;
        \<acute>j :== \<acute>j + 1
      OD ;;
      \<acute>i :== \<acute>i + 1
    OD ;;
    \<acute>R :== \<acute>H
  "

procedures is_K33 (G :: IGraph | R :: bool)
  where
    i :: nat
    j :: nat
    u :: ig_vertex
    v :: ig_vertex
    blue :: "ig_vertex \<Rightarrow> bool"
    blue_cnt :: nat
    io_arcs :: "ig_edge list"
  in "
    TRY
      IF ig_verts_cnt \<acute>G \<noteq> 6 THEN RAISE \<acute>R :== False FI ;;
      \<acute>blue :== (\<lambda>_. False) ;;

      \<acute>u :== ig_verts \<acute>G ! 0 ;;
      \<acute>i :== 0 ;;
      \<acute>io_arcs :== ig_in_out_arcs \<acute>G \<acute>u ;;

      WHILE \<acute>i < length \<acute>io_arcs INV named_loop ''colorize''
      DO
        \<acute>v :== ig_opposite \<acute>G (\<acute>io_arcs ! \<acute>i) \<acute>u ;;
        \<acute>blue :== \<acute>blue(\<acute>v := True) ;;
        \<acute>i :== \<acute>i + 1
      OD ;;

      \<acute>blue_cnt :== 0 ;;
      \<acute>i :== 0 ;;
      WHILE \<acute>i < ig_verts_cnt \<acute>G INV named_loop ''component_size''
      DO
        IF \<acute>blue (ig_verts \<acute>G ! \<acute>i) THEN \<acute>blue_cnt :== \<acute>blue_cnt + 1 FI ;;
        \<acute>i :== \<acute>i + 1
      OD ;;
      IF \<acute>blue_cnt \<noteq> 3 THEN RAISE \<acute>R :== False FI ;;

      \<acute>i :== 0 ;;
      WHILE \<acute>i < ig_verts_cnt \<acute>G INV named_loop ''connected_outer''
      DO
        \<acute>u :== ig_verts \<acute>G ! \<acute>i ;;
        \<acute>j :== 0 ;;
        WHILE \<acute>j < ig_verts_cnt \<acute>G INV named_loop ''connected_inner''
        DO
          \<acute>v :== ig_verts \<acute>G ! \<acute>j ;;
          IF \<not>((\<acute>blue \<acute>u = \<acute>blue \<acute>v) \<longleftrightarrow> (\<acute>u, \<acute>v) \<notin> set (ig_arcs \<acute>G)) THEN RAISE \<acute>R :== False FI ;;
          \<acute>j :== \<acute>j + 1
        OD ;;
        \<acute>i :== \<acute>i + 1
      OD ;;
      \<acute>R :== True
    CATCH SKIP END
  "

procedures is_K5 (G :: IGraph | R :: bool)
  where
    i :: nat
    j :: nat
    u :: ig_vertex
  in "
    TRY
      IF ig_verts_cnt \<acute>G \<noteq> 5 THEN RAISE \<acute>R :== False FI ;;
      \<acute>i :== 0 ;;
      WHILE \<acute>i < 5 INV named_loop ''outer_loop''
        DO
        \<acute>u :== ig_verts \<acute>G ! \<acute>i ;;
        \<acute>j :== 0 ;;
        WHILE \<acute>j < 5 INV named_loop ''inner_loop''
        DO
          IF \<not>(\<acute>i \<noteq> \<acute>j \<longleftrightarrow> (\<acute>u, ig_verts \<acute>G ! \<acute>j) \<in> set (ig_arcs \<acute>G))
          THEN
            RAISE \<acute>R :== False
          FI ;;
          \<acute>j :== \<acute>j + 1
        OD ;;
        \<acute>i :== \<acute>i + 1
      OD ;;
      \<acute>R :== True
    CATCH SKIP END
  "

procedures check_kuratowski (G :: IGraph, K :: IGraph | R :: bool)
  where
    H :: IGraph
  in "
    TRY
      \<acute>R :== CALL is_subgraph(\<acute>K, \<acute>G) ;;
      IF \<not>\<acute>R THEN RAISE \<acute>R :== False FI ;;
      \<acute>R :== CALL is_loopfree(\<acute>K) ;;
      IF \<not>\<acute>R THEN RAISE \<acute>R :== False FI ;;
      \<acute>H :== CALL select_nodes(\<acute>K) ;;
      \<acute>H :== CALL contract(\<acute>K, \<acute>H) ;;
      \<acute>R :== CALL is_K5(\<acute>H) ;;
      IF \<acute>R THEN RAISE \<acute>R :== True FI ;;
      \<acute>R :== CALL is_K33(\<acute>H)
    CATCH SKIP END
  "



end
