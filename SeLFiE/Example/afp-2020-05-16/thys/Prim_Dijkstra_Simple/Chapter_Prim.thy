chapter \<open>Prim's Minimum Spanning Tree Algorithm\<close>
text \<open>
  Prim's algorithm~\cite{Prim57} is a classical algorithm to find a minimum spanning 
  tree of an undirected graph. In this section we describe our formalization 
  of Prim's algorithm, roughly following the presentation of Cormen et al.~\cite{Cormen-Leiserson-Rivest}.
  
  Our approach features stepwise refinement. We start by a generic MST algorithm (Section~\ref{sec:generic_mst}) 
  that covers both Prim's and Kruskal's algorithms. It maintains a subgraph \<open>A\<close> of an MST.
  Initially, \<open>A\<close> contains no edges and only the root node. In each iteration, the algorithm adds a new edge to \<open>A\<close>,
  maintaining the property that \<open>A\<close> is a subgraph of an MST. 
  In a next refinement step, we only add edges that are adjacent to the current \<open>A\<close>, thus 
  maintaining the invariant that \<open>A\<close> is always a tree (Section~\ref{sec:prim_algo}). 
  Next, we show how to use a priority queue to efficiently determine a next edge to be 
  added (Section~\ref{sec:using_pq}), and implement 
  the necessary update of the priority queue using a foreach-loop (Section~\ref{sec:using_foreach}).
  Finally we parameterize our algorithm over ADTs for graphs, maps, and priority queues 
  (Section~\ref{sec:prim_data_structs}), instantiate these with actual data structures (Section~\ref{sec:prim_inst_ds}), and extract
  executable ML code (Section~\ref{sec:prim_exec}).
  
  The advantage of this stepwise refinement approach is that the proof obligations of 
  each step are mostly independent from the other steps. This modularization greatly helps
  to keep the proof manageable. Moreover, the steps also correspond to a natural split 
  of the ideas behind Prim's algorithm: The same structuring is also done in the presentation 
  of Cormen et al.~\cite{Cormen-Leiserson-Rivest}, though not as detailed as ours.
\<close>
(*<*)
theory Chapter_Prim
imports Main begin end
(*>*)
