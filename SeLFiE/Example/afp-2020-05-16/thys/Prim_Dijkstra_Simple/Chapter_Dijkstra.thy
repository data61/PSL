chapter \<open>Dijkstra's Shortest Path Algorithm\<close>
text \<open>\noindent
  Dijkstra's algorithm~\cite{Dijk59} is a classical algorithm to determine the shortest
  paths from a root node to all other nodes in a weighted directed graph. 
  Although it solves a different problem, and works on a different type of graphs, 
  its structure is very similar to Prim's algorithm. 
  In particular, like Prim's algorithm, it has a simple loop structure and can be efficiently 
  implemented by a priority queue. 
  
  Again, our formalization of Dijkstra's algorithm follows the presentation 
  of Cormen et al.~\cite{Cormen-Leiserson-Rivest}. However, for the sake of simplicity, 
  our algorithm does not compute actual shortest paths, but only their weights. 
\<close>
(*<*)
theory Chapter_Dijkstra
imports Main begin end
(*>*)
