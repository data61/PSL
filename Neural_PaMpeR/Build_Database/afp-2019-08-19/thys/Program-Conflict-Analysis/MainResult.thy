(*  Title:       Conflict analysis/Main Result
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)
section "Main Result"
theory MainResult
imports ConstraintSystems
begin
text_raw \<open>\label{thy:MainResult}\<close>

text \<open>At this point everything is available to prove the main result of this project: 
  {\em The constraint system @{term RUV_cs} precisely characterizes simultaneously reachable control nodes w.r.t. to our
  semantic reference point.}

  The ,,trusted base'' of this proof, that are all definitions a reader that trusts the Isabelle prover must additionally trust, is the following:
  \begin{itemize}
    \item The flowgraph and the assumptions made on it in the \<open>flowgraph\<close>- and \<open>eflowgraph\<close>-locales. Note that we show in Section~\ref{sec:Flowgraph:ex_flowgraph} 
      that there is at least one non-trivial model of \<open>eflowgraph\<close>.
    \item The reference point semantics (@{term refpoint}) and the transitive closure operator (@{term trcl}).
    \item The definition of @{term atUV}.
    \item All dependencies of the above definitions in the Isabelle standard libraries.
  \end{itemize}
\<close>
theorem (in eflowgraph) RUV_is_sim_reach: 
  "(\<exists>w c'. ({#[entry fg (main fg)]#},w,c')\<in>trcl (refpoint fg) \<and> atUV U V c') 
    \<longleftrightarrow> (\<exists>Ml Me. (entry fg (main fg),Ml,Me)\<in>RUV_cs fg U V)" 
\<comment> \<open>The proof uses the soundness and precision theorems wrt. to normalized paths (@{thm [source] flowgraph.RUV_sound}, @{thm [source] flowgraph.RUV_precise}) as well as the normalization result, 
  i.e. that every reachable configuration is also reachable using a normalized path (@{thm [source] eflowgraph.normalize}) and, vice versa, that every normalized path is also a usual path (@{thm [source] ntr_is_tr}). 
  Finally the conversion between our working semantics and the semantic reference point is exploited (@{thm [source] flowgraph.refpoint_eq}).\<close>
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain w c' where C: "({#[entry fg (main fg)]#}, w, c') \<in> trcl (tr fg)" "atUV U V c'" by (auto simp add: refpoint_eq)
  from normalize[OF C(1), of "main fg", simplified] obtain ww where "({#[entry fg (main fg)]#}, ww, c') \<in> trcl (ntr fg)" by blast
  from ntrs.gtr2gtrp[where c="{#}", simplified, OF this] obtain s' ce' wwl where 1: "c'=add_mset s' ce'" "ww = map le_rem_s wwl" "(([entry fg (main fg)], {#}), wwl, s', ce') \<in> trcl (ntrp fg)" by blast
  with C(2) have 2: "atUV U V ({#s'#}+ce')" by auto
  from RUV_sound[OF 1(3) 2] show ?rhs by blast
next
  assume ?rhs
  then obtain Ml Me where C: "(entry fg (main fg), Ml, Me) \<in> RUV_cs fg U V" by blast
  from RUV_precise[OF C] obtain wwl s' c' where P: "(([entry fg (main fg)], {#}), wwl, s', c') \<in> trcl (ntrp fg)" "atUV U V ({#s'#} + c')" by blast
  from gtrp2gtr[OF P(1)] have "({# [entry fg (main fg)] #}, map le_rem_s wwl, {#s'#}+c') \<in> trcl (ntr fg)" by (auto)
  from ntr_is_tr[OF this] P(2) have "\<exists>w c'. ({#[entry fg (main fg)]#}, w, c') \<in> trcl (tr fg) \<and> atUV U V c'" by blast
  thus ?lhs by (simp add: refpoint_eq)
qed


end
