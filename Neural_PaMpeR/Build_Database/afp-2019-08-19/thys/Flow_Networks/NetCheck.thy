section \<open>Checking for Valid Network\<close>
theory NetCheck
imports 
  "Lib/Refine_Add_Fofu"
  Network
  Graph_Impl
  DFS_Framework.Reachable_Nodes
begin
text \<open>
  This theory contains code to read a network from an edge list, 
  and verify that the network is a valid input for the 
  Edmonds Karp Algorithm.
\<close>

(*<*)
  declare [[coercion_delete int]]
  declare [[coercion_delete "real::nat\<Rightarrow>real"]]
(*>*)

  subsection \<open>Graphs as Lists of Edges\<close>
  text \<open>Graphs can be represented as lists of edges, each edge being a triple of 
    start node, end node, and capacity. Capacities must be positive, and there
    must not be multiple edges with the same start and end node. \<close>

  type_synonym edge_list = "(node \<times> node \<times> capacity_impl) list"

  definition ln_invar :: "edge_list \<Rightarrow> bool" where 
    "ln_invar el \<equiv> 
      distinct (map (\<lambda>(u, v, _). (u,v)) el) 
    \<and> (\<forall>(u,v,c)\<in>set el. c>0) 
    "
  definition ln_\<alpha> :: "edge_list \<Rightarrow> capacity_impl graph" where 
    "ln_\<alpha> el \<equiv> \<lambda>(u,v). 
      if \<exists>c. (u, v, c) \<in> set el \<and> c \<noteq> 0 then 
        SOME c. (u, v, c) \<in> set el \<and> c \<noteq> 0
      else 0"

  definition "ln_rel \<equiv> br ln_\<alpha> ln_invar"
  
  lemma ln_equivalence: "(el, c') \<in> ln_rel \<longleftrightarrow> ln_invar el \<and> c' = ln_\<alpha> el"
    unfolding ln_rel_def br_def by auto 

  definition ln_N :: "(node\<times>node\<times>_) list \<Rightarrow> nat" 
    \<comment> \<open>Maximum node number plus one. I.e. the size of an array to be indexed by nodes.\<close>
    where "ln_N el \<equiv> Max ((fst`set el) \<union> ((fst o snd)`set el)) + 1"

  lemma ln_\<alpha>_imp_in_set: "\<lbrakk>ln_\<alpha> el (u,v)\<noteq>(0)\<rbrakk> \<Longrightarrow> (u,v,ln_\<alpha> el (u,v))\<in>set el"
    apply (auto simp: ln_\<alpha>_def split: if_split_asm)
    apply (metis (mono_tags, lifting) someI_ex)
    done

  lemma ln_N_correct: "Graph.V (ln_\<alpha> el) \<subseteq> {0..<ln_N el}"  
    apply (clarsimp simp: Graph.V_def Graph.E_def)
    apply (safe dest!: ln_\<alpha>_imp_in_set)
    apply (fastforce simp: ln_N_def less_Suc_eq_le intro: Max_ge)
    apply (force simp: ln_N_def less_Suc_eq_le intro: Max_ge)
    done

  subsection \<open>Pre-Networks\<close>  
  text \<open>This data structure is used to convert an edge-list to a network and 
    check validity. It maintains additional information, like a adjacency maps. \<close>

  record pre_network =
    pn_c :: "capacity_impl graph"
    pn_V :: "nat set"
    pn_succ :: "nat \<Rightarrow> nat list"
    pn_pred :: "nat \<Rightarrow> nat list"
    pn_adjmap :: "nat \<Rightarrow> nat list"
    pn_s_node :: bool
    pn_t_node :: bool

  fun read :: "edge_list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pre_network option" 
    \<comment> \<open>Read a pre-network from an edge list, and source/sink node numbers.\<close>
  where
    "read [] _ _ = Some \<lparr>
      pn_c = (\<lambda> _. 0), 
      pn_V = {}, 
      pn_succ = (\<lambda> _. []),
      pn_pred = (\<lambda> _. []),
      pn_adjmap = (\<lambda> _. []), 
      pn_s_node = False, 
      pn_t_node = False
    \<rparr>"
  | "read ((u, v, c) # es) s t = ((case (read es s t) of 
      Some x \<Rightarrow>
        (if (pn_c x) (u, v) = 0 \<and> (pn_c x) (v, u) = 0 \<and> c > 0 then
          (if u = v \<or> v = s \<or> u = t then
            None
          else
            Some (x\<lparr> 
              pn_c := (pn_c x) ((u, v) := c),
              pn_V := insert u (insert v (pn_V x)),
              pn_succ := (pn_succ x) (u := v # ((pn_succ x) u)),
              pn_pred := (pn_pred x) (v := u # ((pn_pred x) v)),
              pn_adjmap := (pn_adjmap x) (
                u := v # (pn_adjmap x) u, 
                v := u # (pn_adjmap x) v),
              pn_s_node := pn_s_node x \<or> u = s,
              pn_t_node := pn_t_node x \<or> v = t
            \<rparr>))
        else
          None)
    | None \<Rightarrow> None))"
      
  (* TODO: These proofs look overly verbose. *)  
  lemma read_correct1: "read es s t = Some \<lparr>pn_c = c, pn_V = V, pn_succ = succ, 
    pn_pred = pred , pn_adjmap = adjmap, pn_s_node = s_n, pn_t_node = t_n\<rparr> \<Longrightarrow> 
    (es, c) \<in> ln_rel \<and> Graph.V c = V \<and> finite V \<and> 
    (s_n \<longrightarrow> s \<in> V) \<and> (t_n \<longrightarrow> t \<in> V) \<and> (\<not>s_n \<longrightarrow> s \<notin> V) \<and> (\<not>t_n \<longrightarrow> t \<notin> V) \<and>
    (\<forall>u v. c (u,v) \<ge> 0) \<and>
    (\<forall>u. c(u, u) = 0) \<and> (\<forall>u. c (u, s) = 0) \<and> (\<forall>u. c (t, u) = 0) \<and>
    (\<forall>u v. c (u, v) \<noteq> 0 \<longrightarrow> c (v, u) = 0) \<and> 
    (\<forall>u. set (succ u) = Graph.E c``{u} \<and> distinct (succ u)) \<and> 
    (\<forall>u. set (pred u) = (Graph.E c)\<inverse>``{u} \<and> distinct (pred u)) \<and> 
    (\<forall>u. set (adjmap u) = Graph.E c``{u} \<union> (Graph.E c)\<inverse>``{u} 
      \<and> distinct (adjmap u))"
    proof (induction es arbitrary: c V succ pred adjmap s_n t_n)
      case Nil
        thus ?case 
          unfolding Graph.V_def Graph.E_def ln_rel_def br_def 
            ln_\<alpha>_def ln_invar_def 
          by auto
    next
      case (Cons e es)
        obtain u1 v1 c1 where obt1: "e = (u1, v1, c1)" by (meson prod_cases3)
        obtain x where obt2: "read es s t = Some x"
          using Cons.prems obt1 by (auto split: option.splits)
        have fct0: "(pn_c x) (u1, v1) = 0 \<and> (pn_c x) (v1, u1) = 0 \<and> c1 > 0"
          using Cons.prems obt1 obt2 by (auto split: option.splits if_splits)
        have fct1: "c1 > 0 \<and> u1 \<noteq> v1 \<and> v1 \<noteq> s \<and> u1 \<noteq> t"
          using Cons.prems obt1 obt2 by (auto split: option.splits if_splits)
        
        obtain c' V' sc' ps' pd' s_n' t_n' where obt3: 
          "x = \<lparr>pn_c = c', pn_V = V',
                pn_succ = sc', pn_pred = pd',  pn_adjmap = ps', 
                pn_s_node = s_n', pn_t_node = t_n'\<rparr>" 
          apply (cases x) by auto
        then have "read es s t = Some \<lparr>pn_c = c', pn_V = V', 
          pn_succ = sc', pn_pred = pd',
          pn_adjmap = ps', pn_s_node = s_n', pn_t_node = t_n'\<rparr>" 
          using obt2 by blast
        note fct = Cons.IH[OF this]
        have fct2: "s_n = (s_n' \<or> u1 = s)" 
          using fct0 fct1 Cons.prems obt1 obt2 obt3 by simp
        have fct3: "t_n = (t_n' \<or> v1 = t)"
          using fct0 fct1 Cons.prems obt1 obt2 obt3 by simp
        have fct4: "c = c' ((u1, v1) := c1)"
          using fct0 fct1 Cons.prems obt1 obt2 obt3 by simp
        have fct5: "V = V' \<union> {u1, v1}" 
          using fct0 fct1 Cons.prems obt1 obt2 obt3 by simp
        have fct6: "succ = sc' (u1 := v1 # sc' u1)" 
          using fct0 fct1 Cons.prems obt1 obt2 obt3 by simp
        have fct7: "pred = pd' (v1 := u1 # pd' v1)"
          using fct0 fct1 Cons.prems obt1 obt2 obt3 by simp
        have fct8: "adjmap = (ps' (u1 := v1 # ps' u1)) (v1 := u1 # ps' v1)"
          using fct0 fct1 Cons.prems obt1 obt2 obt3 by simp
        
          
        {
          have "(es, c') \<in> ln_rel" using fct by blast
          then have "ln_invar es" and "c' = ln_\<alpha> es" 
            unfolding ln_rel_def br_def by auto
          
          have "ln_invar (e # es)"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              have f1: "\<forall>(u, v, c) \<in> set (e # es). c>0" 
                using \<open>ln_invar es\<close> fct0 obt1
                unfolding ln_invar_def by auto
              have f2: "distinct (map (\<lambda>(u, v, _). (u,v)) es)" 
                using \<open>ln_invar es\<close>
                unfolding ln_invar_def by auto
              
              have "\<exists>c1'. (u1, v1, c1') \<in> (set es) \<and> c1' \<noteq> 0"
                proof (rule ccontr)
                  assume "\<not> ?thesis"
                  then have "\<forall>c1'. (u1, v1, c1') \<notin> (set es) \<or> c1' = 0" by blast
                  then have "distinct (map (\<lambda>(u, v, _). (u,v)) (e # es))" 
                    using obt1 f2 f1 by auto
                  then have "ln_invar (e # es)" 
                    unfolding ln_invar_def using f1 by simp
                  thus "False" using \<open>\<not> ln_invar (e # es)\<close> by blast
                qed
              then obtain c1' where "(u1, v1, c1') \<in> (set es) \<and> c1' \<noteq> 0" 
                by blast
              then have "c' (u1, v1) = (SOME c. (u1, v1, c) \<in> set es \<and> c \<noteq> 0)"
                using \<open>c' = ln_\<alpha> es\<close> unfolding ln_\<alpha>_def by auto
              then have "c' (u1, v1) \<noteq> 0" 
                using \<open>(u1, v1, c1') \<in> (set es) \<and> c1' \<noteq> 0\<close> f1
                by (metis (mono_tags, lifting) tfl_some)
              thus "False" using fct0 obt3 by simp
            qed
          moreover {
            {
              fix a
              have f1: "distinct (map (\<lambda>(u, v, _). (u,v)) (e # es))"
                and f2: "\<forall>u v. (u, v, 0) \<notin> set (e # es)"
                using \<open>ln_invar (e # es)\<close> unfolding ln_invar_def by auto
              have "c a = ln_\<alpha> (e # es) a"
                proof (cases "a = (u1, v1)")
                  case True
                    have "c a = c1" using fct4 True by simp
                    moreover {
                      have "(ln_\<alpha> (e # es)) a 
                        = (SOME c. (u1, v1, c) \<in> set (e # es) \<and> c \<noteq> 0)"
                        (is "?L = ?R") 
                        unfolding ln_\<alpha>_def using obt1 fct0 True by auto
                      moreover have "?R = c1"
                        proof (rule ccontr)
                          assume "\<not> ?thesis"
                          then obtain c1' where 
                            "(u1, v1, c1') \<in> set (e # es) \<and> c1' \<noteq> 0 \<and> c1' \<noteq> c1" 
                            using fct0 obt1 by auto
                          then have 
                            "\<not>distinct (map (\<lambda>(u, v, _). (u,v)) (e # es))" 
                            using obt1 
                            by (metis (mono_tags, lifting) Pair_inject 
                              distinct_map_eq list.set_intros(1) split_conv) 
                          thus "False" using f1 by blast
                        qed
                      ultimately have "?L = c1" by blast
                    }
                    ultimately show ?thesis by simp
                next
                  case False
                    have f1: 
                      "\<forall>u1' v1' c1'. u1' \<noteq> u1 \<or> v1' \<noteq> v1 
                      \<longrightarrow> ((u1', v1', c1') \<in> set (e # es)
                            \<longleftrightarrow> (u1', v1', c1') \<in> set es)" 
                      using obt1 by auto
                    obtain u1' v1' where "a = (u1', v1')" by (cases a)
                    {
                      have "(ln_\<alpha> (e # es)) (u1', v1') = (ln_\<alpha> es) (u1', v1')"
                        proof (cases 
                            "\<exists> c1'. (u1', v1', c1') \<in> set (e # es) \<and> c1' \<noteq> 0")
                          case True
                            thus ?thesis unfolding ln_\<alpha>_def 
                              using f1 False True \<open>a = (u1', v1')\<close> by auto
                        next
                          case False
                            thus ?thesis unfolding ln_\<alpha>_def by auto
                        qed
                      then have "(ln_\<alpha> (e # es)) a = (ln_\<alpha> es) a" 
                        using \<open>a = (u1', v1')\<close> by simp
                    }
                    moreover have "c a = c' a" using False fct4 by simp
                    moreover have "c' a = ln_\<alpha> es a" using \<open>c' = ln_\<alpha> es\<close> 
                      by simp
                    ultimately show ?thesis by simp
                qed
            }
            then have "c = ln_\<alpha> (e # es)" by auto
          }
          ultimately have "(e # es, c) \<in> ln_rel" unfolding ln_rel_def br_def 
            by simp
        }
        moreover {
          have "Graph.V c = Graph.V c' \<union> {u1, v1}" 
            unfolding Graph.V_def Graph.E_def using fct0 fct4 by auto
          moreover have "Graph.V c' = V'" using fct by blast
          ultimately have "Graph.V c = V" using fct5 by auto
        }
        moreover {
          have "finite V'" using fct by blast
          then have "finite V" using fct5 by auto
        }
        moreover {
          assume "s_n"
          then have "s_n' \<or> u1 = s" using fct2 by blast
          then have "s \<in> V"
            proof
              assume "s_n'"
                thus ?thesis using fct fct5 by auto
            next
              assume "u1 = s"
                thus ?thesis using fct5 by simp
            qed
        }
        moreover {
          assume "t_n"
          then have "t_n' \<or> v1 = t" using fct3 by blast
          then have "t \<in> V"
            proof
              assume "t_n'"
                thus ?thesis using fct fct5 by auto
            next
              assume "v1 = t"
                thus ?thesis using fct5 by simp
            qed
        }
        moreover {
          assume "\<not>s_n"
          then have "\<not>s_n' \<and> u1 \<noteq> s" using fct2 by blast
          then have "s \<notin> V" using fct fct5 fct1  by auto
        }
        moreover {
          assume "\<not>t_n"
          then have "\<not>t_n' \<and> v1 \<noteq> t" using fct3 by blast
          then have "t \<notin> V" using fct fct5 fct1  by auto
        }
        moreover have "\<forall>u v. (c (u, v) \<ge> 0)" using fct fct4 fct1 fct0 by auto
        moreover have "\<forall>u. c (u, u) = 0" using fct fct4 fct1 fct0 by auto
        moreover have "\<forall>u. c (u, s) = 0" using fct fct4 fct1 fct0 by auto
        moreover have "\<forall>u. c (t, u) = 0" using fct fct4 fct1 fct0 by auto
        moreover {
          fix a b
          assume "c (a, b) \<noteq> 0"
          then have "a \<noteq> b" using \<open>\<forall>u. c (u, u) = 0\<close> by auto
          have "c (b, a) = 0"
            proof (cases "(a, b) = (u1, v1)")
              case True
                then have "c (b, a) = c' (v1, u1)" using fct4 \<open>a \<noteq> b\<close> by auto 
                moreover have "c' (v1, u1) = 0" using fct0 obt3 by auto
                ultimately show ?thesis by simp
            next
              case False
                thus ?thesis
                  proof (cases "(b, a) = (u1, v1)")
                    case True
                      then have "c (a, b) = c' (v1, u1)" using fct4 \<open>a \<noteq> b\<close> 
                        by auto
                      moreover have "c' (v1, u1) = 0" using fct0 obt3 by auto
                      ultimately show ?thesis using \<open>c (a, b) \<noteq> 0\<close> by simp
                  next
                    case False
                      then have "c (b, a) = c' (b, a)" using fct4 by auto
                      moreover have "c (a, b) = c' (a, b)" 
                        using False \<open>(a, b) \<noteq> (u1, v1)\<close> fct4 by auto
                      ultimately show ?thesis using fct \<open>c (a, b) \<noteq> 0\<close> by auto 
                  qed
            qed
        } note n_fct = this
        moreover {
          {
            fix a
            assume "a \<noteq> u1"
            then have "succ a = sc' a" using fct6 by simp
            moreover have "set (sc' a) = Graph.E c' `` {a} \<and> distinct (sc' a)"
              using fct by blast
            ultimately have "set (succ a) = Graph.E c``{a} \<and> distinct (succ a)"
              unfolding Graph.E_def using fct4 \<open>a \<noteq> u1\<close> by auto 
          }
          moreover {
            fix a
            assume "a = u1"
            have "set (succ a) = Graph.E c``{a} \<and> distinct (succ a)"
              proof (cases "c' (u1, v1) = 0")
                case True
                  have fct: "set (sc' a) = Graph.E c' `` {a} \<and> distinct (sc' a)"
                    using fct by blast
                  
                  have "succ a = v1 # sc' a" using \<open>a = u1\<close> fct6 True by simp
                  moreover have "Graph.E c = Graph.E c' \<union> {(u1, v1)}" 
                    unfolding Graph.E_def using fct4 fct0 by auto
                  moreover have "v1 \<notin> set (sc' a)"
                    proof (rule ccontr)
                      assume "\<not> ?thesis"
                      then have "c' (a, v1) \<noteq> 0" 
                        using fct unfolding Graph.E_def by auto
                      thus "False" using True \<open>a = u1\<close> by simp
                    qed
                  ultimately show ?thesis using \<open>a = u1\<close> fct by auto
              next
                case False
                  thus ?thesis using fct0 obt3 by auto
              qed
        }
        ultimately have 
          "\<forall>u. set (succ u) = Graph.E c `` {u} \<and> distinct (succ u)" 
          by metis
      }
        moreover {
          {
            fix a
            assume "a \<noteq> v1"
            then have "pred a = pd' a" using fct7 by simp
            moreover have 
              "set (pd' a) = (Graph.E c')\<inverse> `` {a} \<and> distinct (pd' a)"
              using fct by blast
            ultimately have 
              "set (pred a) = (Graph.E c)\<inverse>``{a} \<and> distinct (pred a)"
              unfolding Graph.E_def using fct4 \<open>a \<noteq> v1\<close> by auto 
          }
          moreover {
            fix a
            assume "a = v1"
            have "set (pred a) = (Graph.E c)\<inverse>``{a} \<and> distinct (pred a)"
              proof (cases "c' (u1, v1) = 0")
                case True
                  have fct: 
                    "set (pd' a) = (Graph.E c')\<inverse> `` {a} \<and> distinct (pd' a)"
                    using fct by blast
                  
                  have "pred a = u1 # pd' a" using \<open>a = v1\<close> fct7 True by simp
                  moreover have "Graph.E c = Graph.E c' \<union> {(u1, v1)}" 
                    unfolding Graph.E_def using fct4 fct0 by auto
                  moreover have "u1 \<notin> set (pd' a)"
                    proof (rule ccontr)
                      assume "\<not> ?thesis"
                      then have "c' (u1, a) \<noteq> 0" 
                        using fct unfolding Graph.E_def by auto
                      thus "False" using True \<open>a = v1\<close> by simp
                    qed
                  ultimately show ?thesis using \<open>a = v1\<close> fct by auto
              next
                case False
                  thus ?thesis using fct0 obt3 by auto
              qed
        }
        ultimately have 
          "\<forall>u. set (pred u) = (Graph.E c)\<inverse>`` {u} \<and> distinct (pred u)" 
          by metis
      }
      moreover {
        {
          fix a
          assume "a \<noteq> u1 \<and> a \<noteq> v1"
          then have "adjmap a = ps' a" using fct8 by simp
            moreover have "set (ps' a) = 
              Graph.E c'``{a} \<union> (Graph.E c')\<inverse>``{a} \<and> distinct (ps' a)" 
              using fct by blast
            ultimately have 
              "set (adjmap a) = Graph.E c``{a} \<union> (Graph.E c)\<inverse>``{a} 
                \<and> distinct (adjmap a)" 
              unfolding Graph.E_def using fct4 \<open>a \<noteq> u1 \<and> a \<noteq> v1\<close> by auto
        }
        moreover {
          fix a
          assume "a = u1 \<or> a = v1"
          then have 
            "set (adjmap a) = Graph.E c``{a} \<union> (Graph.E c)\<inverse>``{a} 
              \<and> distinct (adjmap a)"
            proof
              assume "a = u1"
              show ?thesis
                proof (cases "c' (u1, v1) = 0 \<and> c' (v1, u1) = 0")
                  case True
                    have fct: 
                      "set (ps' a) = Graph.E c' `` {a} \<union> (Graph.E c')\<inverse> `` {a} 
                      \<and> distinct (ps' a)" 
                      using fct by blast
                    
                    have "adjmap a = v1 # ps' a" 
                      using \<open>a = u1\<close> fct8 True by simp
                    moreover have "Graph.E c = Graph.E c' \<union> {(u1, v1)}" 
                      unfolding Graph.E_def using fct4 fct0 by auto
                    moreover have "v1 \<notin> set (ps' a)"
                      proof (rule ccontr)
                        assume "\<not> ?thesis"
                        then have "c' (a, v1) \<noteq> 0 \<or> c' (v1, a) \<noteq> 0"
                          using fct unfolding Graph.E_def by auto
                        thus "False" using True \<open>a = u1\<close> by simp
                      qed
                    ultimately show ?thesis using \<open>a = u1\<close> fct by auto
                next
                  case False
                    thus ?thesis using fct0 obt3 by auto 
                qed
            next
              assume "a = v1"
              show ?thesis
                proof (cases "c' (u1, v1) = 0 \<and> c' (v1, u1) = 0")
                  case True
                    have fct: 
                      "set (ps' a) = Graph.E c' `` {a} \<union> (Graph.E c')\<inverse> `` {a} 
                      \<and> distinct (ps' a)" 
                      using fct by blast
                    
                    have "adjmap a = u1 # ps' a" 
                      using \<open>a = v1\<close> fct8 True by simp
                    moreover have "Graph.E c = Graph.E c' \<union> {(u1, v1)}" 
                      unfolding Graph.E_def using fct4 fct0 by auto
                    moreover have "u1 \<notin> set (ps' a)"
                      proof (rule ccontr)
                        assume "\<not> ?thesis"
                        then have "c' (u1, a) \<noteq> 0 \<or> c' (a, u1) \<noteq> 0"
                          using fct unfolding Graph.E_def by auto
                        thus "False" using True \<open>a = v1\<close> by simp
                      qed
                    ultimately show ?thesis using \<open>a = v1\<close> fct by auto
                next
                  case False
                    thus ?thesis using fct0 obt3 by auto
                qed
            qed
        }
        ultimately have 
          "\<forall>u. set (adjmap u) = Graph.E c``{u} \<union> (Graph.E c)\<inverse>``{u} 
          \<and> distinct (adjmap u)" 
          by metis
      }
      ultimately show ?case by simp  
    qed
    
  lemma read_correct2: "read el s t = None \<Longrightarrow> \<not>ln_invar el 
    \<or> (\<exists>u v c. (u,v,c) \<in> set el \<and> \<not>(c > 0))
    \<or> (\<exists>u c. (u, u, c) \<in> set el \<and> c \<noteq> 0) \<or> 
    (\<exists>u c. (u, s, c) \<in> set el \<and> c \<noteq> 0) \<or> (\<exists>u c. (t, u, c) \<in> set el \<and> c \<noteq> 0) \<or>
    (\<exists>u v c1 c2. (u, v, c1) \<in> set el \<and> (v, u, c2) \<in> set el \<and> c1 \<noteq> 0 \<and> c2 \<noteq> 0)"
    proof (induction el)
      case Nil
        thus ?case by auto
    next
      case (Cons e el)
        thus ?case
          proof (cases "read el s t = None")
            case True
              note Cons.IH[OF this]
              thus ?thesis
                proof
                  assume "\<not>ln_invar el"
                  then have "\<not>distinct (map (\<lambda>(u, v, _). (u,v)) (e # el)) \<or> 
                    (\<exists>(u, v, c) \<in> set (e # el). \<not>(c>0))" 
                    unfolding ln_invar_def by fastforce
                  thus ?thesis unfolding ln_invar_def by fastforce
                next
                  assume "
                    (\<exists>u v c. (u, v, c) \<in> set (el) \<and> \<not>(c > 0)) 
                  \<or> (\<exists>u c. (u, u, c) \<in> set el \<and> c \<noteq> 0) 
                  \<or> (\<exists>u c. (u, s, c) \<in> set el \<and> c \<noteq> 0) 
                  \<or> (\<exists>u c. (t, u, c) \<in> set el \<and> c \<noteq> 0) 
                  \<or> (\<exists>u v c1 c2. (u, v, c1) \<in> set el \<and> (v, u, c2) \<in> set el 
                      \<and> c1 \<noteq> 0 \<and> c2 \<noteq> 0)" 
                  
                  moreover {
                    assume "(\<exists>u v c. (u, v, c) \<in> set el \<and> \<not>(c > 0))"
                    then have "(\<exists>u v c. (u, v, c) \<in> set (e # el) \<and> \<not>(c > 0))" 
                      by auto
                  }
                  moreover {
                    assume "(\<exists>u c. (u, u, c) \<in> set el \<and> c \<noteq> 0)"
                    then have "(\<exists>u c. (u, u, c) \<in> set (e # el) \<and> c \<noteq> 0)" 
                      by auto
                  }
                  moreover {
                    assume "(\<exists>u c. (u, s, c) \<in> set el \<and> c \<noteq> 0)"
                    then have "(\<exists>u c. (u, s, c) \<in> set (e # el) \<and> c \<noteq> 0)" 
                      by auto
                  }
                  moreover {
                    assume "(\<exists>u c. (t, u, c) \<in> set el \<and> c \<noteq> 0)"
                    then have "(\<exists>u c. (t, u, c) \<in> set (e # el) \<and> c \<noteq> 0)" 
                      by auto
                  }
                  moreover {
                    assume "(\<exists>u v c1 c2. 
                      (u, v, c1) \<in> set el \<and> (v, u, c2) \<in> set el 
                        \<and> c1 \<noteq> 0 \<and> c2 \<noteq> 0)"
                    then have "(\<exists>u v c1 c2. (u, v, c1) \<in> set (e # el) \<and>
                      (v, u, c2) \<in> set (e # el) \<and> c1 \<noteq> 0 \<and> c2 \<noteq> 0)" 
                      by auto
                  }
                  ultimately show ?thesis by blast
                qed
          next
            case False
            then obtain x where obt1: "read el s t = Some x" by auto
            obtain u1 v1 c1 where obt2: "e = (u1, v1, c1)" 
              apply (cases e) by auto
            obtain c' V' sc' pd' ps' s_n' t_n' where obt3: "x = 
              \<lparr>
                pn_c = c', pn_V = V', pn_succ = sc',
                pn_pred = pd', pn_adjmap = ps',
                pn_s_node = s_n', pn_t_node = t_n'
              \<rparr>" 
              apply (cases x) by auto 
            then have "(el, c') \<in> ln_rel" using obt1 read_correct1[of el s t] 
              by simp
            then have "c' = ln_\<alpha> el" unfolding ln_rel_def br_def by simp
            

            have "(c' (u1, v1) \<noteq> 0 \<or> c' (v1, u1) \<noteq> 0 \<or> c1 \<le> 0) \<or> 
              (c1 > 0 \<and> (u1 = v1 \<or> v1 = s \<or> u1 = t))"
              using obt1 obt2 obt3 False Cons.prems 
                by (auto split:option.splits if_splits)
            moreover {
              assume "c1 \<le> 0"
              then have "\<not> ln_invar (e # el)" 
                unfolding ln_invar_def using obt2 by auto
            }
            moreover {
              assume "c1 > 0 \<and> u1 = v1"
              then have "(\<exists>u c. (u, u, c) \<in> set (e # el) \<and> c > 0)" 
                using obt2 by auto
            }
            moreover {
              assume "c1 > 0 \<and> v1 = s"
              then have "(\<exists>u c. (u, s, c) \<in> set (e # el) \<and> c > 0)" 
                using obt2 by auto
            }
            moreover {
              assume "c1 > 0 \<and> u1 = t"
              then have "(\<exists>u c. (t, u, c) \<in> set (e # el) \<and> c > 0)" 
                using obt2 by auto
            }
            moreover {
              assume "c' (u1, v1) \<noteq> 0"
              then have "\<exists>c1'. (u1, v1, c1') \<in> set el" 
                using \<open>c' = ln_\<alpha> el\<close> unfolding ln_\<alpha>_def 
                by (auto split:if_splits)
              then have "\<not> distinct (map (\<lambda>(u, v, _). (u, v)) (e # el))" 
                using obt2 by force
              then have "\<not>ln_invar (e # el)" unfolding ln_invar_def by auto
            }
            moreover {
              assume "c' (v1, u1) \<noteq> 0"
              then have "\<exists>c1'. (v1, u1, c1') \<in> set el \<and> c1' \<noteq> 0" 
                using \<open>c' = ln_\<alpha> el\<close> unfolding ln_\<alpha>_def 
                by (auto split:if_splits)
              then have "\<not>ln_invar (e # el) \<or> (
                \<exists>u v c1 c2.
                  (u, v, c1) \<in> set (e # el) \<and> (v, u, c2) \<in> set (e # el) 
                  \<and> c1 \<noteq> 0 \<and> c2 \<noteq> 0)"
                proof (cases "c1 \<noteq> 0")
                  case True
                    thus ?thesis 
                      using \<open>\<exists>c1'. (v1, u1, c1') \<in> set el  \<and> c1' \<noteq> 0\<close> obt2 
                      by auto
                next
                  case False
                    then have "\<not>ln_invar (e # el)" 
                      unfolding ln_invar_def using obt2 by auto
                    thus ?thesis by blast
                qed
            }
            ultimately show ?thesis by blast
          qed
    qed
    
  subsection \<open>Implementation of Pre-Networks\<close>  

  record 'capacity::linordered_idom pre_network' =
    pn_c' :: "(nat*nat,'capacity) ArrayHashMap.ahm"
    pn_V' :: "nat ahs"
    pn_succ' :: "(nat,nat list) ArrayHashMap.ahm"
    pn_pred' :: "(nat,nat list) ArrayHashMap.ahm"
    pn_adjmap' :: "(nat,nat list) ArrayHashMap.ahm"
    pn_s_node' :: bool
    pn_t_node' :: bool


  definition "pnet_\<alpha> pn' \<equiv> \<lparr>
      pn_c = the_default 0 o (ahm.\<alpha> (pn_c' pn')), 
      pn_V = ahs_\<alpha> (pn_V' pn'), 
      pn_succ = the_default [] o (ahm.\<alpha> (pn_succ' pn')),
      pn_pred = the_default [] o (ahm.\<alpha> (pn_pred' pn')),
      pn_adjmap = the_default [] o (ahm.\<alpha> (pn_adjmap' pn')), 
      pn_s_node = pn_s_node' pn', 
      pn_t_node = pn_t_node' pn'
  \<rparr>"  

  definition "pnet_rel \<equiv> br pnet_\<alpha> (\<lambda>_. True)"
  
  definition "ahm_ld a ahm k \<equiv> the_default a (ahm.lookup k ahm)"
  abbreviation "cap_lookup \<equiv> ahm_ld 0"
  abbreviation "succ_lookup \<equiv> ahm_ld []"


  fun read' :: "(nat \<times> nat \<times> 'capacity::linordered_idom) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    'capacity pre_network' option" where
    "read' [] _ _ = Some \<lparr>
      pn_c' = ahm.empty (), 
      pn_V' = ahs.empty (), 
      pn_succ' = ahm.empty (),
      pn_pred' = ahm.empty (),
      pn_adjmap' = ahm.empty (), 
      pn_s_node' = False, 
      pn_t_node' = False
    \<rparr>"
  | "read' ((u, v, c) # es) s t = ((case (read' es s t) of 
      Some x \<Rightarrow>
        (if 
          cap_lookup (pn_c' x) (u, v) = 0 
          \<and> cap_lookup (pn_c' x) (v, u) = 0 \<and> c > 0 
         then
          (if u = v \<or> v = s \<or> u = t then
            None
          else
            Some (x\<lparr> 
              pn_c' := ahm.update (u, v) c (pn_c' x),
              pn_V' := ahs.ins u (ahs.ins v (pn_V' x)),
              pn_succ' := 
                ahm.update u (v # (succ_lookup (pn_succ' x) u)) (pn_succ' x),
              pn_pred' := 
                ahm.update v (u # (succ_lookup (pn_pred' x) v)) (pn_pred' x),
              pn_adjmap' := ahm.update 
                u (v # (succ_lookup (pn_adjmap' x) u)) (ahm.update 
                v (u # (succ_lookup (pn_adjmap' x) v)) 
                (pn_adjmap' x)),
              pn_s_node' := pn_s_node' x \<or> u = s,
              pn_t_node' := pn_t_node' x \<or> v = t
            \<rparr>))
        else
          None)
    | None \<Rightarrow> None))"

  lemma read'_correct: "read el s t = map_option pnet_\<alpha> (read' el s t)"
    apply (induction el s t rule: read.induct)
    by (auto 
      simp: pnet_\<alpha>_def o_def ahm.correct ahs.correct ahm_ld_def 
      split: option.splits) (* Takes long *)
    
  lemma read'_correct_alt: "(read' el s t, read el s t) \<in> \<langle>pnet_rel\<rangle>option_rel"
    unfolding pnet_rel_def br_def
    apply (simp add: option_rel_def read'_correct)
    using domIff by force

  export_code read checking SML     
  
  subsection \<open>Usefulness Check\<close>
  text \<open>
    We have to check that every node in the network is useful,
    i.e., lays on a path from source to sink.
    \<close>

  definition "reachable_spec c s \<equiv> RETURN (((Graph.E c)\<^sup>*)``{s}) "
  definition "reaching_spec c t \<equiv> RETURN ((((Graph.E c)\<inverse>)\<^sup>*)``{t})"

  definition "checkNet cc s t \<equiv> do {
    if s = t then
      RETURN None
    else do {
      let rd = read cc s t;
      case rd of 
        None \<Rightarrow> RETURN None
      | Some x \<Rightarrow> do {                
          if pn_s_node x \<and> pn_t_node x then
            do {
              ASSERT(finite ((Graph.E (pn_c x))\<^sup>* `` {s}));
              ASSERT(finite (((Graph.E (pn_c x))\<inverse>)\<^sup>* `` {t}));
              ASSERT(\<forall>u. set ((pn_succ x) u) = Graph.E (pn_c x) `` {u} 
                \<and> distinct ((pn_succ x) u));
              ASSERT(\<forall>u. set ((pn_pred x) u) = (Graph.E (pn_c x))\<inverse> `` {u}   
                \<and> distinct ((pn_pred x) u));
              
              succ_s \<leftarrow> reachable_spec (pn_c x) s;
              pred_t \<leftarrow> reaching_spec (pn_c x) t;
              if (pn_V x) = succ_s \<and> (pn_V x) = pred_t then
                RETURN (Some (pn_c x, pn_adjmap x))
              else
                RETURN None
            }
          else
            RETURN None
        }
      }
    }"

  lemma checkNet_pre_correct1 : "checkNet el s t \<le> 
    SPEC (\<lambda> r. r = Some (c, adjmap) \<longrightarrow> (el, c) \<in> ln_rel \<and> Network c s t \<and> 
    (\<forall>u. set (adjmap u) = Graph.E c``{u} \<union> (Graph.E c)\<inverse>``{u} 
      \<and> distinct (adjmap u)))"
    unfolding checkNet_def reachable_spec_def reaching_spec_def
    apply (refine_vcg)
    apply clarsimp_all
      proof -
        {
          fix x
          assume asm1: "s \<noteq> t"
          assume asm2: "read el s t = Some x"
          assume asm3: "pn_s_node x"
          assume asm4: "pn_t_node x"
          obtain c V sc pd adjmap  where obt: "x = 
            \<lparr>
              pn_c = c, pn_V = V,
              pn_succ = sc, pn_pred = pd,  pn_adjmap = adjmap, 
              pn_s_node = True, pn_t_node = True
            \<rparr>"
            apply (cases x) using asm3 asm4 by auto
          then have "read el s t = Some \<lparr>
            pn_c = c, pn_V = V, pn_succ = sc, pn_pred = pd, 
            pn_adjmap = adjmap, pn_s_node = True, pn_t_node = True\<rparr>" 
            using asm2 by simp
          note fct = read_correct1[OF this]
          
          then have [simp, intro!]: "finite (Graph.V c)" by blast
          have "Graph.E c \<subseteq> (Graph.V c) \<times> (Graph.V c)" 
            unfolding Graph.V_def by auto
          from finite_subset[OF this] have "finite (Graph.E (pn_c x))" 
            by (simp add: obt)
          then show "finite ((Graph.E (pn_c x))\<^sup>* `` {s})" 
            and "finite (((Graph.E (pn_c x))\<inverse>)\<^sup>* `` {t})"  
            by (auto simp add: finite_rtrancl_Image)
        }
        {
          fix x
          assume asm1: "s \<noteq> t"
          assume asm2: "read el s t = Some x"
          assume asm3: "finite ((Graph.E (pn_c x))\<^sup>* `` {s})"
          assume asm4: "finite (((Graph.E (pn_c x))\<inverse>)\<^sup>* `` {t})"
          assume asm5: "pn_s_node x"
          assume asm6: "pn_t_node x" 
          obtain c V sc pd adjmap  where obt: "x = \<lparr>pn_c = c, pn_V = V,
            pn_succ = sc, pn_pred = pd,  pn_adjmap = adjmap, 
            pn_s_node = True, pn_t_node = True\<rparr>"
            apply (cases x) using asm5 asm6 by auto
          then have "read el s t = Some \<lparr>pn_c = c, pn_V = V, 
            pn_succ = sc, pn_pred = pd, pn_adjmap = adjmap, 
            pn_s_node = True, pn_t_node = True\<rparr>" 
            using asm2 by simp
          note fct = read_correct1[OF this]
          
          have "\<And>u. set ((pn_succ x) u) 
            = Graph.E (pn_c x) `` {u} \<and> distinct ((pn_succ x) u)"
            using fct obt by simp
          moreover have "\<And>u. set ((pn_pred x) u) = (Graph.E (pn_c x))\<inverse> `` {u} \<and> 
            distinct ((pn_pred x) u)" using fct obt by simp
          ultimately show "\<And>u. set ((pn_succ x) u) = Graph.E (pn_c x) `` {u}" 
            and "\<And>u. distinct ((pn_succ x) u)" 
            and "\<And>u. set ((pn_pred x) u) = (Graph.E (pn_c x))\<inverse> `` {u}"
            and "\<And>u.  distinct ((pn_pred x) u)" 
            by auto 
        }
        {
          fix x
          assume asm1: "s \<noteq> t"
          assume asm2: "read el s t = Some x"
          assume asm3: "pn_s_node x"
          assume asm4: "pn_t_node x"
          assume asm5: 
            "((Graph.E (pn_c x))\<inverse>)\<^sup>* `` {t} = (Graph.E (pn_c x))\<^sup>* `` {s}"
          assume asm6: "pn_V x = (Graph.E (pn_c x))\<^sup>* `` {s}" 
          assume asm7: "c = pn_c x"
          assume asm8: "adjmap = pn_adjmap x"
          obtain V sc pd  where obt: "x = \<lparr>pn_c = c, pn_V = V,
            pn_succ = sc, pn_pred = pd,  pn_adjmap = adjmap, 
            pn_s_node = True, pn_t_node = True\<rparr>"
            apply (cases x) using asm3 asm4 asm7 asm8 by auto
          then have "read el s t = Some \<lparr>pn_c = c, pn_V = V, 
            pn_succ = sc, pn_pred = pd, pn_adjmap = adjmap, 
            pn_s_node = True, pn_t_node = True\<rparr>" 
            using asm2 by simp
          note fct = read_correct1[OF this]
          
          have "\<And>u. set ((pn_succ x) u) = Graph.E (pn_c x) `` {u} 
            \<and> distinct ((pn_succ x) u)"
            using fct obt by simp
          moreover have "\<And>u. set ((pn_pred x) u) = (Graph.E (pn_c x))\<inverse> `` {u} \<and> 
            distinct ((pn_pred x) u)" using fct obt by simp
          moreover have "(el, pn_c x) \<in> ln_rel" using fct asm7 by simp
          moreover {
            {
              {
                have "Graph.V c \<subseteq> ((Graph.E c))\<^sup>* `` {s}" 
                  using asm6 obt fct by simp
                then have "\<forall>v\<in>(Graph.V c). Graph.isReachable c s v" 
                  unfolding Graph.connected_def using Graph.rtc_isPath[of s _ c] 
                  by auto
              }
              moreover {
                have "Graph.V c \<subseteq> ((Graph.E c)\<inverse>)\<^sup>* `` {t}" 
                  using asm5 asm6 obt fct by simp
                then have "\<forall>v\<in>(Graph.V c). Graph.isReachable c v t"
                  unfolding Graph.connected_def using Graph.rtci_isPath 
                  by fastforce
              }
              ultimately have 
                "\<forall>v\<in>(Graph.V c). Graph.isReachable c s v 
                \<and> Graph.isReachable c v t" 
                by simp
            }
            moreover {
              have "finite (Graph.V c)" and "s \<in> (Graph.V c)" 
                using fct obt by auto
              note Graph.reachable_ss_V[OF \<open>s \<in> (Graph.V c)\<close>]
              note finite_subset[OF this \<open>finite (Graph.V c)\<close>]
            }
            ultimately have "Network (pn_c x) s t" 
              unfolding Network_def using asm1 fct asm7 
              by (simp add: Graph.E_def)
          }
          moreover have "\<forall>u.(set (pn_adjmap x u) =
            Graph.E (pn_c x) `` {u} \<union> (Graph.E (pn_c x))\<inverse> `` {u})" 
            using fct obt by simp
          moreover have "\<forall>u. distinct (pn_adjmap x u)" using fct obt by simp
          ultimately show "(el, pn_c x) \<in> ln_rel" and "Network (pn_c x) s t" and
            "\<And>u. set (pn_adjmap x u) 
              = Graph.E (pn_c x) `` {u} \<union> (Graph.E (pn_c x))\<inverse> `` {u}" 
            and "\<And>u. distinct (pn_adjmap x u)" by auto
        }
      qed
  
  lemma checkNet_pre_correct2_aux: 
    assumes asm1: "s \<noteq> t"
    assumes asm2: "read el s t = Some x" 
    assumes asm3: 
      "\<forall>u. set (pn_succ x u) = Graph.E (pn_c x) `` {u} \<and> distinct (pn_succ x u)"
    assumes asm4: "\<forall>u. set (pn_pred x u) = (Graph.E (pn_c x))\<inverse> `` {u} 
      \<and> distinct (pn_pred x u)"
    assumes asm5: "pn_V x = (Graph.E (pn_c x))\<^sup>* `` {s} 
      \<longrightarrow> (Graph.E (pn_c x))\<^sup>* `` {s} \<noteq> ((Graph.E (pn_c x))\<inverse>)\<^sup>* `` {t}"
    assumes asm6: "pn_s_node x"
    assumes asm7: "pn_t_node x"
    assumes asm8: "ln_invar el"
    assumes asm9: "Network (ln_\<alpha> el) s t"
    shows "False"
    proof -          
      obtain c V sc pd ps  where obt: "x = \<lparr>pn_c = c, pn_V = V, 
        pn_succ = sc, pn_pred = pd, pn_adjmap = ps, 
        pn_s_node = True, pn_t_node = True\<rparr>"
        apply (cases x) using asm3 asm4 asm6 asm7 by auto
      then have "read el s t = Some \<lparr>pn_c = c, pn_V = V, 
        pn_succ = sc, pn_pred = pd, pn_adjmap = ps, 
        pn_s_node = True, pn_t_node = True\<rparr>" 
        using asm2 by simp
      note fct = read_correct1[OF this]
      
      have "pn_V x \<noteq> (Graph.E (pn_c x))\<^sup>* `` {s} 
        \<or> (pn_V x = (Graph.E (pn_c x))\<^sup>* `` {s} 
            \<and> ((Graph.E (pn_c x))\<inverse>)\<^sup>* `` {t} \<noteq> (Graph.E (pn_c x))\<^sup>* `` {s})" 
        using asm5 by blast
      thus "False"
        proof
          assume "pn_V x = (Graph.E (pn_c x))\<^sup>* `` {s} \<and> 
            ((Graph.E (pn_c x))\<inverse>)\<^sup>* `` {t} \<noteq> (Graph.E (pn_c x))\<^sup>* `` {s}"
          then have "\<not>(Graph.V c \<subseteq> ((Graph.E c)\<inverse>)\<^sup>* `` {t}) 
            \<or> \<not>(((Graph.E c)\<inverse>)\<^sup>* `` {t} \<subseteq> Graph.V c)"
            using asm5  obt fct by simp
          then have "\<exists>v\<in>(Graph.V c). \<not>Graph.isReachable c v t"
            proof
              assume "\<not>(((Graph.E c)\<inverse>)\<^sup>* `` {t} \<subseteq> Graph.V c)"
              then obtain x where 
                o1: "x \<in> ((Graph.E c)\<inverse>)\<^sup>* `` {t} \<and> x \<notin> Graph.V c" 
                by blast
              then have "\<exists>p. Graph.isPath c x p t" 
                using Graph.rtci_isPath by auto
              then obtain p where "Graph.isPath c x p t" by blast
              then have "x \<in> Graph.V c"
                proof (cases "p = []")
                  case True
                    then have "x = t" 
                      using \<open>Graph.isPath c x p t\<close> Graph.isPath.simps(1) 
                      by auto
                    thus ?thesis using fct by auto
                next
                  case False
                    then obtain p1 ps where "p = p1 # ps" 
                      by (meson neq_Nil_conv)
                    then have "Graph.isPath c x (p1 # ps) t" 
                      using \<open>Graph.isPath c x p t\<close> by auto
                    then have "fst p1 = x \<and> c p1 \<noteq> 0" 
                      using Graph.isPath_head[of c x p1 ps t] 
                      by (auto simp: Graph.E_def)
                    then have "\<exists>v. c (x, v) \<noteq> 0" by (metis prod.collapse)
                    then have "x \<in> Graph.V c" 
                      unfolding Graph.V_def Graph.E_def by auto
                    thus ?thesis by simp
                qed
              thus ?thesis using o1 by auto
            next
              assume "\<not>(Graph.V c \<subseteq> ((Graph.E c)\<inverse>)\<^sup>* `` {t})"
              then obtain x where 
                o1: "x \<notin> ((Graph.E c)\<inverse>)\<^sup>* `` {t} \<and> x \<in> Graph.V c" 
                by blast
              then have "(x , t) \<notin> (Graph.E c)\<^sup>*" 
                by (meson Image_singleton_iff rtrancl_converseI)
              have "\<forall>p. \<not>Graph.isPath c x p t"
                proof (rule ccontr)
                  assume "\<not>?thesis"
                  then obtain p where "Graph.isPath c x p t" by blast
                  thus "False" using Graph.isPath_rtc \<open>(x , t) \<notin> (Graph.E c)\<^sup>*\<close> 
                  by auto
                qed
              then have "\<not>Graph.isReachable c x t" 
                unfolding Graph.connected_def by auto
              thus ?thesis using o1 by auto
            qed
          moreover {
            have "(el, c) \<in> ln_rel" using fct obt by simp
            then have "c = ln_\<alpha> el" unfolding ln_rel_def br_def by auto
          }
          ultimately have "\<not>Network (ln_\<alpha> el) s t" 
            unfolding Network_def by auto
          thus ?thesis using asm9 by blast
        next
          assume "pn_V x \<noteq> (Graph.E (pn_c x))\<^sup>* `` {s}"
          
          then have "\<not>(Graph.V c \<subseteq> (Graph.E c)\<^sup>* `` {s}) 
            \<or> \<not>((Graph.E c)\<^sup>* `` {s} \<subseteq> Graph.V c)"
            using asm5  obt fct by simp
          then have "\<exists>v\<in>(Graph.V c). \<not>Graph.isReachable c s v"
            proof
              assume "\<not>((Graph.E c)\<^sup>* `` {s} \<subseteq> Graph.V c)"
              then obtain x where o1:"x \<in> (Graph.E c)\<^sup>* `` {s} \<and> x \<notin> Graph.V c" 
                by blast
              then have "\<exists>p. Graph.isPath c s p x" 
                using Graph.rtc_isPath by auto
              then obtain p where "Graph.isPath c s p x" by blast
              then have "x \<in> Graph.V c"
                proof (cases "p = []")
                  case True
                    then have "x = s" 
                      using \<open>Graph.isPath c s p x\<close> 
                      by (auto simp: Graph.isPath.simps(1))
                    thus ?thesis using fct by auto
                next
                  case False
                    then obtain p1 ps where "p = ps @ [p1]" 
                      by (metis append_butlast_last_id)
                    then have "Graph.isPath c s (ps @ [p1]) x"
                      using \<open>Graph.isPath c s p x\<close> by auto
                    then have "snd p1 = x \<and> c p1 \<noteq> 0"
                      using Graph.isPath_tail[of c s ps p1 x] 
                      by (auto simp: Graph.E_def)
                    then have "\<exists>v. c (v, x) \<noteq> 0" by (metis prod.collapse)
                    then have "x \<in> Graph.V c" 
                      unfolding Graph.V_def Graph.E_def by auto
                    thus ?thesis by simp
                qed
              thus ?thesis using o1 by auto
            next
              assume "\<not>(Graph.V c \<subseteq> (Graph.E c)\<^sup>* `` {s})"
              then obtain x where o1: "x \<notin> (Graph.E c)\<^sup>* `` {s} \<and> x \<in> Graph.V c" 
                by blast
              then have "(s , x) \<notin> (Graph.E c)\<^sup>*" 
                by (meson Image_singleton_iff rtrancl_converseI)
              have "\<forall>p. \<not>Graph.isPath c s p x"
                proof (rule ccontr)
                  assume "\<not>?thesis"
                  then obtain p where "Graph.isPath c s p x" by blast
                  thus "False" using Graph.isPath_rtc \<open>(s, x) \<notin> (Graph.E c)\<^sup>*\<close> 
                    by auto
                qed
              then have "\<not>Graph.isReachable c s x" 
                unfolding Graph.connected_def by auto
              thus ?thesis using o1 by auto
            qed
          moreover {
            have "(el, c) \<in> ln_rel" using fct obt by simp
            then have "c = ln_\<alpha> el" unfolding ln_rel_def br_def by auto
          }
          ultimately have "\<not>Network (ln_\<alpha> el) s t" 
            unfolding Network_def by auto
          thus ?thesis using asm9 by blast
        qed
    qed

  lemma checkNet_pre_correct2:
    "checkNet el s t 
    \<le> SPEC (\<lambda>r. r = None \<longrightarrow> \<not>ln_invar el \<or> \<not>Network (ln_\<alpha> el) s t)"
    unfolding checkNet_def reachable_spec_def reaching_spec_def
    apply (refine_vcg)
    apply (clarsimp_all) 
    proof -
      {
        assume "s = t" and "ln_invar el" and "Network (ln_\<alpha> el) t t"
        thus "False" using Network_def by auto
      }
      next {
        assume "s \<noteq> t" and "read el s t = None" and "ln_invar el" 
          and "Network (ln_\<alpha> el) s t"
        note read_correct2[OF \<open>read el s t = None\<close>]
        thus "False"
          proof
            assume "\<not>ln_invar el"
            thus ?thesis using \<open>ln_invar el\<close> by blast
          next
            assume asm: "
              (\<exists>u v c. (u, v, c) \<in> set el \<and> \<not>(c > 0)) 
            \<or> (\<exists>u c. (u, u, c) \<in> set el \<and> c\<noteq>0) 
            \<or> (\<exists>u c. (u, s, c) \<in> set el \<and> c\<noteq>0) 
            \<or> (\<exists>u c. (t, u, c) \<in> set el \<and> c\<noteq>0) 
            \<or> (\<exists>u v c1 c2. (u, v, c1) \<in> set el 
                \<and> (v, u, c2) \<in> set el \<and> c1\<noteq>0 \<and> c2\<noteq>0)"
            
            moreover {
              assume A: "(\<exists>u v c. (u, v, c) \<in> set el \<and> \<not>(c>0))"
              then have "\<not>ln_invar el" 
                using not_less by (fastforce simp: ln_invar_def)
              with \<open>ln_invar el\<close> have False by simp
            }
            moreover {
              assume "(\<exists>u c. (u, u, c) \<in> set el \<and> c\<noteq>0)"
              then have "\<exists> u. ln_\<alpha> el (u, u) \<noteq> 0" 
                unfolding ln_\<alpha>_def apply (auto split:if_splits)
                by (metis (mono_tags, lifting) tfl_some)
              then have "False" 
                using \<open>Network (ln_\<alpha> el) s t\<close> 
                unfolding Network_def by (auto simp: Graph.E_def)
            }
            moreover {
              assume "(\<exists>u c. (u, s, c) \<in> set el \<and> c\<noteq>0)"
              then have "\<exists> u. ln_\<alpha> el (u, s) \<noteq> 0" 
                unfolding ln_\<alpha>_def 
                by (clarsimp) (metis (mono_tags, lifting) tfl_some)
              then have "False" 
                using \<open>Network (ln_\<alpha> el) s t\<close> unfolding Network_def 
                by (auto simp: Graph.E_def)
            }
            moreover {
              assume "(\<exists>u c. (t, u, c) \<in> set el \<and> c\<noteq>0)"
              then have "\<exists> u. ln_\<alpha> el (t, u) \<noteq> 0" 
              unfolding ln_\<alpha>_def 
                by (clarsimp) (metis (mono_tags, lifting) tfl_some)
              then have "False" 
                using \<open>Network (ln_\<alpha> el) s t\<close> unfolding Network_def 
                by (auto simp: Graph.E_def)
            }
            moreover {
              assume "(\<exists>u v c1 c2. 
                (u, v, c1) \<in> set el \<and> (v, u, c2) \<in> set el \<and> c1\<noteq>0 \<and> c2\<noteq>0)"
              then obtain u v c1 c2 where 
                o1: "(u, v, c1) \<in> set el \<and> (v, u, c2) \<in> set el 
                    \<and> c1\<noteq>0 \<and> c2\<noteq>0" 
                by blast
              then have "ln_\<alpha> el (u, v) \<noteq> 0" unfolding ln_\<alpha>_def
                by (clarsimp) (metis (mono_tags, lifting) tfl_some)
              moreover have "ln_\<alpha> el (v, u) \<noteq> 0" unfolding ln_\<alpha>_def using o1 
                by (clarsimp) (metis (mono_tags, lifting) tfl_some)
              ultimately have 
                "\<not> (\<forall>u v. (ln_\<alpha> el) (u, v) \<noteq> 0 \<longrightarrow> (ln_\<alpha> el) (v, u) = 0)" 
                by auto
              then have "False" 
                using \<open>Network (ln_\<alpha> el) s t\<close> unfolding Network_def 
                by (auto simp: Graph.E_def)
            }
            ultimately show ?thesis by force
          qed
      }
      next {
        fix x
        assume asm1: "s \<noteq> t"
        assume asm2: "read el s t = Some x"
        assume asm3: "pn_s_node x"
        assume asm4: "pn_t_node x"
        obtain c V sc pd adjmap  where obt: "x = \<lparr>pn_c = c, pn_V = V,
          pn_succ = sc, pn_pred = pd,  pn_adjmap = adjmap, 
          pn_s_node = True, pn_t_node = True\<rparr>"
          apply (cases x) using asm3 asm4 by auto
        then have "read el s t = Some \<lparr>pn_c = c, pn_V = V, 
          pn_succ = sc, pn_pred = pd, pn_adjmap = adjmap, 
          pn_s_node = True, pn_t_node = True\<rparr>" 
          using asm2 by simp
        note fct = read_correct1[OF this]
        
        then have [simp]: "finite (Graph.V c)" by blast
        have "Graph.E c \<subseteq> (Graph.V c) \<times> (Graph.V c)" 
          unfolding Graph.V_def by auto
        from finite_subset[OF this] have "finite (Graph.E (pn_c x))" 
          by (auto simp: obt)
        then show  "finite ((Graph.E (pn_c x))\<^sup>* `` {s})" 
          and "finite (((Graph.E (pn_c x))\<inverse>)\<^sup>* `` {t})"  
          by (auto simp add: finite_rtrancl_Image)
      }
      {
        fix x
        assume asm1: "s \<noteq> t"
        assume asm2: "read el s t = Some x"
        assume asm3: "finite ((Graph.E (pn_c x))\<^sup>* `` {s})"
        assume asm4: "finite (((Graph.E (pn_c x))\<inverse>)\<^sup>* `` {t})"
        assume asm5: "pn_s_node x"
        assume asm6: "pn_t_node x" 
        obtain c V sc pd adjmap  where obt: "x = \<lparr>pn_c = c, pn_V = V,
          pn_succ = sc, pn_pred = pd, pn_adjmap = adjmap, 
          pn_s_node = True, pn_t_node = True\<rparr>"
          apply (cases x) using asm5 asm6 by auto
        then have "read el s t = Some \<lparr>pn_c = c, pn_V = V, pn_succ = sc, 
          pn_pred = pd, pn_adjmap = adjmap, pn_s_node = True, pn_t_node = True\<rparr>" 
          using asm2 by simp
        note fct = read_correct1[OF this]
        
        have "\<And>u. set ((pn_succ x) u) = Graph.E (pn_c x) `` {u} 
          \<and> distinct ((pn_succ x) u)"
          using fct obt by simp
        moreover have "\<And>u. set ((pn_pred x) u) = (Graph.E (pn_c x))\<inverse> `` {u} \<and> 
          distinct ((pn_pred x) u)" 
          using fct obt by simp
        ultimately show  "\<And>u. set ((pn_succ x) u) = Graph.E (pn_c x) `` {u}" 
          and "\<And>u. distinct ((pn_succ x) u)" 
          and "\<And>u. set ((pn_pred x) u) = (Graph.E (pn_c x))\<inverse> `` {u}"
          and "\<And>u.  distinct ((pn_pred x) u)" 
          by auto 
      }
      next {
        fix x
        assume asm1: "s \<noteq> t"
        assume asm2: "read el s t = Some x"
        assume asm3: "pn_s_node x \<longrightarrow> \<not>pn_t_node x"
        assume asm4: "ln_invar el"
        assume asm5: "Network (ln_\<alpha> el) s t"
        obtain c V sc pd ps s_node t_node where 
          obt: "x = \<lparr>pn_c = c, pn_V = V, pn_succ = sc, pn_pred = pd, 
          pn_adjmap = ps, pn_s_node = s_node, pn_t_node = t_node\<rparr>" 
          by (cases x) 
        then have "read el s t = Some \<lparr>pn_c = c, pn_V = V, pn_succ = sc, 
          pn_pred = pd, pn_adjmap = ps, pn_s_node = s_node, pn_t_node = t_node\<rparr>" 
          using asm2 by simp
        note fct = read_correct1[OF this]
        
        have "(el, c) \<in> ln_rel" using fct obt by simp
        then have "c = ln_\<alpha> el" unfolding ln_rel_def br_def by auto
        
        have "\<not>pn_s_node x \<or> \<not>pn_t_node x" using asm3 by auto 
        then show "False"
          proof
            assume "\<not>pn_s_node x"
            then have "\<not>s_node" using obt fct by auto
            then have "s \<notin> Graph.V c" using fct by auto
            thus ?thesis using \<open>c = ln_\<alpha> el\<close> asm5 Network_def by auto
          next
            assume "\<not>pn_t_node x"
            then have "\<not>t_node" using obt fct by auto
            then have "t \<notin> Graph.V c" using fct by auto
            thus ?thesis using \<open>c = ln_\<alpha> el\<close> asm5 Network_def by auto
          qed
      }
    qed (blast dest: checkNet_pre_correct2_aux)  

  lemma checkNet_correct' : "checkNet el s t \<le> SPEC (\<lambda> r. case r of 
      Some (c, adjmap) \<Rightarrow>
        (el, c) \<in> ln_rel \<and> Network c s t 
        \<and> (\<forall>u. set (adjmap u) = Graph.E c``{u} \<union> (Graph.E c)\<inverse>``{u} 
           \<and> distinct (adjmap u))
    | None \<Rightarrow> \<not>ln_invar el \<or> \<not>Network (ln_\<alpha> el) s t)"
    using checkNet_pre_correct1[of el s t] checkNet_pre_correct2[of el s t]
    by (auto split: option.splits simp: pw_le_iff refine_pw_simps)

  lemma checkNet_correct : "checkNet el s t \<le> SPEC (\<lambda>r. case r of 
      Some (c, adjmap) \<Rightarrow> (el, c) \<in> ln_rel \<and> Network c s t 
        \<and> Graph.is_adj_map c adjmap
    | None \<Rightarrow> \<not>ln_invar el \<or> \<not>Network (ln_\<alpha> el) s t)"
    using checkNet_pre_correct1[of el s t] checkNet_pre_correct2[of el s t]
    by (auto 
        split: option.splits 
        simp: Graph.is_adj_map_def pw_le_iff refine_pw_simps)

  subsection \<open>Implementation of Usefulness Check\<close>  
  text \<open>We use the DFS framework to implement the usefulness check.
    We have to convert between our graph representation and the CAVA automata 
    library's graph representation used by the DFS framework.
    \<close>

  definition "graph_of pn s \<equiv> \<lparr>
    g_V = UNIV,
    g_E = Graph.E (pn_c pn),
    g_V0 = {s}
  \<rparr>"

  definition "rev_graph_of pn s \<equiv> \<lparr>
    g_V = UNIV,
    g_E = (Graph.E (pn_c pn))\<inverse>,
    g_V0 = {s}
  \<rparr>"

  
  definition "checkNet2 cc s t \<equiv> do {
    if s = t then
      RETURN None
    else do {
      let rd = read cc s t;
      case rd of 
        None \<Rightarrow> RETURN None
      | Some x \<Rightarrow> do {                
          if pn_s_node x \<and> pn_t_node x then
            do {
              ASSERT(finite ((Graph.E (pn_c x))\<^sup>* `` {s}));
              ASSERT(finite (((Graph.E (pn_c x))\<inverse>)\<^sup>* `` {t}));
              ASSERT(\<forall>u. set ((pn_succ x) u) = Graph.E (pn_c x) `` {u} 
                \<and> distinct ((pn_succ x) u));
              ASSERT(\<forall>u. set ((pn_pred x) u) = (Graph.E (pn_c x))\<inverse> `` {u} 
                \<and> distinct ((pn_pred x) u));
              
              let succ_s = (op_reachable (graph_of x s));
              let pred_t = (op_reachable (rev_graph_of x t));
              if (pn_V x) = succ_s \<and> (pn_V x) = pred_t then
                RETURN (Some (pn_c x, pn_adjmap x))
              else
                RETURN None
            }
          else
            RETURN None
        }
      }
    }"
    
  lemma checkNet2_correct: "checkNet2 c s t \<le> checkNet c s t"
    apply (rule refine_IdD)
    unfolding checkNet_def checkNet2_def graph_of_def rev_graph_of_def 
      reachable_spec_def reaching_spec_def
    apply (refine_rcg)
    apply refine_dref_type
    apply auto
    done
    
  definition "graph_of_impl pn' s \<equiv> \<lparr>
    gi_V = \<lambda>_. True,
    gi_E = succ_lookup (pn_succ' pn'),
    gi_V0 = [s]
  \<rparr>"

  definition "rev_graph_of_impl pn' t \<equiv> \<lparr>
    gi_V = \<lambda>_. True,
    gi_E = succ_lookup (pn_pred' pn'),
    gi_V0 = [t]
  \<rparr>"
    
  definition "well_formed_pn x \<equiv> 
    (\<forall>u. set ((pn_succ x) u) = Graph.E (pn_c x) `` {u} 
      \<and> distinct ((pn_succ x) u))"
  
  definition "rev_well_formed_pn x \<equiv> 
    (\<forall>u. set ((pn_pred x) u) = (Graph.E (pn_c x))\<inverse> `` {u} 
      \<and> distinct ((pn_pred x) u))"
    
  lemma id_slg_rel_alt_a: "\<langle>Id\<rangle>slg_rel 
    = { (s,E). \<forall>u. distinct (s u) \<and> set (s u) = E``{u} }"
    by (auto simp add: slg_rel_def br_def list_set_rel_def dest: fun_relD)  
    
  lemma graph_of_impl_correct: "well_formed_pn pn \<Longrightarrow> (pn', pn) \<in> pnet_rel \<Longrightarrow>
    (graph_of_impl pn' s, graph_of pn s) \<in> \<langle>unit_rel,Id\<rangle>g_impl_rel_ext"
    unfolding pnet_rel_def graph_of_impl_def graph_of_def
      g_impl_rel_ext_def gen_g_impl_rel_ext_def
    apply (auto simp: fun_set_rel_def br_def list_set_rel_def 
        id_slg_rel_alt_a ahm_ld_def)
    apply (auto simp: well_formed_pn_def Graph.E_def 
        pnet_\<alpha>_def o_def ahm_correct)
    done
    
  lemma rev_graph_of_impl_correct:"\<lbrakk>rev_well_formed_pn pn; (pn',pn)\<in>pnet_rel\<rbrakk> 
    \<Longrightarrow> 
    (rev_graph_of_impl pn' s, rev_graph_of pn s) \<in> \<langle>unit_rel,Id\<rangle>g_impl_rel_ext"
    unfolding pnet_rel_def rev_graph_of_impl_def rev_graph_of_def
      g_impl_rel_ext_def gen_g_impl_rel_ext_def
    apply (auto simp: fun_set_rel_def br_def list_set_rel_def 
        id_slg_rel_alt_a ahm_ld_def)
    apply (auto simp: rev_well_formed_pn_def Graph.E_def pnet_\<alpha>_def 
        o_def ahm_correct)
    done   
  
  schematic_goal reachable_impl:
    assumes [simp]: "finite ((g_E G)\<^sup>* `` g_V0 G)" "graph G"
    assumes [autoref_rules]: "(Gi,G)\<in>\<langle>unit_rel,nat_rel\<rangle>g_impl_rel_ext"
    shows "RETURN (?c::?'c) \<le> \<Down>?R (RETURN (op_reachable G))"  
    by autoref_monadic
  concrete_definition reachable_impl uses reachable_impl
  thm reachable_impl.refine

  context begin
    interpretation autoref_syn .

    schematic_goal sets_eq_impl:
      fixes a b :: "nat set"
      assumes [autoref_rules]: "(ai,a) \<in> \<langle>nat_rel\<rangle>ahs.rel"
      assumes [autoref_rules]: "(bi,b) \<in> \<langle>nat_rel\<rangle>dflt_ahs_rel"
      shows "(?c, (a ::: \<langle>nat_rel\<rangle>ahs.rel) = (b ::: \<langle>nat_rel\<rangle>dflt_ahs_rel )) 
        \<in> bool_rel"
      apply (autoref)
      done
    concrete_definition sets_eq_impl uses sets_eq_impl  

  end
  
  definition "net_\<alpha> \<equiv> (\<lambda>(ci, adjmapi) . 
    ((the_default 0 o (ahm.\<alpha> ci)), (the_default [] o (ahm.\<alpha> adjmapi))))"

  lemma [code]: "net_\<alpha> (ci, adjmapi) = (
    cap_lookup ci, succ_lookup adjmapi
    )"
    unfolding net_\<alpha>_def 
    by (auto split: option.splits simp: ahm.correct ahm_ld_def)

  definition "checkNet3 cc s t \<equiv> do {
    if s = t then
      RETURN None
    else do {
      let rd = read' cc s t;
      case rd of 
        None \<Rightarrow> RETURN None
      | Some x \<Rightarrow> do {                
          if pn_s_node' x \<and> pn_t_node' x then
            do {
              ASSERT(finite ((Graph.E (pn_c (pnet_\<alpha> x)))\<^sup>* `` {s}));
              ASSERT(finite (((Graph.E (pn_c (pnet_\<alpha> x)))\<inverse>)\<^sup>* `` {t}));
              ASSERT(\<forall>u. set ((pn_succ (pnet_\<alpha> x)) u) =
                Graph.E (pn_c (pnet_\<alpha> x)) `` {u} 
                \<and> distinct ((pn_succ (pnet_\<alpha> x)) u));
              ASSERT(\<forall>u. set ((pn_pred (pnet_\<alpha> x)) u) = 
                (Graph.E (pn_c (pnet_\<alpha> x)))\<inverse> `` {u} 
                \<and> distinct ((pn_pred (pnet_\<alpha> x)) u));
            
              let succ_s = (reachable_impl (graph_of_impl x s));
              let pred_t = (reachable_impl (rev_graph_of_impl x t));
              if (sets_eq_impl (pn_V' x) succ_s) 
                \<and> (sets_eq_impl (pn_V' x) pred_t) 
              then
                RETURN (Some (net_\<alpha> (pn_c' x, pn_adjmap' x)))
              else
                RETURN None
            }
          else
            RETURN None
        }
      }
    }"     
  
  lemma aux1: "(x', x) \<in> pnet_rel \<Longrightarrow> (pn_V' x', pn_V x) \<in> br ahs.\<alpha> ahs.invar"
    unfolding pnet_rel_def br_def pnet_\<alpha>_def by auto

  lemma [simp]: "graph (graph_of pn s)"
    apply unfold_locales
    unfolding graph_of_def
    by auto

  lemma [simp]: "graph (rev_graph_of pn s)"
    apply unfold_locales
    unfolding rev_graph_of_def
    by auto


  context begin
  private lemma sets_eq_impl_correct_aux1:
    assumes A: "(pn', pn) \<in> pnet_rel"  
    assumes WF: "well_formed_pn pn" 

    assumes F: "finite ((Graph.E (pn_c (pnet_\<alpha> pn')))\<^sup>* `` {s})"
    shows "sets_eq_impl (pn_V' pn') (reachable_impl (graph_of_impl pn' s))
      \<longleftrightarrow> pn_V pn = (g_E (graph_of pn s))\<^sup>* `` g_V0 (graph_of pn s)"
  proof -
    from A have S1i: "(pn_V' pn', pn_V pn) \<in> br ahs.\<alpha> ahs.invar"
      unfolding pnet_rel_def br_def pnet_\<alpha>_def by auto

    note GI = graph_of_impl_correct[OF WF A]
    have G: "graph (graph_of pn s)" by simp

    have F': "finite ((g_E (graph_of pn s))\<^sup>* `` g_V0 (graph_of pn s))"
      using F A by (simp add: graph_of_def pnet_\<alpha>_def pnet_rel_def br_def)

    note S2i = reachable_impl.refine[simplified, OF F' G GI]  

    from sets_eq_impl.refine[simplified, OF S1i S2i] show ?thesis .
  qed 

  private lemma sets_eq_impl_correct_aux2:
    assumes A: "(pn', pn) \<in> pnet_rel"  
    assumes WF: "rev_well_formed_pn pn" 

    assumes F: "finite (((Graph.E (pn_c (pnet_\<alpha> pn')))\<inverse>)\<^sup>* `` {s})"
    shows "sets_eq_impl (pn_V' pn') (reachable_impl (rev_graph_of_impl pn' s))
      \<longleftrightarrow> pn_V pn = (g_E (rev_graph_of pn s))\<^sup>* `` g_V0 (rev_graph_of pn s)"
  proof -
    from A have S1i: "(pn_V' pn', pn_V pn) \<in> br ahs.\<alpha> ahs.invar"
      unfolding pnet_rel_def br_def pnet_\<alpha>_def by auto

    note GI = rev_graph_of_impl_correct[OF WF A]
    have G: "graph (rev_graph_of pn s)" by simp

    have F': "finite ((g_E (rev_graph_of pn s))\<^sup>* `` g_V0 (rev_graph_of pn s))"
      using F A by (simp add: rev_graph_of_def pnet_\<alpha>_def pnet_rel_def br_def)

    note S2i = reachable_impl.refine[simplified, OF F' G GI]  

    from sets_eq_impl.refine[simplified, OF S1i S2i] show ?thesis .
  qed 



  lemma checkNet3_correct: "checkNet3 el s t \<le> checkNet2 el s t" 
    unfolding checkNet3_def checkNet2_def
    apply (rule refine_IdD)
    apply (refine_rcg)
    apply clarsimp_all
    apply (rule introR[where R="\<langle>pnet_rel\<rangle>option_rel"])
    apply (simp add: read'_correct_alt; fail)
    apply ((simp add: pnet_rel_def br_def pnet_\<alpha>_def)+) [7]
    apply (subst sets_eq_impl_correct_aux1; assumption?)
    apply (simp add: well_formed_pn_def)
    
    apply (subst sets_eq_impl_correct_aux2; assumption?)
    apply (simp add: rev_well_formed_pn_def)

    apply simp

    apply (simp add: net_\<alpha>_def o_def pnet_\<alpha>_def pnet_rel_def br_def)
    done

  end  


  schematic_goal checkNet4: "RETURN ?c \<le> checkNet3 el s t"
    unfolding checkNet3_def
    by (refine_transfer)
  concrete_definition checkNet4 for el s t uses checkNet4
    

  lemma checkNet4_correct: "case checkNet4 el s t of 
      Some (c, adjmap) \<Rightarrow> (el, c) \<in> ln_rel 
        \<and> Network c s t \<and> Graph.is_adj_map c adjmap
    | None \<Rightarrow> \<not>ln_invar el \<or> \<not>Network (ln_\<alpha> el) s t"
  proof -  
    note checkNet4.refine 
    also note checkNet3_correct 
    also note checkNet2_correct
    also note checkNet_correct
    finally show ?thesis by simp
  qed  

subsection \<open>Executable Network Checker\<close>

  definition prepareNet :: "edge_list \<Rightarrow> node \<Rightarrow> node 
    \<Rightarrow> (capacity_impl graph \<times> (node\<Rightarrow>node list) \<times> nat) option"
    \<comment> \<open>Read an edge list and a source/sink node, and return a network graph,
      an adjacency map, and the maximum node number plus one. 
      If the edge list or network is invalid, return \<open>NONE\<close>.\<close>
  where
    "prepareNet el s t \<equiv> do {
      (c,adjmap) \<leftarrow> checkNet4 el s t;
      let N = ln_N el;
      Some (c,adjmap,N)
    }"

  export_code prepareNet checking SML  

  theorem prepareNet_correct: "case (prepareNet el s t) of 
      Some (c, adjmap,N) \<Rightarrow> (el, c) \<in> ln_rel \<and> Network c s t 
        \<and> Graph.is_adj_map c adjmap \<and> Graph.V c \<subseteq> {0..<N}
    | None \<Rightarrow> \<not>ln_invar el \<or> \<not>Network (ln_\<alpha> el) s t"
    using checkNet4_correct[of el s t] ln_N_correct[of el]
    unfolding prepareNet_def
    by (auto split: Option.bind_split simp: ln_rel_def br_def)

end
