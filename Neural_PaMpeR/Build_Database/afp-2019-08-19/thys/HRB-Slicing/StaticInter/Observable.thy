section \<open>Observable Sets of Nodes\<close>

theory Observable imports ReturnAndCallNodes begin

context CFG begin


subsection \<open>Intraprocedural observable sets\<close>

inductive_set obs_intra :: "'node \<Rightarrow> 'node set \<Rightarrow> 'node set" 
for n::"'node" and S::"'node set"
where obs_intra_elem:
  "\<lbrakk>n -as\<rightarrow>\<^sub>\<iota>* n'; \<forall>nx \<in> set(sourcenodes as). nx \<notin> S; n' \<in> S\<rbrakk> \<Longrightarrow> n' \<in> obs_intra n S"


lemma obs_intraE:
  assumes "n' \<in> obs_intra n S"
  obtains as where "n -as\<rightarrow>\<^sub>\<iota>* n'" and "\<forall>nx \<in> set(sourcenodes as). nx \<notin> S" and "n' \<in> S"
  using \<open>n' \<in> obs_intra n S\<close>
  by(fastforce elim:obs_intra.cases)


lemma n_in_obs_intra:
  assumes "valid_node n" and "n \<in> S" shows "obs_intra n S = {n}"
proof -
  from \<open>valid_node n\<close> have "n -[]\<rightarrow>* n" by(rule empty_path)
  hence "n -[]\<rightarrow>\<^sub>\<iota>* n" by(simp add:intra_path_def)
  with \<open>n \<in> S\<close> have "n \<in> obs_intra n S" 
    by(fastforce elim:obs_intra_elem simp:sourcenodes_def)
  { fix n' assume "n' \<in> obs_intra n S"
    have "n' = n"
    proof(rule ccontr)
      assume "n' \<noteq> n"
      from \<open>n' \<in> obs_intra n S\<close> obtain as where "n -as\<rightarrow>\<^sub>\<iota>* n'"
        and "\<forall>nx \<in> set(sourcenodes as). nx \<notin> S"
        and "n' \<in> S" by(fastforce elim:obs_intra.cases)
      from \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> have "n -as\<rightarrow>* n'" by(simp add:intra_path_def)
      from this \<open>\<forall>nx \<in> set(sourcenodes as). nx \<notin> S\<close> \<open>n' \<noteq> n\<close> \<open>n \<in> S\<close>
      show False
      proof(induct rule:path.induct)
        case (Cons_path n'' as n' a n)
        from \<open>\<forall>nx\<in>set (sourcenodes (a#as)). nx \<notin> S\<close> \<open>sourcenode a = n\<close>
        have "n \<notin> S" by(simp add:sourcenodes_def)
        with \<open>n \<in> S\<close> show False by simp
      qed simp
    qed }
  with \<open>n \<in> obs_intra n S\<close> show ?thesis by fastforce
qed


lemma in_obs_intra_valid:
  assumes "n' \<in> obs_intra n S" shows "valid_node n" and "valid_node n'"
  using \<open>n' \<in> obs_intra n S\<close>
  by(auto elim!:obs_intraE intro:path_valid_node simp:intra_path_def)


lemma edge_obs_intra_subset:
  assumes "valid_edge a" and "intra_kind (kind a)" and "sourcenode a \<notin> S"
  shows "obs_intra (targetnode a) S \<subseteq> obs_intra (sourcenode a) S"
proof
  fix n assume "n \<in> obs_intra (targetnode a) S"
  then obtain as where "targetnode a -as\<rightarrow>\<^sub>\<iota>* n" 
    and all:"\<forall>nx \<in> set(sourcenodes as). nx \<notin> S" and "n \<in> S" by(erule obs_intraE)
  from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close> \<open>targetnode a -as\<rightarrow>\<^sub>\<iota>* n\<close>
  have "sourcenode a -[a]@as\<rightarrow>\<^sub>\<iota>* n" by(fastforce intro:Cons_path simp:intra_path_def)
  moreover
  from all \<open>sourcenode a \<notin> S\<close> have "\<forall>nx \<in> set(sourcenodes (a#as)). nx \<notin> S"
    by(simp add:sourcenodes_def)
  ultimately show "n \<in> obs_intra (sourcenode a) S" using \<open>n \<in> S\<close>
    by(fastforce intro:obs_intra_elem)
qed


lemma path_obs_intra_subset:
  assumes "n -as\<rightarrow>\<^sub>\<iota>* n'" and "\<forall>n' \<in> set(sourcenodes as). n' \<notin> S"
  shows "obs_intra n' S \<subseteq> obs_intra n S"
proof -
  from \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> have "n -as\<rightarrow>* n'" and "\<forall>a \<in> set as. intra_kind (kind a)"
    by(simp_all add:intra_path_def)
  from this \<open>\<forall>n' \<in> set(sourcenodes as). n' \<notin> S\<close> show ?thesis
  proof(induct rule:path.induct)
    case (Cons_path n'' as n' a n)
    note IH = \<open>\<lbrakk>\<forall>a\<in>set as. intra_kind (kind a); \<forall>n'\<in>set (sourcenodes as). n' \<notin> S\<rbrakk>
      \<Longrightarrow> obs_intra n' S \<subseteq> obs_intra n'' S\<close>
    from \<open>\<forall>n'\<in>set (sourcenodes (a#as)). n' \<notin> S\<close> 
    have all:"\<forall>n'\<in>set (sourcenodes as). n' \<notin> S" and "sourcenode a \<notin> S"
      by(simp_all add:sourcenodes_def)
    from \<open>\<forall>a \<in> set (a#as). intra_kind (kind a)\<close>
    have "intra_kind (kind a)" and "\<forall>a \<in> set as. intra_kind (kind a)"
      by(simp_all add:intra_path_def)
    from IH[OF \<open>\<forall>a \<in> set as. intra_kind (kind a)\<close> all]
    have "obs_intra n' S \<subseteq> obs_intra n'' S" .
    from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close> \<open>targetnode a = n''\<close>
      \<open>sourcenode a = n\<close> \<open>sourcenode a \<notin> S\<close>
    have "obs_intra n'' S \<subseteq> obs_intra n S" by(fastforce dest:edge_obs_intra_subset)
    with \<open>obs_intra n' S \<subseteq> obs_intra n'' S\<close> show ?case by fastforce
  qed simp
qed


lemma path_ex_obs_intra:
  assumes "n -as\<rightarrow>\<^sub>\<iota>* n'" and "n' \<in> S"
  obtains m where "m \<in> obs_intra n S"
proof(atomize_elim)
  show "\<exists>m. m \<in> obs_intra n S"
  proof(cases "\<forall>nx \<in> set(sourcenodes as). nx \<notin> S")
    case True
    with \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>n' \<in> S\<close> have "n' \<in> obs_intra n S" by -(rule obs_intra_elem)
    thus ?thesis by fastforce
  next
    case False
    hence "\<exists>nx \<in> set(sourcenodes as). nx \<in> S" by fastforce
    then obtain nx ns ns' where "sourcenodes as = ns@nx#ns'"
      and "nx \<in> S" and "\<forall>n' \<in> set ns. n' \<notin> S"
      by(fastforce elim!:split_list_first_propE)
    from \<open>sourcenodes as = ns@nx#ns'\<close> obtain as' a as'' 
      where "ns = sourcenodes as'"
      and "as = as'@a#as''" and "sourcenode a = nx"
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    with \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> have "n -as'\<rightarrow>\<^sub>\<iota>* nx"
      by(fastforce dest:path_split simp:intra_path_def)
    with \<open>nx \<in> S\<close> \<open>\<forall>n' \<in> set ns. n' \<notin> S\<close> \<open>ns = sourcenodes as'\<close> 
    have "nx \<in> obs_intra n S" by(fastforce intro:obs_intra_elem)
    thus ?thesis by fastforce
  qed
qed


subsection \<open>Interprocedural observable sets restricted to the slice\<close>


fun obs :: "'node list \<Rightarrow> 'node set \<Rightarrow> 'node list set" 
  where "obs [] S = {}"
  | "obs (n#ns) S = (let S' = obs_intra n S in 
  (if (S' = {} \<or> (\<exists>n' \<in> set ns. \<exists>nx. call_of_return_node n' nx \<and> nx \<notin> S)) 
   then obs ns S else (\<lambda>nx. nx#ns) ` S'))"


lemma obsI:
  assumes "n' \<in> obs_intra n S"
  and "\<forall>nx \<in> set nsx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> S"
  shows "\<lbrakk>ns = nsx@n#nsx'; \<forall>xs x xs'. nsx = xs@x#xs' \<and> obs_intra x S \<noteq> {}
     \<longrightarrow> (\<exists>x'' \<in> set (xs'@[n]). \<exists>nx. call_of_return_node x'' nx \<and> nx \<notin> S)\<rbrakk>
  \<Longrightarrow> n'#nsx' \<in> obs ns S"
proof(induct ns arbitrary:nsx)
case (Cons x xs)
  note IH = \<open>\<And>nsx. \<lbrakk>xs = nsx@n#nsx'; 
    \<forall>xs x xs'. nsx = xs @ x # xs' \<and> obs_intra x S \<noteq> {} \<longrightarrow>
    (\<exists>x''\<in>set (xs'@[n]). \<exists>nx. call_of_return_node x'' nx \<and> nx \<notin> S)\<rbrakk>
    \<Longrightarrow> n'#nsx' \<in> obs xs S\<close>
  note nsx = \<open>\<forall>xs x xs'. nsx = xs @ x # xs' \<and> obs_intra x S \<noteq> {} \<longrightarrow>
    (\<exists>x''\<in>set (xs' @ [n]). \<exists>nx. call_of_return_node x'' nx \<and> nx \<notin> S)\<close>
  show ?case
  proof(cases nsx)
    case Nil
    with \<open>x#xs = nsx@n#nsx'\<close> have "n = x" and "xs = nsx'" by simp_all
    with \<open>n' \<in> obs_intra n S\<close>
      \<open>\<forall>nx\<in>set nsx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> S\<close>
    show ?thesis by(fastforce simp:Let_def)
  next
    case (Cons z zs)
    with \<open>x#xs = nsx@n#nsx'\<close> have [simp]:"x = z" "xs = zs@n#nsx'" by simp_all
    from nsx Cons
    have "\<forall>xs x xs'. zs = xs @ x # xs' \<and> obs_intra x S \<noteq> {} \<longrightarrow>
      (\<exists>x''\<in>set (xs' @ [n]). \<exists>nx. call_of_return_node x'' nx \<and> nx \<notin> S)"
      by clarsimp(erule_tac x="z#xs" in allE,auto)
    from IH[OF \<open>xs = zs@n#nsx'\<close> this] have "n'#nsx' \<in> obs xs S" by simp
    show ?thesis
    proof(cases "obs_intra z S = {}")
      case True
      with Cons \<open>n'#nsx' \<in> obs xs S\<close> show ?thesis by(simp add:Let_def)
    next
      case False
      from nsx Cons
      have "obs_intra z S \<noteq> {} \<longrightarrow>
        (\<exists>x''\<in>set (zs @ [n]). \<exists>nx. call_of_return_node x'' nx \<and> nx \<notin> S)"
        by clarsimp
      with False have "\<exists>x''\<in>set (zs @ [n]). \<exists>nx. call_of_return_node x'' nx \<and> nx \<notin> S"
        by simp
      with \<open>xs = zs@n#nsx'\<close> 
      have "\<exists>n' \<in> set xs. \<exists>nx. call_of_return_node n' nx \<and> nx \<notin> S" by fastforce
      with Cons \<open>n'#nsx' \<in> obs xs S\<close> show ?thesis by(simp add:Let_def)
    qed
  qed
qed simp



lemma obsE [consumes 2]:
  assumes "ns' \<in> obs ns S" and "\<forall>n \<in> set (tl ns). return_node n"
  obtains nsx n nsx' n' where "ns = nsx@n#nsx'" and "ns' = n'#nsx'" 
  and "n' \<in> obs_intra n S" 
  and "\<forall>nx \<in> set nsx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> S"
  and "\<forall>xs x xs'. nsx = xs@x#xs' \<and> obs_intra x S \<noteq> {}
  \<longrightarrow> (\<exists>x'' \<in> set (xs'@[n]). \<exists>nx. call_of_return_node x'' nx \<and> nx \<notin> S)"
proof(atomize_elim)
  from \<open>ns' \<in> obs ns S\<close> \<open>\<forall>n \<in> set (tl ns). return_node n\<close>
  show "\<exists>nsx n nsx' n'. ns = nsx @ n # nsx' \<and> ns' = n' # nsx' \<and>
    n' \<in> obs_intra n S \<and> (\<forall>nx\<in>set nsx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> S) \<and>
    (\<forall>xs x xs'. nsx = xs @ x # xs' \<and> obs_intra x S \<noteq> {} \<longrightarrow>
    (\<exists>x''\<in>set (xs' @ [n]). \<exists>nx. call_of_return_node x'' nx \<and> nx \<notin> S))"
  proof(induct ns)
    case Nil thus ?case by simp
  next
    case (Cons nx ns'')
    note IH = \<open>\<lbrakk>ns' \<in> obs ns'' S; \<forall>a\<in>set (tl ns''). return_node a\<rbrakk>
      \<Longrightarrow> \<exists>nsx n nsx' n'. ns'' = nsx @ n # nsx' \<and> ns' = n' # nsx' \<and>
      n' \<in> obs_intra n S \<and> 
      (\<forall>nx\<in>set nsx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> S) \<and>
      (\<forall>xs x xs'. nsx = xs @ x # xs' \<and> obs_intra x S \<noteq> {} \<longrightarrow>
         (\<exists>x''\<in>set (xs' @ [n]). \<exists>nx. call_of_return_node x'' nx \<and> nx \<notin> S))\<close>
    from \<open>\<forall>a\<in>set (tl (nx # ns'')). return_node a\<close> have "\<forall>n \<in> set ns''. return_node n"
      by simp
    show ?case
    proof(cases ns'')
      case Nil
      with \<open>ns' \<in> obs (nx#ns'') S\<close> obtain x where "ns' = [x]" and "x \<in> obs_intra nx S"
        by(auto simp:Let_def split:if_split_asm)
      with Nil show ?thesis by fastforce
    next
      case Cons
      with \<open>\<forall>n \<in> set ns''. return_node n\<close> have "\<forall>a\<in>set (tl ns''). return_node a"
        by simp
      show ?thesis
      proof(cases "\<exists>n' \<in> set ns''. \<exists>nx'. call_of_return_node n' nx' \<and> nx' \<notin> S")
        case True
        with \<open>ns' \<in> obs (nx#ns'') S\<close> have "ns' \<in> obs ns'' S" by simp
        from IH[OF this \<open>\<forall>a\<in>set (tl ns''). return_node a\<close>]
        obtain nsx n nsx' n' where split:"ns'' = nsx @ n # nsx'"
          "ns' = n' # nsx'" "n' \<in> obs_intra n S"
          "\<forall>nx\<in>set nsx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> S"
          and imp:"\<forall>xs x xs'. nsx = xs @ x # xs' \<and> obs_intra x S \<noteq> {} \<longrightarrow>
          (\<exists>x''\<in>set (xs' @ [n]). \<exists>nx. call_of_return_node x'' nx \<and> nx \<notin> S)"
          by blast
        from True \<open>ns'' = nsx @ n # nsx'\<close>
          \<open>\<forall>nx\<in>set nsx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> S\<close>
        have "(\<exists>nx'. call_of_return_node n nx' \<and> nx' \<notin> S) \<or>
          (\<exists>n'\<in>set nsx. \<exists>nx'. call_of_return_node n' nx' \<and> nx' \<notin> S)" by fastforce
        thus ?thesis
        proof
          assume "\<exists>nx'. call_of_return_node n nx' \<and> nx' \<notin> S"
          with split show ?thesis by clarsimp
        next
          assume "\<exists>n'\<in>set nsx. \<exists>nx'. call_of_return_node n' nx' \<and> nx' \<notin> S"
          with imp have "\<forall>xs x xs'. nx#nsx = xs @ x # xs' \<and> obs_intra x S \<noteq> {} \<longrightarrow>
          (\<exists>x''\<in>set (xs' @ [n]). \<exists>nx. call_of_return_node x'' nx \<and> nx \<notin> S)"
            apply clarsimp apply(case_tac xs) apply auto
            by(erule_tac x="list" in allE,auto)+
          with split Cons show ?thesis by auto
        qed
      next
        case False
        hence "\<forall>n'\<in>set ns''. \<forall>nx'. call_of_return_node n' nx' \<longrightarrow> nx' \<in> S" by simp
        show ?thesis
        proof(cases "obs_intra nx S = {}")
          case True
          with \<open>ns' \<in> obs (nx#ns'') S\<close> have "ns' \<in> obs ns'' S" by simp
          from IH[OF this \<open>\<forall>a\<in>set (tl ns''). return_node a\<close>]
          obtain nsx n nsx' n' where split:"ns'' = nsx @ n # nsx'"
            "ns' = n' # nsx'" "n' \<in> obs_intra n S"
            "\<forall>nx\<in>set nsx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> S"
            and imp:"\<forall>xs x xs'. nsx = xs @ x # xs' \<and> obs_intra x S \<noteq> {} \<longrightarrow>
            (\<exists>x''\<in>set (xs' @ [n]). \<exists>nx. call_of_return_node x'' nx \<and> nx \<notin> S)"
            by blast
          from True imp Cons 
          have "\<forall>xs x xs'. nx#nsx = xs @ x # xs' \<and> obs_intra x S \<noteq> {} \<longrightarrow>
            (\<exists>x''\<in>set (xs' @ [n]). \<exists>nx. call_of_return_node x'' nx \<and> nx \<notin> S)"
            by clarsimp (hypsubst_thin,case_tac xs,clarsimp+,erule_tac x="list" in allE,auto)
          with split Cons show ?thesis by auto
        next
          case False
          with \<open>\<forall>n'\<in>set ns''. \<forall>nx'. call_of_return_node n' nx' \<longrightarrow> nx' \<in> S\<close>
            \<open>ns' \<in> obs (nx # ns'') S\<close>
          obtain nx'' where "ns' = nx''#ns''" and "nx'' \<in> obs_intra nx S"
          by(fastforce simp:Let_def split:if_split_asm)
          { fix n' assume "n'\<in>set ns''"
            with \<open>\<forall>n \<in> set ns''. return_node n\<close> have "return_node n'" by simp
            hence "\<exists>!n''. call_of_return_node n' n''" 
              by(rule return_node_call_of_return_node)
            from \<open>n'\<in>set ns''\<close> 
              \<open>\<forall>n'\<in>set ns''. \<forall>nx'. call_of_return_node n' nx' \<longrightarrow> nx' \<in> S\<close>
            have "\<forall>nx'. call_of_return_node n' nx' \<longrightarrow> nx' \<in> S" by simp
            with \<open>\<exists>!n''. call_of_return_node n' n''\<close> 
            have "\<exists>n''. call_of_return_node n' n'' \<and> n'' \<in> S" by fastforce }
          with \<open>ns' = nx''#ns''\<close> \<open>nx'' \<in> obs_intra nx S\<close> show ?thesis by fastforce
        qed
      qed
    qed
  qed
qed



lemma obs_split_det:
  assumes "xs@x#xs' = ys@y#ys'" 
  and "obs_intra x S \<noteq> {}" 
  and "\<forall>x' \<in> set xs'. \<exists>x''. call_of_return_node x' x'' \<and> x'' \<in> S"
  and "\<forall>zs z zs'. xs = zs@z#zs' \<and> obs_intra z S \<noteq> {}
  \<longrightarrow> (\<exists>z'' \<in> set (zs'@[x]). \<exists>nx. call_of_return_node z'' nx \<and> nx \<notin> S)"
  and "obs_intra y S \<noteq> {}" 
  and "\<forall>y' \<in> set ys'. \<exists>y''. call_of_return_node y' y'' \<and> y'' \<in> S"
  and "\<forall>zs z zs'. ys = zs@z#zs' \<and> obs_intra z S \<noteq> {}
  \<longrightarrow> (\<exists>z'' \<in> set (zs'@[y]). \<exists>ny. call_of_return_node z'' ny \<and> ny \<notin> S)"
  shows "xs = ys \<and> x = y \<and> xs' = ys'"
using assms
proof(induct xs arbitrary:ys)
  case Nil
  note impy = \<open>\<forall>zs z zs'. ys = zs@z#zs' \<and> obs_intra z S \<noteq> {}
    \<longrightarrow> (\<exists>z'' \<in> set (zs'@[y]). \<exists>ny. call_of_return_node z'' ny \<and> ny \<notin> S)\<close>
  show ?case
  proof(cases "ys = []")
    case True
    with Nil \<open>[]@x#xs' = ys@y#ys'\<close> show ?thesis by simp
  next
    case False
    with \<open>[] @ x # xs' = ys @ y # ys'\<close> 
    obtain zs where "x#zs = ys" and "xs' = zs@y#ys'" by(auto simp:Cons_eq_append_conv)
    from \<open>x#zs = ys\<close> \<open>obs_intra x S \<noteq> {}\<close> impy 
    have "\<exists>z'' \<in> set (zs@[y]). \<exists>ny. call_of_return_node z'' ny \<and> ny \<notin> S"
      by blast
    with \<open>xs' = zs@y#ys'\<close> \<open>\<forall>x' \<in> set xs'. \<exists>x''. call_of_return_node x' x'' \<and> x'' \<in> S\<close>
    have False by fastforce
    thus ?thesis by simp
  qed
next
  case (Cons w ws)
  note IH = \<open>\<And>ys. \<lbrakk>ws @ x # xs' = ys @ y # ys'; obs_intra x S \<noteq> {};
    \<forall>x'\<in>set xs'. \<exists>x''. call_of_return_node x' x'' \<and> x'' \<in> S;
    \<forall>zs z zs'. ws = zs @ z # zs' \<and> obs_intra z S \<noteq> {} \<longrightarrow>
      (\<exists>z''\<in>set (zs' @ [x]). \<exists>nx. call_of_return_node z'' nx \<and> nx \<notin> S);
    obs_intra y S \<noteq> {}; \<forall>y'\<in>set ys'. \<exists>y''. call_of_return_node y' y'' \<and> y'' \<in> S;
    \<forall>zs z zs'. ys = zs @ z # zs' \<and> obs_intra z S \<noteq> {} \<longrightarrow>
      (\<exists>z''\<in>set (zs' @ [y]). \<exists>ny. call_of_return_node z'' ny \<and> ny \<notin> S)\<rbrakk>    
    \<Longrightarrow> ws = ys \<and> x = y \<and> xs' = ys'\<close>
  note impw = \<open>\<forall>zs z zs'. w # ws = zs @ z # zs' \<and> obs_intra z S \<noteq> {} \<longrightarrow>
    (\<exists>z''\<in>set (zs' @ [x]). \<exists>nx. call_of_return_node z'' nx \<and> nx \<notin> S)\<close>
  note impy = \<open>\<forall>zs z zs'. ys = zs @ z # zs' \<and> obs_intra z S \<noteq> {} \<longrightarrow>
    (\<exists>z''\<in>set (zs' @ [y]). \<exists>ny. call_of_return_node z'' ny \<and> ny \<notin> S)\<close>
  show ?case
  proof(cases ys)
    case Nil
    with \<open>(w#ws) @ x # xs' = ys @ y # ys'\<close> have "y = w" and "ys' = ws @ x # xs'"
      by simp_all
    from \<open>y = w\<close> \<open>obs_intra y S \<noteq> {}\<close> impw
    have "\<exists>z''\<in>set (ws @ [x]). \<exists>nx. call_of_return_node z'' nx \<and> nx \<notin> S" by blast
    with \<open>ys' = ws @ x # xs'\<close> 
      \<open>\<forall>y'\<in>set ys'. \<exists>y''. call_of_return_node y' y'' \<and> y'' \<in> S\<close>
    have False by fastforce
    thus ?thesis by simp
  next
    case (Cons w' ws')
    with \<open>(w # ws) @ x # xs' = ys @ y # ys'\<close> have "w = w'"
      and "ws @ x # xs' = ws' @ y # ys'" by simp_all
    from impw have imp1:"\<forall>zs z zs'. ws = zs @ z # zs' \<and> obs_intra z S \<noteq> {} \<longrightarrow>
      (\<exists>z''\<in>set (zs' @ [x]). \<exists>nx. call_of_return_node z'' nx \<and> nx \<notin> S)"
      by clarsimp(erule_tac x="w#zs" in allE,clarsimp)
    from Cons impy have imp2:"\<forall>zs z zs'. ws' = zs @ z # zs' \<and> obs_intra z S \<noteq> {} \<longrightarrow>
      (\<exists>z''\<in>set (zs' @ [y]). \<exists>ny. call_of_return_node z'' ny \<and> ny \<notin> S)"
      by clarsimp(erule_tac x="w'#zs" in allE,clarsimp)
    from IH[OF \<open>ws @ x # xs' = ws' @ y # ys'\<close> \<open>obs_intra x S \<noteq> {}\<close>
      \<open>\<forall>x'\<in>set xs'. \<exists>x''. call_of_return_node x' x'' \<and> x'' \<in> S\<close> imp1
      \<open>obs_intra y S \<noteq> {}\<close> \<open>\<forall>y'\<in>set ys'. \<exists>y''. call_of_return_node y' y'' \<and> y'' \<in> S\<close> 
      imp2]
    have "ws = ws' \<and> x = y \<and> xs' = ys'" .
    with \<open>w = w'\<close> Cons show ?thesis by simp
  qed
qed


lemma in_obs_valid:
  assumes "ns' \<in> obs ns S" and "\<forall>n \<in> set ns. valid_node n"
  shows "\<forall>n \<in> set ns'. valid_node n"
  using \<open>ns' \<in> obs ns S\<close> \<open>\<forall>n \<in> set ns. valid_node n\<close>
  by(induct ns)(auto intro:in_obs_intra_valid simp:Let_def split:if_split_asm)



end

end

