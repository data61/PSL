section \<open>Core Lens Laws\<close>

theory Lens_Laws
imports
  Two Interp
begin

subsection \<open>Lens Signature\<close>
  
text \<open>This theory introduces the signature of lenses and indentifies the core algebraic hierarchy of lens 
  classes, including laws for well-behaved, very well-behaved, and bijective lenses~\cite{Foster07,Fischer2015,Gibbons17}.\<close>
  
record ('a, 'b) lens =
  lens_get :: "'b \<Rightarrow> 'a" ("get\<index>")
  lens_put :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" ("put\<index>")

type_notation
  lens (infixr "\<Longrightarrow>" 0)

text \<open>
  \begin{figure}
  \begin{center}
    \includegraphics[width=6cm]{figures/Lens}
  \end{center}
  \vspace{-5ex}
  \caption{Visualisation of a simple lens}
  \label{fig:Lens}
  \end{figure}

  A lens $X : \view \lto \src$, for source type $\src$ and view type $\view$, identifies
  $\view$ with a subregion of $\src$~\cite{Foster07,Foster09}, as illustrated in Figure~\ref{fig:Lens}. The arrow denotes
  $X$ and the hatched area denotes the subregion $\view$ it characterises. Transformations on
  $\view$ can be performed without affecting the parts of $\src$ outside the hatched area. The lens
  signature consists of a pair of functions $\lget_X : \src \Rightarrow \view$ that extracts a view
  from a source, and $\lput_X : \src \Rightarrow \view \Rightarrow \src$ that updates a view within
  a given source. \<close>

named_theorems lens_defs

text \<open> \<open>lens_source\<close> gives the set of constructible sources; that is those that can be built
  by putting a value into an arbitrary source. \<close>

definition lens_source :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'b set" ("\<S>\<index>") where
"lens_source X = {s. \<exists> v s'. s = put\<^bsub>X\<^esub> s' v}"

abbreviation some_source :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'b" ("src\<index>") where
"some_source X \<equiv> (SOME s. s \<in> \<S>\<^bsub>X\<^esub>)"

definition lens_create :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("create\<index>") where
[lens_defs]: "create\<^bsub>X\<^esub> v = put\<^bsub>X\<^esub> (src\<^bsub>X\<^esub>) v"

text \<open> Function $\lcreate_X~v$ creates an instance of the source type of $X$ by injecting $v$
  as the view, and leaving the remaining context arbitrary. \<close>

subsection \<open>Weak Lenses\<close>

text \<open> Weak lenses are the least constrained class of lenses in our algebraic hierarchy. They
  simply require that the PutGet law~\cite{Foster09,Fischer2015} is satisfied, meaning that
  $\lget$ is the inverse of $\lput$. \<close>

locale weak_lens =
  fixes x :: "'a \<Longrightarrow> 'b" (structure)
  assumes put_get: "get (put \<sigma> v) = v"
begin
  lemma source_nonempty: "\<exists> s. s \<in> \<S>"
    by (auto simp add: lens_source_def)

  lemma put_closure: "put \<sigma> v \<in> \<S>"
    by (auto simp add: lens_source_def)

  lemma create_closure: "create v \<in> \<S>"
    by (simp add: lens_create_def put_closure)

  lemma src_source [simp]: "src \<in> \<S>"
    using some_in_eq source_nonempty by auto

  lemma create_get: "get (create v) = v"
    by (simp add: lens_create_def put_get)

  lemma create_inj: "inj create"
    by (metis create_get injI)

  text \<open> The update function is analogous to the record update function which lifts a function
    on a view type to one on the source type. \<close>
    
  definition update :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b)" where
  [lens_defs]: "update f \<sigma> = put \<sigma> (f (get \<sigma>))"

  lemma get_update: "get (update f \<sigma>) = f (get \<sigma>)"
    by (simp add: put_get update_def)

  lemma view_determination: 
    assumes "put \<sigma> u = put \<rho> v"
    shows "u = v"
    by (metis assms put_get)
    
  lemma put_inj: "inj (put \<sigma>)"
    by (simp add: injI view_determination)
end

declare weak_lens.put_get [simp]
declare weak_lens.create_get [simp]

subsection \<open>Well-behaved Lenses\<close>

text \<open> Well-behaved lenses add to weak lenses that requirement that the GetPut law~\cite{Foster09,Fischer2015}
  is satisfied, meaning that $\lput$ is the inverse of $\lget$. \<close>

locale wb_lens = weak_lens +
  assumes get_put: "put \<sigma> (get \<sigma>) = \<sigma>"
begin

  lemma put_twice: "put (put \<sigma> v) v = put \<sigma> v"
    by (metis get_put put_get)

  lemma put_surjectivity: "\<exists> \<rho> v. put \<rho> v = \<sigma>"
    using get_put by blast

  lemma source_stability: "\<exists> v. put \<sigma> v = \<sigma>"
    using get_put by auto

  lemma source_UNIV [simp]: "\<S> = UNIV"
    by (metis UNIV_eq_I put_closure wb_lens.source_stability wb_lens_axioms)

end

declare wb_lens.get_put [simp]

lemma wb_lens_weak [simp]: "wb_lens x \<Longrightarrow> weak_lens x"
  by (simp add: wb_lens_def)

subsection \<open> Mainly Well-behaved Lenses \<close>

text \<open> Mainly well-behaved lenses extend weak lenses with the PutPut law that shows how one put
  override a previous one. \<close>

locale mwb_lens = weak_lens +
  assumes put_put: "put (put \<sigma> v) u = put \<sigma> u"
begin

  lemma update_comp: "update f (update g \<sigma>) = update (f \<circ> g) \<sigma>"
    by (simp add: put_get put_put update_def)

  text \<open> Mainly well-behaved lenses give rise to a weakened version of the $get-put$ law, 
    where the source must be within the set of constructible sources. \<close>

  lemma weak_get_put: "\<sigma> \<in> \<S> \<Longrightarrow> put \<sigma> (get \<sigma>) = \<sigma>"
    by (auto simp add: lens_source_def put_get put_put)

  lemma weak_source_determination:
    assumes "\<sigma> \<in> \<S>" "\<rho> \<in> \<S>" "get \<sigma> = get \<rho>" "put \<sigma> v = put \<rho> v"
    shows "\<sigma> = \<rho>"
    by (metis assms put_put weak_get_put)

   lemma weak_put_eq:
     assumes "\<sigma> \<in> \<S>" "get \<sigma> = k" "put \<sigma> u = put \<rho> v"
     shows "put \<rho> k = \<sigma>"
     by (metis assms put_put weak_get_put)

  text \<open> Provides $s$ is constructible, then @{term get} can be uniquely determined from @{term put} \<close>

  lemma weak_get_via_put: "s \<in> \<S> \<Longrightarrow> get s = (THE v. put s v = s)"
    by (rule sym, auto intro!: the_equality weak_get_put, metis put_get)

end

declare mwb_lens.put_put [simp]
declare mwb_lens.weak_get_put [simp]

lemma mwb_lens_weak [simp]:
  "mwb_lens x \<Longrightarrow> weak_lens x"
  by (simp add: mwb_lens.axioms(1))

subsection \<open>Very Well-behaved Lenses\<close>

text \<open>Very well-behaved lenses combine all three laws, as in the literature~\cite{Foster09,Fischer2015}.\<close>

locale vwb_lens = wb_lens + mwb_lens
begin

  lemma source_determination:
    assumes "get \<sigma> = get \<rho>" "put \<sigma> v = put \<rho> v"
    shows "\<sigma> = \<rho>"
    by (metis assms get_put put_put)
    
 lemma put_eq:
   assumes "get \<sigma> = k" "put \<sigma> u = put \<rho> v"
   shows "put \<rho> k = \<sigma>"
   using assms weak_put_eq[of \<sigma> k u \<rho> v] by (simp)

  text \<open> @{term get} can be uniquely determined from @{term put} \<close>

  lemma get_via_put: "get s = (THE v. put s v = s)"
    by (simp add: weak_get_via_put)

end

lemma vwb_lens_wb [simp]: "vwb_lens x \<Longrightarrow> wb_lens x"
  by (simp add: vwb_lens_def)

lemma vwb_lens_mwb [simp]: "vwb_lens x \<Longrightarrow> mwb_lens x"
  using vwb_lens_def by auto

subsection \<open> Ineffectual Lenses \<close>

text \<open>Ineffectual lenses can have no effect on the view type -- application of the $\lput$ function
  always yields the same source. They are thus, trivially, very well-behaved lenses.\<close>

locale ief_lens = weak_lens +
  assumes put_inef: "put \<sigma> v = \<sigma>"
begin

sublocale vwb_lens
proof
  fix \<sigma> v u
  show "put \<sigma> (get \<sigma>) = \<sigma>"
    by (simp add: put_inef)
  show "put (put \<sigma> v) u = put \<sigma> u"
    by (simp add: put_inef)
qed

lemma ineffectual_const_get:
  "\<exists> v.  \<forall> \<sigma>\<in>\<S>. get \<sigma> = v"
  using put_get put_inef by auto

end

abbreviation "eff_lens X \<equiv> (weak_lens X \<and> (\<not> ief_lens X))"

subsection \<open> Bijective Lenses \<close>

text \<open>Bijective lenses characterise the situation where the source and view type are equivalent:
  in other words the view type full characterises the whole source type. It is often useful
  when the view type and source type are syntactically different, but nevertheless correspond
  precisely in terms of what they observe. Bijective lenses are formulates using
  the strong GetPut law~\cite{Foster09,Fischer2015}.\<close>

locale bij_lens = weak_lens +
  assumes strong_get_put: "put \<sigma> (get \<rho>) = \<rho>"
begin

sublocale vwb_lens
proof
  fix \<sigma> v u
  show "put \<sigma> (get \<sigma>) = \<sigma>"
    by (simp add: strong_get_put)
  show "put (put \<sigma> v) u = put \<sigma> u"
    by (metis bij_lens.strong_get_put bij_lens_axioms put_get)
qed
    
  lemma put_bij: "bij_betw (put \<sigma>) UNIV UNIV"
    by (metis bijI put_inj strong_get_put surj_def)

  lemma put_is_create: "\<sigma> \<in> \<S> \<Longrightarrow> put \<sigma> v = create v"
    by (metis create_get strong_get_put)

  lemma get_create: "\<sigma> \<in> \<S> \<Longrightarrow> create (get \<sigma>) = \<sigma>"
    by (simp add: lens_create_def strong_get_put)
    
end

declare bij_lens.strong_get_put [simp]
declare bij_lens.get_create [simp]

lemma bij_lens_weak [simp]:
  "bij_lens x \<Longrightarrow> weak_lens x"
  by (simp_all add: bij_lens_def)

lemma bij_lens_vwb [simp]: "bij_lens x \<Longrightarrow> vwb_lens x"
  by (metis bij_lens.strong_get_put bij_lens_weak mwb_lens.intro mwb_lens_axioms.intro vwb_lens_def wb_lens.intro wb_lens_axioms.intro weak_lens.put_get)

subsection \<open>Lens Independence\<close>

text \<open> 
  \begin{figure}
  \begin{center}
    \includegraphics[width=6cm]{figures/Independence}
  \end{center}
  \vspace{-5ex}
  \caption{Lens Independence}
  \label{fig:Indep}
  \end{figure}

  Lens independence shows when two lenses $X$ and $Y$ characterise disjoint regions of the
  source type, as illustrated in Figure~\ref{fig:Indep}. We specify this by requiring that the $\lput$ 
  functions of the two lenses commute, and that the $\lget$ function of each lens is unaffected by 
  application of $\lput$ from the corresponding lens. \<close>

locale lens_indep =
  fixes X :: "'a \<Longrightarrow> 'c" and Y :: "'b \<Longrightarrow> 'c"
  assumes lens_put_comm: "put\<^bsub>X\<^esub> (put\<^bsub>Y\<^esub> \<sigma> v) u = put\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> \<sigma> u) v"
  and lens_put_irr1: "get\<^bsub>X\<^esub> (put\<^bsub>Y\<^esub> \<sigma> v) = get\<^bsub>X\<^esub> \<sigma>"
  and lens_put_irr2: "get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> \<sigma> u) = get\<^bsub>Y\<^esub> \<sigma>"

notation lens_indep (infix "\<bowtie>" 50)

lemma lens_indepI:
  "\<lbrakk> \<And> u v \<sigma>. lens_put x (lens_put y \<sigma> v) u = lens_put y (lens_put x \<sigma> u) v;
     \<And> v \<sigma>. lens_get x (lens_put y \<sigma> v) = lens_get x \<sigma>;
     \<And> u \<sigma>. lens_get y (lens_put x \<sigma> u) = lens_get y \<sigma> \<rbrakk> \<Longrightarrow> x \<bowtie> y"
  by (simp add: lens_indep_def)

text \<open>Lens independence is symmetric.\<close>

lemma lens_indep_sym:  "x \<bowtie> y \<Longrightarrow> y \<bowtie> x"
  by (simp add: lens_indep_def)

lemma lens_indep_comm:
  "x \<bowtie> y \<Longrightarrow> lens_put x (lens_put y \<sigma> v) u = lens_put y (lens_put x \<sigma> u) v"
  by (simp add: lens_indep_def)

lemma lens_indep_get [simp]:
  assumes "x \<bowtie> y"
  shows "lens_get x (lens_put y \<sigma> v) = lens_get x \<sigma>"
  using assms lens_indep_def by fastforce

end