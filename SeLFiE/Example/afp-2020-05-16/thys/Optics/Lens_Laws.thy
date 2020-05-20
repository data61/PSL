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

text \<open> Alternative parameters ordering, inspired by Back and von Wright's refinement 
  calculus~\cite{Back1998}, which similarly uses two functions to characterise updates to variables. \<close>

abbreviation (input) lens_set :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" ("lset\<index>") where
"lens_set \<equiv> (\<lambda> X v s. put\<^bsub>X\<^esub> s v)"

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

text \<open> @{text lens_source} gives the set of constructible sources; that is those that can be built
  by putting a value into an arbitrary source. \<close>

definition lens_source :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'b set" ("\<S>\<index>") where
"lens_source X = {s. \<exists> v s'. s = put\<^bsub>X\<^esub> s' v}"

abbreviation some_source :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'b" ("src\<index>") where
"some_source X \<equiv> (SOME s. s \<in> \<S>\<^bsub>X\<^esub>)"

definition lens_create :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("create\<index>") where
[lens_defs]: "create\<^bsub>X\<^esub> v = put\<^bsub>X\<^esub> (src\<^bsub>X\<^esub>) v"

text \<open> Function $\lcreate_X~v$ creates an instance of the source type of $X$ by injecting $v$
  as the view, and leaving the remaining context arbitrary. \<close>
    
definition lens_update :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b)" ("update\<index>") where
[lens_defs]: "lens_update X f \<sigma> = put\<^bsub>X\<^esub> \<sigma> (f (get\<^bsub>X\<^esub> \<sigma>))"

text \<open> The update function is analogous to the record update function which lifts a function
  on a view type to one on the source type. \<close>

definition lens_obs_eq :: "('b \<Longrightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<simeq>\<index>" 50) where
[lens_defs]: "s\<^sub>1 \<simeq>\<^bsub>X\<^esub> s\<^sub>2 = (s\<^sub>1 = put\<^bsub>X\<^esub> s\<^sub>2 (get\<^bsub>X\<^esub> s\<^sub>1))"

text \<open> This relation states that two sources are equivalent outside of the region characterised
  by lens $X$. \<close>

definition lens_override :: "('b \<Longrightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<triangleleft>\<index>" 95) where
[lens_defs]: "S\<^sub>1 \<triangleleft>\<^bsub>X\<^esub> S\<^sub>2 = put\<^bsub>X\<^esub> S\<^sub>1 (get\<^bsub>X\<^esub> S\<^sub>2)"

abbreviation (input) lens_override' :: "'a \<Rightarrow> 'a \<Rightarrow> ('b \<Longrightarrow> 'a) \<Rightarrow> 'a" ("_ \<oplus>\<^sub>L _ on _" [95,0,96] 95) where
"S\<^sub>1 \<oplus>\<^sub>L S\<^sub>2 on X \<equiv> S\<^sub>1 \<triangleleft>\<^bsub>X\<^esub> S\<^sub>2"

text \<open>Lens override uses a lens to replace part of a source type with a given value for the
  corresponding view.\<close>

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

  lemma get_update: "get (update f \<sigma>) = f (get \<sigma>)"
    by (simp add: put_get lens_update_def)

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
    by (simp add: put_get put_put lens_update_def)

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

abbreviation (input) "partial_lens \<equiv> mwb_lens"

declare mwb_lens.put_put [simp]
declare mwb_lens.weak_get_put [simp]

lemma mwb_lens_weak [simp]:
  "mwb_lens x \<Longrightarrow> weak_lens x"
  by (simp add: mwb_lens.axioms(1))

subsection \<open>Very Well-behaved Lenses\<close>

text \<open>Very well-behaved lenses combine all three laws, as in the literature~\cite{Foster09,Fischer2015}.
  The same set of axioms can be found in Back and von Wright's refinement calculus~\cite{Back1998}, 
  though with different names for the functions. \<close>

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

  lemma get_surj: "surj get"
    by (metis put_get surjI)

  text \<open> Observation equivalence is an equivalence relation. \<close>

  lemma lens_obs_equiv: "equivp (\<simeq>)"
  proof (rule equivpI)
    show "reflp (\<simeq>)"
      by (rule reflpI, simp add: lens_obs_eq_def get_put)
    show "symp (\<simeq>)"
      by (rule sympI, simp add: lens_obs_eq_def, metis get_put put_put)
    show "transp (\<simeq>)"
      by (rule transpI, simp add: lens_obs_eq_def, metis put_put)
  qed

end

abbreviation (input) "total_lens \<equiv> vwb_lens"

lemma vwb_lens_wb [simp]: "vwb_lens x \<Longrightarrow> wb_lens x"
  by (simp add: vwb_lens_def)

lemma vwb_lens_mwb [simp]: "vwb_lens x \<Longrightarrow> mwb_lens x"
  using vwb_lens_def by auto

lemma mwb_UNIV_src_is_vwb_lens: 
  "\<lbrakk> mwb_lens X; \<S>\<^bsub>X\<^esub> = UNIV \<rbrakk> \<Longrightarrow> vwb_lens X"
  using vwb_lens_def wb_lens_axioms_def wb_lens_def by fastforce

text \<open> Alternative characterisation: a very well-behaved (i.e. total) lens is a mainly well-behaved
  (i.e. partial) lens whose source is the universe set. \<close>

lemma vwb_lens_iff_mwb_UNIV_src: 
  "vwb_lens X \<longleftrightarrow> (mwb_lens X \<and> \<S>\<^bsub>X\<^esub> = UNIV)"
  by (meson mwb_UNIV_src_is_vwb_lens vwb_lens_def wb_lens.source_UNIV)

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

subsection \<open> Partially Bijective Lenses \<close>

locale pbij_lens = weak_lens +
  assumes put_det: "put \<sigma> v = put \<rho> v"
begin

  sublocale mwb_lens
  proof
    fix \<sigma> v u
    show "put (put \<sigma> v) u = put \<sigma> u"
      using put_det by blast
  qed
  
  lemma put_is_create: "put \<sigma> v = create v"
    by (simp add: lens_create_def put_det)

  lemma partial_get_put: "\<rho> \<in> \<S> \<Longrightarrow> put \<sigma> (get \<rho>) = \<rho>"
    by (metis put_det weak_get_put)

end

lemma pbij_lens_weak [simp]:
  "pbij_lens x \<Longrightarrow> weak_lens x"
  by (simp_all add: pbij_lens_def)

lemma pbij_lens_mwb [simp]: "pbij_lens x \<Longrightarrow> mwb_lens x"
  by (simp add: mwb_lens_axioms.intro mwb_lens_def pbij_lens.put_is_create)

lemma pbij_alt_intro:
  "\<lbrakk> weak_lens X; \<And> s. s \<in> \<S>\<^bsub>X\<^esub> \<Longrightarrow> create\<^bsub>X\<^esub> (get\<^bsub>X\<^esub> s) = s \<rbrakk> \<Longrightarrow> pbij_lens X"
  by (metis pbij_lens_axioms_def pbij_lens_def weak_lens.put_closure weak_lens.put_get)

subsection \<open> Bijective Lenses \<close>

text \<open>Bijective lenses characterise the situation where the source and view type are equivalent:
  in other words the view type full characterises the whole source type. It is often useful
  when the view type and source type are syntactically different, but nevertheless correspond
  precisely in terms of what they observe. Bijective lenses are formulates using
  the strong GetPut law~\cite{Foster09,Fischer2015}.\<close>

locale bij_lens = weak_lens +
  assumes strong_get_put: "put \<sigma> (get \<rho>) = \<rho>"
begin

sublocale pbij_lens
proof
  fix \<sigma> v \<rho>
  show "put \<sigma> v = put \<rho> v"
    by (metis put_get strong_get_put)
qed

sublocale vwb_lens
proof
  fix \<sigma> v u
  show "put \<sigma> (get \<sigma>) = \<sigma>"
    by (simp add: strong_get_put)
qed

  lemma put_bij: "bij_betw (put \<sigma>) UNIV UNIV"
    by (metis bijI put_inj strong_get_put surj_def)

  lemma get_create: "create (get \<sigma>) = \<sigma>"
    by (simp add: lens_create_def strong_get_put)
    
end

declare bij_lens.strong_get_put [simp]
declare bij_lens.get_create [simp]

lemma bij_lens_weak [simp]:
  "bij_lens x \<Longrightarrow> weak_lens x"
  by (simp_all add: bij_lens_def)

lemma bij_lens_pbij [simp]:
  "bij_lens x \<Longrightarrow> pbij_lens x"
  by (metis bij_lens.get_create bij_lens_def pbij_lens_axioms.intro pbij_lens_def weak_lens.put_get)

lemma bij_lens_vwb [simp]: "bij_lens x \<Longrightarrow> vwb_lens x"
  by (metis bij_lens.strong_get_put bij_lens_weak mwb_lens.intro mwb_lens_axioms.intro vwb_lens_def wb_lens.intro wb_lens_axioms.intro weak_lens.put_get)

text \<open> Alternative characterisation: a bijective lens is a partial bijective lens that is also
  very well-behaved (i.e. total). \<close>

lemma pbij_vwb_is_bij_lens:
  "\<lbrakk> pbij_lens X; vwb_lens X \<rbrakk> \<Longrightarrow> bij_lens X"
  by (unfold_locales, simp_all, meson pbij_lens.put_det vwb_lens.put_eq)

lemma bij_lens_iff_pbij_vwb:
  "bij_lens X \<longleftrightarrow> (pbij_lens X \<and> vwb_lens X)"
  using pbij_vwb_is_bij_lens by auto

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
  "\<lbrakk> \<And> u v \<sigma>. put\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> \<sigma> v) u = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> \<sigma> u) v;
     \<And> v \<sigma>. get\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> \<sigma> v) = get\<^bsub>x\<^esub> \<sigma>;
     \<And> u \<sigma>. get\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> \<sigma> u) = get\<^bsub>y\<^esub> \<sigma> \<rbrakk> \<Longrightarrow> x \<bowtie> y"
  by (simp add: lens_indep_def)

text \<open>Lens independence is symmetric.\<close>

lemma lens_indep_sym:  "x \<bowtie> y \<Longrightarrow> y \<bowtie> x"
  by (simp add: lens_indep_def)

lemma lens_indep_comm:
  "x \<bowtie> y \<Longrightarrow> put\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> \<sigma> v) u = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> \<sigma> u) v"
  by (simp add: lens_indep_def)

lemma lens_indep_get [simp]:
  assumes "x \<bowtie> y"
  shows "get\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> \<sigma> v) = get\<^bsub>x\<^esub> \<sigma>"
  using assms lens_indep_def by fastforce

text \<open> Characterisation of independence for two very well-behaved lenses \<close>

lemma lens_indep_vwb_iff:
  assumes "vwb_lens x" "vwb_lens y"
  shows "x \<bowtie> y \<longleftrightarrow> (\<forall> u v \<sigma>. put\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> \<sigma> v) u = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> \<sigma> u) v)"
proof
  assume "x \<bowtie> y"
  thus "\<forall> u v \<sigma>. put\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> \<sigma> v) u = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> \<sigma> u) v"
    by (simp add: lens_indep_comm)
next
  assume a: "\<forall> u v \<sigma>. put\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> \<sigma> v) u = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> \<sigma> u) v"
  show "x \<bowtie> y"
  proof (unfold_locales)
    fix \<sigma> v u
    from a show "put\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> \<sigma> v) u = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> \<sigma> u) v" 
      by auto
    show "get\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> \<sigma> v) = get\<^bsub>x\<^esub> \<sigma>"
      by (metis a assms(1) vwb_lens.put_eq vwb_lens_wb wb_lens_def weak_lens.put_get)
    show "get\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> \<sigma> u) = get\<^bsub>y\<^esub> \<sigma>"
      by (metis a assms(2) vwb_lens.put_eq vwb_lens_wb wb_lens_def weak_lens.put_get)
  qed
qed

subsection \<open> Lens Compatibility \<close>

text \<open> Lens compatibility is a weaker notion than independence. It allows that two lenses can overlap
  so long as they manipulate the source in the same way in that region. It is most easily defined
  in terms of a function for copying a region from one source to another using a lens. \<close>

definition lens_compat (infix "##\<^sub>L" 50) where
[lens_defs]: "lens_compat X Y = (\<forall>s\<^sub>1 s\<^sub>2. s\<^sub>1 \<triangleleft>\<^bsub>X\<^esub> s\<^sub>2 \<triangleleft>\<^bsub>Y\<^esub> s\<^sub>2 = s\<^sub>1 \<triangleleft>\<^bsub>Y\<^esub> s\<^sub>2 \<triangleleft>\<^bsub>X\<^esub> s\<^sub>2)"

lemma lens_compat_idem [simp]: "x ##\<^sub>L x"
  by (simp add: lens_defs)

lemma lens_compat_sym: "x ##\<^sub>L y \<Longrightarrow> y ##\<^sub>L x"
  by (simp add: lens_defs)

lemma lens_indep_compat [simp]: "x \<bowtie> y \<Longrightarrow> x ##\<^sub>L y"
  by (simp add: lens_override_def lens_compat_def lens_indep_comm)

end