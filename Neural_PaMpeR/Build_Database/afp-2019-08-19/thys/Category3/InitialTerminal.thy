(*  Title:       InitialTerminal
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter InitialTerminal

theory InitialTerminal
imports EpiMonoIso
begin

  text\<open>
    This theory defines the notions of initial and terminal object in a category
    and establishes some properties of these notions, including that when they exist
    they are unique up to isomorphism.
\<close>

  context category
  begin

    definition initial
    where "initial a \<equiv> ide a \<and> (\<forall>b. ide b \<longrightarrow> (\<exists>!f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright>))"

    definition terminal
    where "terminal b \<equiv> ide b \<and> (\<forall>a. ide a \<longrightarrow> (\<exists>!f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright>))"
    
    abbreviation initial_arr
    where "initial_arr f \<equiv> arr f \<and> initial (dom f)"
    
    abbreviation terminal_arr
    where "terminal_arr f \<equiv> arr f \<and> terminal (cod f)"
    
    abbreviation point
    where "point f \<equiv> arr f \<and> terminal (dom f)"

    lemma initial_arr_unique:
    assumes "par f f'" and "initial_arr f" and "initial_arr f'"
    shows "f = f'"
      using assms in_homI initial_def ide_cod by blast

    lemma initialI [intro]:
    assumes "ide a" and "\<And>b. ide b \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
    shows "initial a"
      using assms initial_def by auto

    lemma initialE [elim]:
    assumes "initial a" and "ide b"
    obtains f where "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>" and "\<And>f'. \<guillemotleft>f' : a \<rightarrow> b\<guillemotright> \<Longrightarrow> f' = f"
      using assms initial_def initial_arr_unique by meson
      
    lemma terminal_arr_unique:
    assumes "par f f'" and "terminal_arr f" and "terminal_arr f'"
    shows "f = f'"
      using assms in_homI terminal_def ide_dom by blast

    lemma terminalI [intro]:
    assumes "ide b" and "\<And>a. ide a \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
    shows "terminal b"
      using assms terminal_def by auto

    lemma terminalE [elim]:
    assumes "terminal b" and "ide a"
    obtains f where "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>" and "\<And>f'. \<guillemotleft>f' : a \<rightarrow> b\<guillemotright> \<Longrightarrow> f' = f"
      using assms terminal_def terminal_arr_unique by meson

    theorem terminal_objs_isomorphic:
    assumes "terminal a" and "terminal b"
    shows "isomorphic a b"
    proof -
      from assms obtain f where f: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
        using terminal_def by meson
      from assms obtain g where g: "\<guillemotleft>g : b \<rightarrow> a\<guillemotright>"
        using terminal_def by meson
      have "iso f"
        using assms f g
        by (metis (no_types, lifting) iso_iff_section_and_retraction retractionI sectionI
            terminal_def comp_in_homI ide_in_hom)
      thus ?thesis using f by auto
    qed

    theorem initial_objs_isomorphic:
    assumes "initial a" and "initial b"
    shows "isomorphic a b"
    proof -
      from assms obtain f where f: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>" using initial_def by auto
      from assms obtain g where g: "\<guillemotleft>g : b \<rightarrow> a\<guillemotright>" using initial_def by auto
      have "iso f"
        using assms f g
        by (metis iso_iff_section_and_retraction retractionI sectionI
            initial_def comp_in_homI ide_in_hom)
      thus ?thesis
        using f by auto
    qed

    lemma point_is_mono:
    assumes "point f"
    shows "mono f"
    proof -
      have "ide (cod f)" using assms by auto
      from this obtain t where t: "\<guillemotleft>t: cod f \<rightarrow> dom f\<guillemotright>"
        using assms terminal_def by blast
      thus ?thesis
        using assms terminal_def monoI
        by (metis seqE in_homI dom_comp ide_dom terminal_def)
    qed
      
  end

end

