subsection\<open>HC, SC, and ND\<close>
theory HCSCND
imports HCSC SCND NDHC
begin

theorem HCSCND:
  defines "hc F \<equiv> AX10 \<turnstile>\<^sub>H F"
  defines "nd F \<equiv> {} \<turnstile> F"
  defines "sc F \<equiv> {#} \<Rightarrow> {# F #}"
  shows "hc F \<longleftrightarrow> nd F" and "nd F \<longleftrightarrow> sc F" and "sc F \<longleftrightarrow> hc F"
using HCSC[where F=F and \<Gamma>=Mempty, simplified]
      SCND[where \<Gamma>=Mempty and \<Delta>="{#F#}"] ND.ND.CC[where F=F and \<Gamma>="{}"]
      NDHC[where \<Gamma>="{}" and F=F]
by(simp_all add: assms) blast+

end
