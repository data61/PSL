section \<open>Instantiate CFG locale with While CFG\<close>

theory Interpretation imports 
  WCFG 
  "../Basic/CFGExit" 
begin

subsection \<open>Instatiation of the \<open>CFG\<close> locale\<close>

abbreviation sourcenode :: "w_edge \<Rightarrow> w_node"
  where "sourcenode e \<equiv> fst e"

abbreviation targetnode :: "w_edge \<Rightarrow> w_node"
  where "targetnode e \<equiv> snd(snd e)"

abbreviation kind :: "w_edge \<Rightarrow> state edge_kind"
  where "kind e \<equiv> fst(snd e)"


definition valid_edge :: "cmd \<Rightarrow> w_edge \<Rightarrow> bool"
  where "valid_edge prog a \<equiv> prog \<turnstile> sourcenode a -kind a\<rightarrow> targetnode a"

definition valid_node ::"cmd \<Rightarrow> w_node \<Rightarrow> bool"
  where "valid_node prog n \<equiv> 
    (\<exists>a. valid_edge prog a \<and> (n = sourcenode a \<or> n = targetnode a))"


lemma While_CFG_aux:
  "CFG sourcenode targetnode (valid_edge prog) Entry"
proof(unfold_locales)
  fix a assume "valid_edge prog a" and "targetnode a = (_Entry_)"
  obtain nx et nx' where "a = (nx,et,nx')" by (cases a) auto
  with \<open>valid_edge prog a\<close> \<open>targetnode a = (_Entry_)\<close> 
  have "prog \<turnstile> nx -et\<rightarrow> (_Entry_)" by(simp add:valid_edge_def)
  thus False by fastforce
next
  fix a a'
  assume assms:"valid_edge prog a" "valid_edge prog a'"
    "sourcenode a = sourcenode a'" "targetnode a = targetnode a'"
  obtain x et y where [simp]:"a = (x,et,y)" by (cases a) auto
  obtain x' et' y' where [simp]:"a' = (x',et',y')" by (cases a') auto
  from assms have "et = et'"
    by(fastforce intro:WCFG_edge_det simp:valid_edge_def)
  with \<open>sourcenode a = sourcenode a'\<close> \<open>targetnode a = targetnode a'\<close>
  show "a = a'" by simp
qed

interpretation While_CFG:
  CFG sourcenode targetnode kind "valid_edge prog" Entry
  for prog
  by(rule While_CFG_aux)


lemma While_CFGExit_aux:
  "CFGExit sourcenode targetnode kind (valid_edge prog) Entry Exit"
proof(unfold_locales)
  fix a assume "valid_edge prog a" and "sourcenode a = (_Exit_)"
  obtain nx et nx' where "a = (nx,et,nx')" by (cases a) auto
  with \<open>valid_edge prog a\<close> \<open>sourcenode a = (_Exit_)\<close> 
  have "prog \<turnstile> (_Exit_) -et\<rightarrow> nx'" by(simp add:valid_edge_def)
  thus False by fastforce
next
  have "prog \<turnstile> (_Entry_) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (_Exit_)" by(rule WCFG_Entry_Exit)
  thus "\<exists>a. valid_edge prog a \<and> sourcenode a = (_Entry_) \<and>
            targetnode a = (_Exit_) \<and> kind a = (\<lambda>s. False)\<^sub>\<surd>"
    by(fastforce simp:valid_edge_def)
qed

interpretation While_CFGExit:
  CFGExit sourcenode targetnode kind "valid_edge prog" Entry Exit
  for prog
by(rule While_CFGExit_aux)

end
