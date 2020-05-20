theory Abbrevs
imports PIMP SyntaxTweaks
begin


text \<open>now we can use dots as a term\<close>

consts dots::"'a" ("\<dots>") 


lemma conj_to_impl: "(P \<and> Q \<longrightarrow> R) = (P \<longrightarrow> Q \<longrightarrow> R)"
  by auto


notation (in xvalid_program) (latex output)
barrier_inv ("flush'_inv")


abbreviation
"acquire sb owns \<equiv> acquired True sb owns"
notation (latex output)
direct_memop_step ("_ \<^latex>\<open>$\\overset{\\isa{v}_\\isa{d}}{\\rightarrow}_{\\isa{m}}$\<close> _" [60,60] 100)
notation (latex output)
virtual_memop_step ("_ \<^latex>\<open>$\\overset{\\isa{v}}{\\rightarrow}_{\\isa{m}}$\<close> _" [60,60] 100)



context program
begin
term "(ts, m) \<Rightarrow>\<^sub>s\<^sub>b (ts',m')"
notation (latex output) store_buffer.concurrent_step ("_ \<^latex>\<open>$\\overset{\\isa{sb}}{\\Rightarrow}$\<close> _" [60,60] 100)
notation (latex output) virtual.concurrent_step ("_ \<^latex>\<open>$\\overset{\\isa{v}}{\\Rightarrow}$\<close> _" [60,60] 100)
thm store_buffer.concurrent_step.Program
end


abbreviation (output)
"sbh_global_step \<equiv> computation.concurrent_step sbh_memop_step flush_step stmt_step (\<lambda>p p' is sb. sb @ [Prog\<^sub>s\<^sub>b p p' is])"

notation (latex output)
sbh_global_step ("_ \<^latex>\<open>$\\overset{\\isa{sbh}}{\\Rightarrow}$\<close> _" [60,60] 100)


notation (latex output)
direct_pimp_step ("_ \<^latex>\<open>$\\overset{\\isa{v}}{\\Rightarrow}$\<close> _" [60,60] 100)


notation (latex output)
sbh_memop_step ("_ \<^latex>\<open>$\\overset{\\isa{sbh}}{\\rightarrow}_{\\isa{m}}$\<close> _" [60,60] 100)

notation (latex output)
sb_memop_step ("_ \<^latex>\<open>$\\overset{\\isa{sb}}{\\rightarrow}_{\\isa{m}}$\<close> _" [60,60] 100)


notation (output) 
sim_direct_config ("_ \<sim> _ " [60,60] 100)

notation (output) 
flush_step ("_ \<rightarrow>\<^sub>s\<^sub>b\<^sub>h _" [60,60] 100)

notation (output) 
store_buffer_step ("_ \<rightarrow>\<^sub>s\<^sub>b _" [60,60] 100)

notation (output)
outstanding_refs ("refs")

notation (output)
is_volatile_Write\<^sub>s\<^sub>b ("volatile'_Write")

abbreviation (output)
"not_volatile_write \<equiv> Not \<circ> is_volatile_Write\<^sub>s\<^sub>b"

notation (output)
"flush_all_until_volatile_write" ("exec'_all'_until'_volatile'_write")
notation (output)
"share_all_until_volatile_write" ("share'_all'_until'_volatile'_write")

notation (output)
stmt_step ("_\<turnstile> _ \<rightarrow>\<^sub>p _" [60,60,60] 100)

notation (output)
augment_rels ("aug")

context program
begin
notation (latex output)
direct_concurrent_step ("_ \<^latex>\<open>$\\overset{\\isa{v}_\\isa{d}}{\\Rightarrow}$\<close> _" [60,60] 100)
notation (latex output)
direct_concurrent_steps ("_ \<^latex>\<open>$\\overset{\\isa{v}_\\isa{d}}{\\Rightarrow}^{*}$\<close> _" [60,60] 100)

notation (latex output)
sbh_concurrent_step ("_ \<^latex>\<open>$\\overset{\\isa{sbh}}{\\Rightarrow}$\<close> _" [60,60] 100)
notation (latex output) 
sbh_concurrent_steps ("_ \<^latex>\<open>$\\overset{\\isa{sbh}}{\\Rightarrow}^{*}$\<close> _" [60,60] 100)

notation (latex output)
sb_concurrent_step ("_ \<^latex>\<open>$\\overset{\\isa{sb}}{\\Rightarrow}$\<close> _" [60,60] 100)
notation (latex output) 
sb_concurrent_steps ("_ \<^latex>\<open>$\\overset{\\isa{sb}}{\\Rightarrow}^{*}$\<close> _" [60,60] 100)

notation (latex output)
virtual_concurrent_step ("_ \<^latex>\<open>$\\overset{\\isa{v}}{\\Rightarrow}$\<close> _" [60,60] 100)
notation (latex output) 
virtual_concurrent_steps ("_ \<^latex>\<open>$\\overset{\\isa{v}}{\\Rightarrow}^{*}$\<close> _" [60,60] 100)
end


context xvalid_program_progress
begin

abbreviation
"safe_reach_virtual_free_flowing \<equiv> safe_reach virtual_concurrent_step safe_free_flowing"
notation (latex output)
"safe_reach_virtual_free_flowing" ("safe'_reach")

abbreviation
"safe_reach_direct_delayed \<equiv> safe_reach direct_concurrent_step safe_delayed"

notation (latex output)
"safe_reach_direct_delayed" ("safe'_reach'_delayed")

end



(* hide unit's in tuples *)

translations
 "x" <= "(x,())"
 "x" <= "((),x)"


translations
"CONST initial\<^sub>v xs ys" <= "CONST initial\<^sub>v xs ys zs"


end
