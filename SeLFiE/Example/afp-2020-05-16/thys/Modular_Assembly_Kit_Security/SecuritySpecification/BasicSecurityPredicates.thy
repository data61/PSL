theory BasicSecurityPredicates
imports Views "../Basics/Projection"
begin

(*Auxiliary predicate capturing that a a set of traces consists 
only of traces of a given set of events *)
definition areTracesOver :: "('e list) set \<Rightarrow> 'e set \<Rightarrow> bool "
where
"areTracesOver Tr E \<equiv> 
  \<forall> \<tau> \<in> Tr. (set \<tau>) \<subseteq> E"



(* Basic Security Predicates are properties of sets of traces
 that are parameterized with a view *)
type_synonym 'e BSP = "'e V_rec \<Rightarrow> (('e list) set) \<Rightarrow> bool"

(* Basic Security Predicates are valid if and only if they are closure property of sets of traces 
for arbitrary views and sets of traces *)
definition BSP_valid :: "'e BSP \<Rightarrow> bool"
where 
"BSP_valid bsp \<equiv> 
  \<forall>\<V> Tr E. ( isViewOn \<V> E \<and> areTracesOver Tr E ) 
              \<longrightarrow> (\<exists> Tr'. Tr' \<supseteq> Tr  \<and> bsp \<V> Tr')"

(* Removal of Confidential Events (R) *)
definition R :: "'e BSP"
where
"R \<V> Tr \<equiv> 
  \<forall>\<tau>\<in>Tr. \<exists>\<tau>'\<in>Tr. \<tau>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [] \<and> \<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<tau> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"

lemma BSP_valid_R: "BSP_valid R" 
proof -
  {  
    fix \<V>::"('e V_rec)" 
    fix Tr E
    assume "isViewOn \<V> E"
    and "areTracesOver Tr E"     
    let ?Tr'="{t. (set t) \<subseteq> E}"
    have "?Tr'\<supseteq> Tr" 
      by (meson Ball_Collect \<open>areTracesOver Tr E\<close> areTracesOver_def)
    moreover
    have "R \<V> ?Tr'" 
      proof -
        {
          fix \<tau>
          assume "\<tau> \<in> {t. (set t) \<subseteq> E}"
          let ?\<tau>'="\<tau>\<upharpoonleft>(V\<^bsub>\<V>\<^esub>)"
          have "?\<tau>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []  \<and> ?\<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<tau> \<upharpoonleft> V\<^bsub>\<V>\<^esub>" 
            using \<open>isViewOn \<V> E\<close>  disjoint_projection projection_idempotent 
            unfolding isViewOn_def V_valid_def VC_disjoint_def  by metis
          moreover
          from \<open>\<tau> \<in> {t. (set t) \<subseteq> E}\<close> have "?\<tau>' \<in> ?Tr'" using \<open>isViewOn \<V> E\<close>
            unfolding isViewOn_def
            by (simp add: list_subset_iff_projection_neutral projection_commute) 
          ultimately 
          have " \<exists>\<tau>'\<in>{t. set t \<subseteq> E}. \<tau>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [] \<and> \<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<tau> \<upharpoonleft> V\<^bsub>\<V>\<^esub>" 
            by auto
        }
        thus ?thesis unfolding R_def
          by auto
      qed  
    ultimately
    have  "\<exists> Tr'. Tr' \<supseteq> Tr  \<and> R \<V> Tr'"
      by auto
  }
  thus ?thesis 
    unfolding BSP_valid_def by auto
qed
    
(* Deletion of Confidential Events (D) *)
definition D :: "'e BSP"
where
"D \<V> Tr \<equiv> 
  \<forall>\<alpha> \<beta>. \<forall>c\<in>C\<^bsub>\<V>\<^esub>. ((\<beta> @ [c] @ \<alpha>) \<in> Tr \<and> \<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []) 
    \<longrightarrow> (\<exists>\<alpha>' \<beta>'. ((\<beta>' @ \<alpha>') \<in> Tr \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []
                  \<and> \<beta>'\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<beta>\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>)))"

lemma BSP_valid_D: "BSP_valid D"
proof -
  {  
    fix \<V>::"('e V_rec)" 
    fix Tr E
    assume "isViewOn \<V> E"
    and "areTracesOver Tr E"     
    let ?Tr'="{t. (set t) \<subseteq> E}"
    have "?Tr'\<supseteq> Tr" 
      by (meson Ball_Collect \<open>areTracesOver Tr E\<close> areTracesOver_def)
    moreover
    have "D \<V> ?Tr'"
      unfolding D_def by auto
    ultimately
    have  "\<exists> Tr'. Tr' \<supseteq> Tr  \<and> D \<V> Tr'" 
      by auto
  }
  thus ?thesis 
    unfolding BSP_valid_def by auto
qed

(* Insertion of Confidential Events (I) *)
definition I :: "'e BSP"
where
"I \<V> Tr \<equiv> 
  \<forall>\<alpha> \<beta>. \<forall>c\<in>C\<^bsub>\<V>\<^esub>. ((\<beta> @ \<alpha>) \<in> Tr \<and> \<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []) 
    \<longrightarrow> (\<exists>\<alpha>' \<beta>'. ((\<beta>' @ [c] @ \<alpha>') \<in> Tr \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []
                     \<and> \<beta>'\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<beta>\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>)))"

lemma BSP_valid_I: "BSP_valid I"
proof -
  {  
    fix \<V>::"('e V_rec)" 
    fix Tr E
    assume "isViewOn \<V> E"
    and "areTracesOver Tr E"     
    let ?Tr'="{t. (set t) \<subseteq> E}"
    have "?Tr'\<supseteq> Tr"
      by (meson Ball_Collect \<open>areTracesOver Tr E\<close> areTracesOver_def)
    moreover
    have "I \<V> ?Tr'" using \<open>isViewOn \<V> E\<close> 
      unfolding isViewOn_def I_def by auto
    ultimately
    have  "\<exists> Tr'. Tr' \<supseteq> Tr  \<and> I \<V> Tr'"
      by auto
  }
  thus ?thesis
    unfolding BSP_valid_def by auto
qed


(* \<rho>-Admissibility *)
type_synonym 'e Rho = "'e V_rec \<Rightarrow> 'e set"

definition 
Adm :: "'e V_rec \<Rightarrow> 'e Rho \<Rightarrow> ('e list) set \<Rightarrow> 'e list \<Rightarrow> 'e \<Rightarrow> bool"
where 
"Adm \<V> \<rho> Tr \<beta> e \<equiv>
   \<exists>\<gamma>. ((\<gamma> @ [e]) \<in> Tr \<and> \<gamma>\<upharpoonleft>(\<rho> \<V>) = \<beta>\<upharpoonleft>(\<rho> \<V>))"

(* Insertion of Admissible Confidential Events (IA) *)
definition IA :: "'e Rho \<Rightarrow> 'e BSP"
where
"IA \<rho> \<V> Tr \<equiv> 
  \<forall>\<alpha> \<beta>. \<forall>c\<in>C\<^bsub>\<V>\<^esub>. ((\<beta> @ \<alpha>) \<in> Tr \<and> \<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = [] \<and> (Adm \<V> \<rho> Tr \<beta> c)) 
    \<longrightarrow> (\<exists> \<alpha>' \<beta>'. ((\<beta>' @ [c] @ \<alpha>') \<in> Tr) \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> 
                    \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = [] \<and> \<beta>'\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<beta>\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>))" 

lemma BSP_valid_IA: "BSP_valid (IA \<rho>) "
proof -
  {  
    fix \<V> :: "('a V_rec)"
    fix Tr E
    assume "isViewOn \<V> E"
    and "areTracesOver Tr E"     
    let ?Tr'="{t. (set t) \<subseteq> E}"
    have "?Tr'\<supseteq> Tr"
      by (meson Ball_Collect \<open>areTracesOver Tr E\<close> areTracesOver_def)
    moreover
    have "IA \<rho> \<V> ?Tr'" using \<open>isViewOn \<V> E\<close>
      unfolding isViewOn_def IA_def by auto
    ultimately
    have  "\<exists> Tr'. Tr' \<supseteq> Tr  \<and> IA \<rho> \<V> Tr'"
      by auto
  }
  thus ?thesis
    unfolding BSP_valid_def by auto
qed


(* Backwards Strict Deletion of Confidential Events (BSD) *)
definition BSD :: "'e BSP"
where
"BSD \<V> Tr \<equiv> 
  \<forall>\<alpha> \<beta>. \<forall>c\<in>C\<^bsub>\<V>\<^esub>. ((\<beta> @ [c] @ \<alpha>) \<in> Tr \<and> \<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []) 
    \<longrightarrow> (\<exists>\<alpha>'. ((\<beta> @ \<alpha>') \<in> Tr \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []))"

lemma BSP_valid_BSD: "BSP_valid BSD"
proof -
  {  
    fix \<V>::"('e V_rec)" 
    fix Tr E
    assume "isViewOn \<V> E"
    and "areTracesOver Tr E"     
    let ?Tr'="{t. (set t) \<subseteq> E}"
    have "?Tr'\<supseteq> Tr"
      by (meson Ball_Collect \<open>areTracesOver Tr E\<close> areTracesOver_def)
    moreover
    have "BSD \<V> ?Tr'"
      unfolding BSD_def by auto
    ultimately
    have  "\<exists> Tr'. Tr' \<supseteq> Tr  \<and> BSD \<V> Tr'"
      by auto
  }
  thus ?thesis
    unfolding BSP_valid_def by auto
qed

(* Backwards Strict Insertion of Confidential Events (BSI) *)
definition BSI :: "'e BSP"
where
"BSI \<V> Tr \<equiv> 
  \<forall>\<alpha> \<beta>. \<forall>c\<in>C\<^bsub>\<V>\<^esub>. ((\<beta> @ \<alpha>) \<in> Tr \<and> \<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []) 
    \<longrightarrow> (\<exists>\<alpha>'. ((\<beta> @ [c] @ \<alpha>') \<in> Tr \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []))"

lemma BSP_valid_BSI: "BSP_valid BSI"
proof -
  {  
    fix \<V>::"('e V_rec)" 
    fix Tr E
    assume "isViewOn \<V> E"
    and "areTracesOver Tr E"     
    let ?Tr'="{t. (set t) \<subseteq> E}"
    have "?Tr'\<supseteq> Tr"
      by (meson Ball_Collect \<open>areTracesOver Tr E\<close> areTracesOver_def)
    moreover
    have "BSI \<V> ?Tr'" using \<open>isViewOn \<V> E\<close>
      unfolding isViewOn_def BSI_def by auto
    ultimately
    have  "\<exists> Tr'. Tr' \<supseteq> Tr  \<and> BSI \<V> Tr'"
      by auto
  }
  thus ?thesis
    unfolding BSP_valid_def by auto
qed

(* Backwards Strict Insertion of Admissible Confidential Events (BSIA) *)
definition BSIA :: "'e Rho \<Rightarrow> 'e BSP"
where 
"BSIA \<rho> \<V> Tr \<equiv> 
  \<forall>\<alpha> \<beta>. \<forall>c\<in>C\<^bsub>\<V>\<^esub>. ((\<beta> @ \<alpha>) \<in> Tr \<and> \<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = [] \<and> (Adm \<V> \<rho> Tr \<beta> c)) 
    \<longrightarrow> (\<exists>\<alpha>'. ((\<beta> @ [c] @ \<alpha>') \<in> Tr \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []))"

lemma BSP_valid_BSIA: "BSP_valid (BSIA \<rho>) "
proof -
  {  
    fix \<V> :: "('a V_rec)"
    fix Tr E
    assume "isViewOn \<V> E"
    and "areTracesOver Tr E"     
    let ?Tr'="{t. (set t) \<subseteq> E}"
    have "?Tr'\<supseteq> Tr"
      by (meson Ball_Collect \<open>areTracesOver Tr E\<close> areTracesOver_def)
    moreover
    have "BSIA \<rho> \<V> ?Tr'" using \<open>isViewOn \<V> E\<close>
      unfolding isViewOn_def BSIA_def by auto
    ultimately
    have  "\<exists> Tr'. Tr' \<supseteq> Tr  \<and> BSIA \<rho> \<V> Tr'"
      by auto
  }
  thus ?thesis
    unfolding BSP_valid_def by auto
qed

(* Forward Correctable BSPs *)
record 'e Gamma =
  Nabla :: "'e set"
  Delta :: "'e set"
  Upsilon :: "'e set"

(* syntax abbreviations for Gamma *)
abbreviation GammaNabla :: "'e Gamma \<Rightarrow> 'e set"
("\<nabla>\<^bsub>_\<^esub>" [100] 1000)
where
"\<nabla>\<^bsub>\<Gamma>\<^esub> \<equiv> (Nabla \<Gamma>)"

abbreviation GammaDelta :: "'e Gamma \<Rightarrow> 'e set"
("\<Delta>\<^bsub>_\<^esub>" [100] 1000)
where
"\<Delta>\<^bsub>\<Gamma>\<^esub> \<equiv> (Delta \<Gamma>)"

abbreviation GammaUpsilon :: "'e Gamma \<Rightarrow> 'e set"
("\<Upsilon>\<^bsub>_\<^esub>" [100] 1000)
where
"\<Upsilon>\<^bsub>\<Gamma>\<^esub> \<equiv> (Upsilon \<Gamma>)"


(* Forward Correctable Deletion of Confidential Events (FCD) *)
definition FCD :: "'e Gamma \<Rightarrow> 'e BSP"
where
"FCD \<Gamma> \<V> Tr \<equiv> 
  \<forall>\<alpha> \<beta>. \<forall>c\<in>(C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>). \<forall>v\<in>(V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>). 
    ((\<beta> @ [c,v] @ \<alpha>) \<in> Tr \<and> \<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []) 
      \<longrightarrow> (\<exists>\<alpha>'. \<exists>\<delta>'. (set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) 
                      \<and> ((\<beta> @ \<delta>' @ [v] @ \<alpha>') \<in> Tr  
                      \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []))"

lemma BSP_valid_FCD: "BSP_valid (FCD \<Gamma>)"
proof -
  {  
    fix \<V>::"('a V_rec)" 
    fix Tr E
    assume "isViewOn \<V> E"
    and "areTracesOver Tr E"     
    let ?Tr'="{t. (set t) \<subseteq> E}"
    have "?Tr'\<supseteq> Tr" 
      by (meson Ball_Collect \<open>areTracesOver Tr E\<close> areTracesOver_def)
    moreover
    have "FCD \<Gamma> \<V> ?Tr'"
      proof -
        {
          fix \<alpha> \<beta> c v
          assume  "c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>"
             and  "v \<in>V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>"
             and  "\<beta> @ [c ,v] @ \<alpha> \<in> ?Tr'"
             and  "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
          let ?\<alpha>'="\<alpha>" and ?\<delta>'="[]"  
          from \<open>\<beta> @ [c ,v] @ \<alpha> \<in> ?Tr'\<close> have "\<beta> @ ?\<delta>' @ [v] @ ?\<alpha>' \<in> ?Tr'"
            by auto 
          hence  "(set ?\<delta>') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> ((\<beta> @ ?\<delta>' @ [v] @ ?\<alpha>') \<in> ?Tr'  
                      \<and> ?\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> ?\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])"   
            using \<open>isViewOn \<V> E\<close> \<open>\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []\<close> 
            unfolding isViewOn_def \<open>\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []\<close> by auto
          hence "\<exists>\<alpha>'. \<exists>\<delta>'. (set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> ((\<beta> @ \<delta>' @ [v] @ \<alpha>') \<in> ?Tr'  
            \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])"
            by blast
        }
        thus ?thesis
          unfolding FCD_def by auto 
      qed
    ultimately
    have  "\<exists> Tr'. Tr' \<supseteq> Tr  \<and> FCD \<Gamma> \<V> Tr'"
      by auto
  }
  thus ?thesis
    unfolding BSP_valid_def by auto
qed

(* Forward Correctable Insertion of Confidential Events (FCI) *)
definition FCI :: "'e Gamma \<Rightarrow> 'e BSP"
where
"FCI \<Gamma> \<V> Tr \<equiv> 
  \<forall>\<alpha> \<beta>. \<forall>c\<in>(C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>). \<forall>v\<in>(V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>). 
    ((\<beta> @ [v] @ \<alpha>) \<in> Tr \<and> \<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []) 
      \<longrightarrow> (\<exists>\<alpha>'. \<exists>\<delta>'. (set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) 
                      \<and> ((\<beta> @ [c] @ \<delta>' @ [v] @ \<alpha>') \<in> Tr  
                      \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []))"

lemma BSP_valid_FCI: "BSP_valid (FCI \<Gamma>)"
proof -
  {  
    fix \<V>::"('a V_rec)" 
    fix Tr E
    assume "isViewOn \<V> E"
    and "areTracesOver Tr E"     
    let ?Tr'="{t. (set t) \<subseteq> E}"
    have "?Tr'\<supseteq> Tr" 
      by (meson Ball_Collect \<open>areTracesOver Tr E\<close> areTracesOver_def)
    moreover
    have "FCI \<Gamma> \<V> ?Tr'"
      proof -
        {
          fix \<alpha> \<beta> c v
          assume  "c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>"
             and  "v \<in>V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>"
             and  "\<beta> @ [v] @ \<alpha> \<in> ?Tr'"
             and  "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
          let ?\<alpha>'="\<alpha>" and ?\<delta>'="[]"  
          from \<open>c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>\<close> have" c \<in> E" 
            using \<open>isViewOn \<V> E\<close>
            unfolding isViewOn_def by auto
          with  \<open>\<beta> @ [v] @ \<alpha> \<in> ?Tr'\<close> have "\<beta> @ [c] @ ?\<delta>' @ [v] @ ?\<alpha>' \<in> ?Tr'" 
            by auto 
          hence  "(set ?\<delta>') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> ((\<beta> @ [c] @ ?\<delta>' @ [v] @ ?\<alpha>') \<in> ?Tr'  
                      \<and> ?\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> ?\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])"   
           using \<open>isViewOn \<V> E\<close> \<open>\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []\<close>  unfolding isViewOn_def \<open>\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []\<close> by auto
         hence 
           "\<exists>\<alpha>'. \<exists>\<delta>'. (set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> ((\<beta> @ [c] @ \<delta>' @ [v] @ \<alpha>') \<in> ?Tr'  
            \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])" 
            by blast
        }
        thus ?thesis
          unfolding FCI_def by auto 
      qed
    ultimately
    have  "\<exists> Tr'. Tr' \<supseteq> Tr  \<and> FCI \<Gamma> \<V> Tr'" 
      by auto
  }
  thus ?thesis 
    unfolding BSP_valid_def by auto
qed

(* Forward correctable Insertion of Admissible Confidential Events (FCIA) *)
definition FCIA :: "'e Rho \<Rightarrow> 'e Gamma \<Rightarrow> 'e BSP"
where
"FCIA \<rho> \<Gamma> \<V> Tr \<equiv> 
  \<forall>\<alpha> \<beta>. \<forall>c\<in>(C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>). \<forall>v\<in>(V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>).
    ((\<beta> @ [v] @ \<alpha>) \<in> Tr \<and> \<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = [] \<and> (Adm \<V> \<rho> Tr \<beta> c)) 
      \<longrightarrow> (\<exists>\<alpha>'. \<exists>\<delta>'. (set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) 
                      \<and> ((\<beta> @ [c] @ \<delta>' @ [v] @ \<alpha>') \<in> Tr  
                      \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []))"

lemma BSP_valid_FCIA: "BSP_valid (FCIA \<rho> \<Gamma>) "
proof -
  {  
    fix \<V> :: "('a V_rec)"
    fix Tr E
    assume "isViewOn \<V> E"
    and "areTracesOver Tr E"     
    let ?Tr'="{t. (set t) \<subseteq> E}"
    have "?Tr'\<supseteq> Tr"
      by (meson Ball_Collect \<open>areTracesOver Tr E\<close> areTracesOver_def)
    moreover
    have "FCIA \<rho> \<Gamma> \<V> ?Tr'"
    proof -
        {
          fix \<alpha> \<beta> c v
          assume  "c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>"
             and  "v \<in>V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>"
             and  "\<beta> @ [v] @ \<alpha> \<in> ?Tr'"
             and  "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
          let ?\<alpha>'="\<alpha>" and ?\<delta>'="[]"  
          from \<open>c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>\<close> have" c \<in> E" 
            using \<open>isViewOn \<V> E\<close> unfolding isViewOn_def by auto
          with  \<open>\<beta> @ [v] @ \<alpha> \<in> ?Tr'\<close> have "\<beta> @ [c] @ ?\<delta>' @ [v] @ ?\<alpha>' \<in> ?Tr'"
            by auto 
          hence  "(set ?\<delta>') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> ((\<beta> @ [c] @ ?\<delta>' @ [v] @ ?\<alpha>') \<in> ?Tr'  
                      \<and> ?\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> ?\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])"   
            using \<open>isViewOn \<V> E\<close> \<open>\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []\<close>  
            unfolding isViewOn_def \<open>\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []\<close> by auto
          hence 
            "\<exists>\<alpha>'. \<exists>\<delta>'. (set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> ((\<beta> @ [c] @ \<delta>' @ [v] @ \<alpha>') \<in> ?Tr'  
            \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])" 
            by blast
        }
        thus ?thesis
          unfolding FCIA_def by auto 
      qed
    ultimately
    have  "\<exists> Tr'. Tr' \<supseteq> Tr  \<and> FCIA \<rho> \<Gamma> \<V> Tr'"
      by auto
  }
  thus ?thesis
    unfolding BSP_valid_def by auto
qed

(* Strict Removal of Confidential Events (SR) *)
definition SR :: "'e BSP"
where
"SR \<V> Tr \<equiv> \<forall>\<tau>\<in>Tr. \<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) \<in> Tr"

lemma "BSP_valid SR"
proof -
  {  
    fix \<V>::"('e V_rec)" 
    fix Tr E
    assume "isViewOn \<V> E"
    and "areTracesOver Tr E"     
    let ?Tr'="{t. \<exists>\<tau> \<in> Tr. t=\<tau>\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)} \<union> Tr"
    have "?Tr'\<supseteq> Tr" 
      by blast
    moreover
    have "SR \<V> ?Tr'" unfolding SR_def 
      proof
        fix \<tau>
        assume "\<tau> \<in> ?Tr'"
        {
          from \<open>\<tau> \<in> ?Tr'\<close> have "(\<exists>t\<in>Tr. \<tau> = t \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)) \<or> \<tau> \<in> Tr"
            by auto
          hence "\<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) \<in> ?Tr'" 
            proof 
              assume "\<exists>t\<in>Tr. \<tau> = t \<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)" 
              hence "\<exists>t\<in>Tr. \<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)= t \<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)" 
                using projection_idempotent by metis
              thus ?thesis 
                by auto
            next
              assume "\<tau> \<in> Tr" 
              thus ?thesis 
                by auto
            qed  
        }  
        thus "\<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) \<in> ?Tr'" 
          by auto
      qed
    ultimately
    have "\<exists> Tr'. Tr' \<supseteq> Tr  \<and> SR \<V> Tr'" 
      by auto
  }
  thus ?thesis 
    unfolding BSP_valid_def by auto
qed

(* Strict Deletion of Confidential Events (SD) *)
definition SD :: "'e BSP"
where
"SD \<V> Tr \<equiv> 
  \<forall>\<alpha> \<beta>. \<forall>c\<in>C\<^bsub>\<V>\<^esub>. ((\<beta> @ [c] @ \<alpha>) \<in> Tr \<and> \<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []) \<longrightarrow> \<beta> @ \<alpha> \<in> Tr"

lemma "BSP_valid SD"
proof -
  {  
    fix \<V>::"('e V_rec)" 
    fix Tr E
    assume "isViewOn \<V> E"
    and "areTracesOver Tr E"     
    let ?Tr'="{t. (set t) \<subseteq> E}"
    have "?Tr'\<supseteq> Tr" by (meson Ball_Collect \<open>areTracesOver Tr E\<close> areTracesOver_def)
    moreover
    have "SD \<V> ?Tr'" unfolding SD_def by auto
    ultimately
    have  "\<exists> Tr'. Tr' \<supseteq> Tr  \<and> SD \<V> Tr'" by auto
  }
  thus ?thesis unfolding BSP_valid_def by auto
qed
 
(* Strict Insertion of Confidential Events (SI) *)
definition SI :: "'e BSP"
where
"SI \<V> Tr \<equiv> 
  \<forall>\<alpha> \<beta>. \<forall>c\<in>C\<^bsub>\<V>\<^esub>. ((\<beta> @ \<alpha>) \<in> Tr \<and> \<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []) \<longrightarrow> \<beta> @ [c] @ \<alpha> \<in> Tr"

lemma "BSP_valid SI"
proof -
  {  
    fix \<V>::"('a V_rec)" 
    fix Tr E
    assume "isViewOn \<V> E"
    and "areTracesOver Tr E"     
    let ?Tr'="{t. (set t) \<subseteq> E}"
    have "?Tr'\<supseteq> Tr"
      by (meson Ball_Collect \<open>areTracesOver Tr E\<close> areTracesOver_def)
    moreover
    have "SI \<V> ?Tr'" 
      using \<open>isViewOn \<V> E\<close> 
      unfolding isViewOn_def SI_def by auto
    ultimately
    have  "\<exists> Tr'. Tr' \<supseteq> Tr  \<and> SI \<V> Tr'" 
      by auto
  }
  thus ?thesis 
    unfolding BSP_valid_def by auto
qed

(* Strict Insertion of Admissible Confidential Events (SIA) *)
definition SIA :: "'e Rho \<Rightarrow> 'e BSP"
where
"SIA \<rho> \<V> Tr \<equiv> 
  \<forall>\<alpha> \<beta>. \<forall>c\<in>C\<^bsub>\<V>\<^esub>. ((\<beta> @ \<alpha>) \<in> Tr \<and> \<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [] \<and> (Adm \<V> \<rho> Tr \<beta> c)) 
    \<longrightarrow> (\<beta> @ [c] @ \<alpha>) \<in> Tr" 

lemma "BSP_valid (SIA \<rho>) "
proof -
  {  
    fix \<V> :: "('a V_rec)"
    fix Tr E
    assume "isViewOn \<V> E"
    and "areTracesOver Tr E"     
    let ?Tr'="{t. (set t) \<subseteq> E}"
    have "?Tr'\<supseteq> Tr" 
      by (meson Ball_Collect \<open>areTracesOver Tr E\<close> areTracesOver_def)
    moreover
    have "SIA \<rho> \<V> ?Tr'" 
      using \<open>isViewOn \<V> E\<close> 
      unfolding isViewOn_def SIA_def by auto
    ultimately
    have  "\<exists> Tr'. Tr' \<supseteq> Tr  \<and> SIA \<rho> \<V> Tr'" 
      by auto
  }
  thus ?thesis 
    unfolding BSP_valid_def by auto
qed

end
