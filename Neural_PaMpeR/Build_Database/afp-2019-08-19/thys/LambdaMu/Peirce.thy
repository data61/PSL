subsection\<open>Peirce\<close>

theory Peirce
  imports Types
begin
  
text\<open>As an example of our $\lambda\mu$ formalisation, we show show a
     $\lambda\mu$-term inhabiting Peirce's Law. The example is due to
     Parigot~\cite{DBLP:conf/lpar/Parigot92}.\<close>  
    
text\<open>Peirce's law: $((A \rightarrow B) \rightarrow A) \rightarrow A$.\<close>

lemma "\<Gamma>, \<Delta> \<turnstile>\<^sub>T \<lambda> (A\<rightarrow>B)\<rightarrow>A: (\<mu> A:(<0>((`0) \<degree> (\<lambda> A: (\<mu> B:(<1> (`0))))))) 
    : ((A\<rightarrow>B)\<rightarrow>A)\<rightarrow>A"
  by fastforce    
    
end
  
