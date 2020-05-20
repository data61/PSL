chapter \<open>Gap Buffer\<close>
section \<open>Challenge\<close>
text_raw \<open>{\upshape
A gap buffer is a data structure for the implementation of text editors,
which can efficiently move the cursor, as well add and delete characters.

The idea is simple: the editor's content is represented as a character array~$a$
of length~$n$,
which has a gap of unused entries $a[l], \ldots, a[r-1]$,
with respect to two indices $l \le r$.
The data it represents is composed as $a[0], \ldots, a[l-1], a[r], ..., a[n-1]$.

The current cursor position is at the left index $l$, and if we type a character, it is
written to $a[l]$ and $l$ is increased.
When the gap becomes empty, the array is enlarged and the data from $r$ is shifted to the right.

\paragraph{Implementation task.}
Implement the following four operations in the language of your tool:
Procedures \verb|left()| and \verb|right()| move the cursor by one character;
\verb|insert()| places a character at the beginning of the gap $a[l]$;
\verb|delete()| removes the character at $a[l]$ from the range of text.

\begin{multicols}{2}
\begin{lstlisting}[language=C,morekeywords={procedure,function,end,to,in,var,then,not,mod}]
procedure left()
    if l != 0 then
        l := l - 1
        r := r - 1
        a[r] := a[l]
    end-if
end-procedure


procedure right()
    // your task: similar to left()
    // but pay attention to the
    // order of statements
end-procedure
\end{lstlisting}

\begin{lstlisting}[language=C,morekeywords={procedure,function,end,to,in,var,then,not,mod}]
procedure insert(x: char)
    if l == r then
        // see extended task
        grow()
    end-if
    a[l] := x
    l := l + 1
end-procedure

procedure delete()
    if l != 0 then
        l := l - 1
    end-if
end-procedure
\end{lstlisting}
\end{multicols}

\paragraph{Verification task.}
Specify the intended behavior of the buffer in terms of a contiguous
representation of the editor content.
This can for example be based on strings, functional arrays, sequences, or lists.
Verify that the gap buffer implementation satisfies this specification,
and that every access to the array is within bounds.

\emph{Hint:}
For this task you may assume that \verb|insert()| has the
precondition $l < r$ and remove the call to \verb|grow()|.
Alternatively, assume a contract for \verb|grow()| that ensures
that this call does not change the abstract representation.

\paragraph{Extended verification task.}
Implement the operation \verb|grow()|, specify its behavior in a way that lets
you verify \verb|insert()| in a modular way
(i.e. not by referring to the implementation of \verb|grow()|),
and verify that \verb|grow()| satisfies this specification.

\emph{Hint}: You may assume that the allocation of the new buffer always succeeds.
If~your tool/language supports copying array ranges (such as
\verb|System.arraycopy()| in Java),
consider using these primitives instead of the loops in the
pseudo-code below.

\begin{lstlisting}[language=C,morekeywords={procedure,function,end,to,in,new,var,then,not,mod}]
procedure grow()
    var b := new char[a.length + K]

    // b[0..l] := a[0..l]
    for i = 0 to l - 1 do
        b[i] := a[i]
    end-for

    // b[r + K..] := a[r..]
    for i = r to a.length - 1 do
        b[i + K] := a[i]
    end-for

    r := r + K
    a := b
end-procedure
\end{lstlisting}

\paragraph{Resources}
\begin{itemize}
\item \url{https://en.wikipedia.org/wiki/Gap_buffer}
\item \url{http://scienceblogs.com/goodmath/2009/02/18/gap-buffers-or-why-bother-with-1}
\end{itemize}
}
\clearpage  
\<close>
section \<open>Solution\<close>
theory Challenge1
imports "lib/VTcomp"
begin


  text \<open>Fully fledged specification of textbuffer ADT,
    and its implementation by a gap buffer.
  \<close>
  subsection \<open>Abstract Specification\<close>

  text \<open>
    Initially, we modelled the abstract text as a cursor position and a list.
    However, this gives you an invariant on the abstract level. An isomorphic
    but invariant free formulation is a pair of lists, representing the text 
    before and after the cursor.
  \<close>

  datatype 'a textbuffer = BUF "'a list" "'a list"

  text \<open>The primitive operations are the empty textbuffer, 
    and to extract the text and the cursor position\<close>
  
  definition empty :: "'a textbuffer" where "empty = BUF [] []"  
  primrec get_text :: "'a textbuffer \<Rightarrow> 'a list" where "get_text (BUF a b) = a@b"
  primrec get_pos :: "'a textbuffer \<Rightarrow> nat" where "get_pos (BUF a b) = length a"

  text \<open>These are the operations that were specified in the challenge\<close>
  primrec move_left :: "'a textbuffer \<Rightarrow> 'a textbuffer" where
    "move_left (BUF a b) 
    = (if a\<noteq>[] then BUF (butlast a) (last a#b) else BUF a b)"
  primrec move_right :: "'a textbuffer \<Rightarrow> 'a textbuffer" where
    "move_right (BUF a b) 
    = (if b\<noteq>[] then BUF (a@[hd b]) (tl b) else BUF a b)"
  primrec insert :: "'a \<Rightarrow> 'a textbuffer \<Rightarrow> 'a textbuffer" where
    "insert x (BUF a b) = BUF (a@[x]) b"
  primrec delete :: "'a textbuffer \<Rightarrow> 'a textbuffer" where
    "delete (BUF a b) = BUF (butlast a) b" 
   \<comment> \<open>Note that @{lemma \<open>butlast [] = []\<close> by simp} in Isabelle\<close>

  text \<open>We can also assign them a meaning wrt position and text\<close>  
  
  lemma empty_pos[simp]: "get_pos empty = 0"
    unfolding empty_def by auto
  lemma empty_text[simp]: "get_text empty = []"
    unfolding empty_def by auto
  lemma move_left_pos[simp]: "get_pos (move_left b) = get_pos b - 1" 
    \<comment> \<open>Note that @{lemma \<open>0-(1::nat)=0\<close> by simp} in Isabelle\<close>
    by (cases b) auto
  lemma move_left_text[simp]: "get_text (move_left b) = get_text b"  
    by (cases b) auto

  lemma move_right_pos[simp]: 
    "get_pos (move_right b) = min (get_pos b+1) (length (get_text b))"
    by (cases b) auto
  lemma move_right_text[simp]: "get_text (move_right b) = get_text b"  
    by (cases b) auto
    
  lemma insert_pos[simp]: "get_pos (insert x b) = get_pos b + 1"  
    by (cases b) auto
  lemma insert_text: "get_text (insert x b) 
    = take (get_pos b) (get_text b)@x#drop (get_pos b) (get_text b)"    
    by (cases b) auto
    
  lemma delete_pos[simp]: "get_pos (delete b) = get_pos b - 1"  
    by (cases b) auto
  lemma delete_text: "get_text (delete b) 
    = take (get_pos b-1) (get_text b)@drop (get_pos b) (get_text b)"
    by (cases b) auto
  text \<open>For the zero case, we can prove a simpler (equivalent) lemma\<close>  
  lemma delete_text0[simp]: "get_pos b=0 \<Longrightarrow> get_text (delete b) = get_text b"  
    by (cases b) auto

  text \<open>To fully exploit the capabilities of our tool, we can (optionally) show 
    that the operations of a text buffer are parametric in its content. 
    Then, we can automatically refine the representation of the content.
  \<close>    
  definition [to_relAPP]:
    "textbuffer_rel A \<equiv> {(BUF a b, BUF a' b') | a b a' b'. 
                           (a,a')\<in>\<langle>A\<rangle>list_rel \<and> (b,b')\<in>\<langle>A\<rangle>list_rel}"

  lemma [param]: "(BUF,BUF) \<in> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>textbuffer_rel"
    by (auto simp: textbuffer_rel_def)        
  lemma [param]: "(rec_textbuffer,rec_textbuffer)
    \<in> (\<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel\<rightarrow>B) \<rightarrow> \<langle>A\<rangle>textbuffer_rel \<rightarrow> B"  
    by (auto simp: textbuffer_rel_def) parametricity


  context 
    notes[simp] = 
      empty_def get_text_def get_pos_def move_left_def move_right_def 
      insert_def delete_def conv_to_is_Nil
  begin      
    sepref_decl_op (no_def) empty :: "\<langle>A\<rangle>textbuffer_rel" .
    sepref_decl_op (no_def) get_text :: "\<langle>A\<rangle>textbuffer_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
    sepref_decl_op (no_def) get_pos :: "\<langle>A\<rangle>textbuffer_rel \<rightarrow> nat_rel" .
    sepref_decl_op (no_def) move_left :: "\<langle>A\<rangle>textbuffer_rel \<rightarrow> \<langle>A\<rangle>textbuffer_rel" .
    sepref_decl_op (no_def) move_right :: "\<langle>A\<rangle>textbuffer_rel \<rightarrow> \<langle>A\<rangle>textbuffer_rel" .
    sepref_decl_op (no_def) insert :: "A\<rightarrow>\<langle>A\<rangle>textbuffer_rel \<rightarrow> \<langle>A\<rangle>textbuffer_rel" .
    sepref_decl_op (no_def) delete :: "\<langle>A\<rangle>textbuffer_rel \<rightarrow> \<langle>A\<rangle>textbuffer_rel" .
  end    
  
  
subsection \<open>Refinement 1: List with Gap\<close>  
  
  subsection \<open>Implementation on List-Level\<close>  
  type_synonym 'a gap_buffer = "nat \<times> nat \<times> 'a list"

  subsubsection \<open>Abstraction Relation\<close>
  text \<open>Also called coupling relation sometimes. 
    Can be any relation, here we define it by an invariant and an 
    abstraction function.  \<close>
  definition "gap_\<alpha> \<equiv> \<lambda>(l,r,buf). BUF (take l buf) (drop r buf)"
  definition "gap_invar \<equiv> \<lambda>(l,r,buf). l\<le>r \<and> r\<le>length buf"
  abbreviation "gap_rel \<equiv> br gap_\<alpha> gap_invar"

  subsubsection \<open>Empty\<close>
      
  definition "empty1 \<equiv> RETURN (0,0,[])"
  lemma empty1_correct: "(empty1, RETURN empty) \<in> \<langle>gap_rel\<rangle>nres_rel"
    unfolding empty1_def empty_def
    apply refine_vcg
    by (auto simp: in_br_conv gap_\<alpha>_def gap_invar_def)
  
  subsubsection \<open>Left\<close>
  definition "move_left1 \<equiv> \<lambda>(l,r,buf). doN {
    if l\<noteq>0 then doN {
      ASSERT(r-1<length buf \<and> l-1<length buf);
      RETURN (l-1,r-1,buf[r-1:=buf!(l-1)])
    } else RETURN (l,r,buf)
  }"

  lemma move_left1_correct: 
    "(move_left1, RETURN o move_left) \<in> gap_rel \<rightarrow> \<langle>gap_rel\<rangle>nres_rel"
    apply clarsimp
    unfolding move_left1_def
    apply refine_vcg
    apply (auto 
      simp: in_br_conv gap_\<alpha>_def gap_invar_def move_left1_def 
      split: prod.splits)
    subgoal by (simp add: butlast_take)
    subgoal
      by (smt Cons_nth_drop_Suc One_nat_def Suc_pred diff_Suc_less 
        drop_update_cancel last_take_nth_conv le_trans length_list_update 
        less_le_trans neq0_conv nth_list_update_eq)
    done

  subsubsection \<open>Right\<close>        
  definition "move_right1 \<equiv> \<lambda>(l,r,buf). doN {
    if r<length buf then doN {
      ASSERT (l<length buf);
      RETURN (l+1,r+1,buf[l:=buf!r])
    } else RETURN (l,r,buf)
  }"
    
  lemma move_right1_correct: 
    "(move_right1,RETURN o move_right) \<in> gap_rel \<rightarrow> \<langle>gap_rel\<rangle>nres_rel"
    apply clarsimp
    unfolding move_right1_def
    apply refine_vcg
    unfolding gap_\<alpha>_def gap_invar_def
    apply (auto 
      simp: in_br_conv hd_drop_conv_nth take_update_last
      split: prod.split)
    by (simp add: drop_Suc tl_drop)
        
  subsubsection \<open>Insert and Grow\<close>
     
  definition "can_insert \<equiv> \<lambda>(l,r,buf). l<r"
  
  definition "grow1 K \<equiv> \<lambda>(l,r,buf). doN {
    let b = op_array_replicate (length buf + K) default;
    b \<leftarrow> mop_list_blit buf 0 b 0 l;
    b \<leftarrow> mop_list_blit buf r b (r+K) (length buf - r);
    RETURN (l,r+K,b)
  }"
  
  lemma grow1_correct[THEN SPEC_trans, refine_vcg]:
    assumes "gap_invar gb"
    shows "grow1 K gb  \<le> (SPEC (\<lambda>gb'. 
          gap_invar gb' 
        \<and> gap_\<alpha> gb' = gap_\<alpha> gb 
        \<and> (K>0 \<longrightarrow> can_insert gb')))"
    unfolding grow1_def
    apply refine_vcg    
    using assms
    unfolding gap_\<alpha>_def gap_invar_def can_insert_def
    apply clarsimp_all
    apply (auto simp: op_list_blit_def)
    by (simp add: min_def)  
  
  definition "insert1 x \<equiv> \<lambda>(l,r,buf). doN {
    (l,r,buf) \<leftarrow> 
      if (l=r) then grow1 (length buf+1) (l,r,buf) else RETURN (l,r,buf);
    ASSERT (l<length buf);
    RETURN (l+1,r,buf[l:=x])
  }" 
  
  lemma insert1_correct: 
    "(insert1,RETURN oo insert) \<in> Id \<rightarrow> gap_rel \<rightarrow> \<langle>gap_rel\<rangle>nres_rel"
    apply clarsimp
    unfolding insert1_def
    apply refine_vcg 
    unfolding insert_def gap_\<alpha>_def gap_invar_def can_insert_def
    apply (auto simp: in_br_conv take_update_last split: prod.split)
    done
  

  subsubsection \<open>Delete\<close>
  definition "delete1 
    \<equiv> \<lambda>(l,r,buf). if l>0 then RETURN (l-1,r,buf) else RETURN (l,r,buf)" 
  lemma delete1_correct: 
    "(delete1,RETURN o delete) \<in> gap_rel \<rightarrow> \<langle>gap_rel\<rangle>nres_rel"
    apply clarsimp
    unfolding delete1_def
    apply refine_vcg
    unfolding gap_\<alpha>_def gap_invar_def
    by (auto simp: in_br_conv butlast_take split: prod.split)
  
subsection \<open>Imperative Arrays and Executable Code\<close>  
  abbreviation "gap_impl_assn \<equiv> nat_assn \<times>\<^sub>a nat_assn \<times>\<^sub>a array_assn id_assn"  
  definition "gap_assn A 
    \<equiv> hr_comp (hr_comp gap_impl_assn gap_rel) (\<langle>the_pure A\<rangle>textbuffer_rel)"

  context 
    notes gap_assn_def[symmetric,fcomp_norm_unfold] 
  begin
    sepref_definition empty_impl 
      is "uncurry0 empty1" :: "unit_assn\<^sup>k\<rightarrow>\<^sub>agap_impl_assn"
      unfolding empty1_def array.fold_custom_empty
      by sepref
    sepref_decl_impl empty_impl: empty_impl.refine[FCOMP empty1_correct] .
  
    sepref_definition move_left_impl 
      is move_left1 :: "gap_impl_assn\<^sup>d\<rightarrow>\<^sub>agap_impl_assn"
      unfolding move_left1_def by sepref
    sepref_decl_impl move_left_impl: move_left_impl.refine[FCOMP move_left1_correct] .
  
    sepref_definition move_right_impl 
      is move_right1 :: "gap_impl_assn\<^sup>d\<rightarrow>\<^sub>agap_impl_assn"
      unfolding move_right1_def by sepref
    sepref_decl_impl move_right_impl: move_right_impl.refine[FCOMP move_right1_correct] .
    
    sepref_definition insert_impl 
      is "uncurry insert1" :: "id_assn\<^sup>k*\<^sub>agap_impl_assn\<^sup>d\<rightarrow>\<^sub>agap_impl_assn"
      unfolding insert1_def grow1_def by sepref 
      \<comment> \<open>We inline @{const grow1} here\<close>
    sepref_decl_impl insert_impl: insert_impl.refine[FCOMP insert1_correct] .
    
    sepref_definition delete_impl 
      is delete1 :: "gap_impl_assn\<^sup>d\<rightarrow>\<^sub>agap_impl_assn"
      unfolding delete1_def by sepref
    sepref_decl_impl delete_impl: delete_impl.refine[FCOMP delete1_correct] .

  end

  text \<open>
  The above setup generated the following refinement theorems, connecting the implementations
  with our abstract specification:
  @{thm [display]
    empty_impl_hnr move_left_impl_hnr move_right_impl_hnr insert_impl_hnr delete_impl_hnr
  }
  \<close>

  export_code move_left_impl move_right_impl insert_impl delete_impl  
    in SML_imp module_name Gap_Buffer
    in OCaml_imp module_name Gap_Buffer
    in Haskell module_name Gap_Buffer
    in Scala module_name Gap_Buffer
    

subsection \<open>Simple Client\<close>
    
  definition "client \<equiv> RETURN (fold (\<lambda>f. f) [
    insert (1::int),
    insert (2::int),
    insert (3::int),
    insert (5::int),
    move_left,
    insert (4::int),
    move_right,
    insert (6::int),
    delete
  ] empty)"

  lemma "client \<le> SPEC (\<lambda>r. get_text r=[1,2,3,4,5])"
    unfolding client_def
    by (simp add: delete_text insert_text)
  
  sepref_definition client_impl 
    is "uncurry0 client" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a gap_assn id_assn"
    unfolding client_def fold.simps id_def comp_def
    by sepref

  ML_val \<open>
    @{code client_impl} () 
  \<close>      
        
end
