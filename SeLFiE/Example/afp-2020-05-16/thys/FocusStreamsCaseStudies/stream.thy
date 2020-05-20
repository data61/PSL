(*<*)
(*
   Title:  Theory  stream.thy (FOCUS streams)
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*)
(*>*)

section "FOCUS streams: operators and lemmas"
 
theory stream
  imports ListExtras ArithExtras
begin

subsection \<open>Definition of the FOCUS stream types\<close>

\<comment> \<open>Finite timed FOCUS stream\<close>
type_synonym 'a fstream = "'a list list"

\<comment> \<open>Infinite timed FOCUS stream\<close>
type_synonym 'a istream = "nat \<Rightarrow> 'a list"

\<comment> \<open>Infinite untimed FOCUS stream\<close>
type_synonym 'a iustream = "nat \<Rightarrow> 'a"

\<comment> \<open>FOCUS stream (general)\<close>
datatype 'a stream = 
          FinT "'a fstream" \<comment> \<open>finite timed streams\<close>
        | FinU "'a list" \<comment> \<open>finite untimed streams\<close>
        | InfT "'a istream" \<comment> \<open>infinite timed streams\<close>
        | InfU "'a iustream" \<comment> \<open>infinite untimed streams\<close>


subsection \<open>Definitions of operators\<close>
  
\<comment> \<open>domain of an infinite untimed stream\<close>
definition
   infU_dom :: "natInf set"
 where
  "infU_dom \<equiv> {x. \<exists> i. x = (Fin i)} \<union> {\<infinity>}"
  
\<comment> \<open>domain of a finite untimed stream (using natural numbers enriched by Infinity)\<close>
definition
   finU_dom_natInf :: "'a list \<Rightarrow> natInf set"
   where
  "finU_dom_natInf s \<equiv> {x. \<exists> i. x = (Fin i) \<and> i < (length s)}"

\<comment> \<open>domain of a finite untimed stream\<close>
primrec
finU_dom :: "'a list \<Rightarrow> nat set"
where
  "finU_dom [] = {}" |
  "finU_dom (x#xs) = {length xs} \<union> (finU_dom xs)"

\<comment> \<open>range of a finite timed stream\<close>
primrec
  finT_range :: "'a fstream \<Rightarrow> 'a set"
where  
  "finT_range [] = {}" |
  "finT_range (x#xs) = (set x) \<union> finT_range xs"

\<comment> \<open>range of a finite untimed stream\<close>
definition
   finU_range :: "'a list \<Rightarrow> 'a set"
where
  "finU_range x \<equiv> set x"

\<comment> \<open>range of an infinite timed stream\<close>
definition
   infT_range :: "'a istream \<Rightarrow> 'a set"
where
  "infT_range s \<equiv> {y. \<exists> i::nat. y mem (s i)}"

\<comment> \<open>range of a finite untimed stream\<close>
definition
   infU_range :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a set"
where
  "infU_range s \<equiv> { y. \<exists> i::nat. y = (s i) }"

\<comment> \<open>range of a (general) stream\<close>
definition
   stream_range :: "'a stream \<Rightarrow> 'a set"
where
 "stream_range s \<equiv> case s of
       FinT x \<Rightarrow> finT_range x 
     | FinU x \<Rightarrow> finU_range x 
     | InfT x \<Rightarrow> infT_range x  
     | InfU x \<Rightarrow> infU_range x" 

\<comment> \<open>finite timed stream that consists of n empty time intervals\<close> 
primrec
   nticks :: "nat \<Rightarrow> 'a fstream"
where
  "nticks 0 = []" |
  "nticks (Suc i) = [] # (nticks i)"

\<comment> \<open>removing the first element from an infinite stream\<close>
\<comment> \<open>in the case of an untimed stream: removing the first data element\<close>  
\<comment> \<open>in the case of a timed stream: removing the first time interval\<close> 
definition
   inf_tl :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)"
where
  "inf_tl s \<equiv> (\<lambda> i. s (Suc i))"

\<comment> \<open>removing i first elements from an infinite stream s\<close>  
\<comment> \<open>in the case of an untimed stream: removing i first data elements\<close>  
\<comment> \<open>in the case of a timed stream: removing i first time intervals\<close> 
definition
   inf_drop :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)"
where
  "inf_drop i s \<equiv>  \<lambda> j. s (i+j)"  

\<comment> \<open>finding the first nonempty time interval in a finite timed stream\<close>
primrec
 fin_find1nonemp :: "'a fstream \<Rightarrow> 'a list"
where 
 "fin_find1nonemp [] = []" |
 "fin_find1nonemp (x#xs) =
    ( if x = []
      then fin_find1nonemp xs
      else x )"

\<comment> \<open>finding the first nonempty time interval in an infinite timed stream\<close>
definition 
  inf_find1nonemp :: "'a istream \<Rightarrow> 'a list"
where
 "inf_find1nonemp s 
  \<equiv>
  ( if (\<exists> i. s i \<noteq> [])
    then s (LEAST i. s i \<noteq> [])
    else [] )"

\<comment> \<open>finding the index of the first nonempty time interval in a finite timed stream\<close>
primrec
 fin_find1nonemp_index :: "'a fstream \<Rightarrow> nat"
where
 "fin_find1nonemp_index [] = 0" |
 "fin_find1nonemp_index (x#xs) =
    ( if x = []
      then Suc (fin_find1nonemp_index xs)
      else 0 )"

\<comment> \<open>finding the index of the first nonempty time interval in an infinite timed stream\<close>
definition
  inf_find1nonemp_index :: "'a istream \<Rightarrow> nat"
where
 "inf_find1nonemp_index s 
  \<equiv>
  ( if (\<exists> i. s i \<noteq> [])
    then (LEAST i. s i \<noteq> [])
    else 0 )"

\<comment> \<open>length of a finite timed stream: number of data elements in this stream\<close>  
primrec
  fin_length :: "'a fstream \<Rightarrow> nat"
where
  "fin_length [] = 0" |
  "fin_length (x#xs) = (length x) + (fin_length xs)"

\<comment> \<open>length of a (general) stream\<close>
definition
   stream_length :: "'a stream \<Rightarrow> natInf"
where
  "stream_length s \<equiv> 
      case s of 
                (FinT x) \<Rightarrow> Fin (fin_length x) 
              | (FinU x) \<Rightarrow> Fin (length x)  
              | (InfT x) \<Rightarrow> \<infinity> 
              | (InfU x) \<Rightarrow> \<infinity>"

\<comment> \<open>removing the first k elements from a finite (nonempty) timed stream\<close>
axiomatization
  fin_nth :: "'a fstream \<Rightarrow> nat \<Rightarrow> 'a"
where 
   fin_nth_Cons:
  "fin_nth (hds # tls) k = 
      ( if hds = []
        then fin_nth tls k
        else ( if (k < (length hds))
               then nth hds k
               else fin_nth tls (k - length hds) ))"

\<comment> \<open>removing i first data elements from an infinite timed stream s\<close>   
primrec
  inf_nth :: "'a istream \<Rightarrow> nat \<Rightarrow> 'a"
where 
 "inf_nth s 0 =  hd (s (LEAST i.(s i) \<noteq> []))"  |
 "inf_nth s (Suc k) = 
      ( if ((Suc k) < (length (s 0))) 
        then (nth (s 0) (Suc k))
        else ( if (s 0) = []
               then (inf_nth (inf_tl (inf_drop 
                     (LEAST i. (s i) \<noteq> []) s)) k )
               else inf_nth (inf_tl s) k ))"

\<comment> \<open>removing the first k data elements from a (general) stream\<close>
definition
    stream_nth :: "'a stream \<Rightarrow> nat \<Rightarrow> 'a"
where
   "stream_nth s k \<equiv> 
         case s of (FinT x) \<Rightarrow> fin_nth x k
                 | (FinU x) \<Rightarrow> nth x k
                 | (InfT x) \<Rightarrow> inf_nth x k 
                 | (InfU x) \<Rightarrow> x k"

\<comment> \<open>prefix of an infinite stream\<close>
primrec 
  inf_prefix :: "'a list \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> bool"
where   
  "inf_prefix [] s k = True" |
  "inf_prefix (x#xs) s k = ( (x = (s k)) \<and> (inf_prefix xs s (Suc k)) )"

\<comment> \<open>prefix of a finite stream\<close>
primrec 
  fin_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where   
  "fin_prefix [] s = True" |
  "fin_prefix (x#xs) s = 
     (if (s = []) 
      then False
      else (x = (hd s)) \<and> (fin_prefix xs s) )"

\<comment> \<open>prefix of a (general) stream\<close>
definition
   stream_prefix :: "'a stream \<Rightarrow> 'a stream \<Rightarrow> bool"
where
  "stream_prefix p s \<equiv>
   (case p of 
        (FinT x) \<Rightarrow> 
        (case s of (FinT y) \<Rightarrow>  (fin_prefix x y)
                 | (FinU y) \<Rightarrow> False
                 | (InfT y) \<Rightarrow> inf_prefix x y 0
                 | (InfU y) \<Rightarrow> False )
      | (FinU x) \<Rightarrow> 
        (case s of (FinT y) \<Rightarrow> False
                 | (FinU y) \<Rightarrow>  (fin_prefix x y)
                 | (InfT y) \<Rightarrow> False
                 | (InfU y) \<Rightarrow>  inf_prefix x y 0 )    
      | (InfT x) \<Rightarrow>
        (case s of (FinT y) \<Rightarrow> False
                 | (FinU y) \<Rightarrow> False
                 | (InfT y) \<Rightarrow> (\<forall> i. x i = y i)
                 | (InfU y) \<Rightarrow> False ) 
      | (InfU x) \<Rightarrow>
        (case s of (FinT y) \<Rightarrow> False
                 | (FinU y) \<Rightarrow> False
                 | (InfT y) \<Rightarrow> False
                 | (InfU y) \<Rightarrow> (\<forall> i. x i = y i) )  )"

\<comment> \<open>truncating a finite stream after the n-th element\<close>
primrec  
fin_truncate :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list"
where 
  "fin_truncate [] n = []" |
  "fin_truncate (x#xs) i = 
      (case i of 0 \<Rightarrow> [] 
         | (Suc n) \<Rightarrow> x # (fin_truncate xs n))"

\<comment> \<open>truncating a finite stream after the n-th element\<close>
\<comment> \<open>n is of type of natural numbers enriched by Infinity\<close>
definition
  fin_truncate_plus :: "'a list \<Rightarrow> natInf \<Rightarrow> 'a list"
 where
 "fin_truncate_plus s n 
  \<equiv> 
  case n of (Fin i) \<Rightarrow> fin_truncate s i
           |  \<infinity>     \<Rightarrow> s "

\<comment> \<open>truncating an infinite stream after the n-th element\<close>
primrec
  inf_truncate :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list"
where   
   "inf_truncate s 0 = [ s 0 ]" |
   "inf_truncate s (Suc k) = (inf_truncate s k) @ [s (Suc k)]"

\<comment> \<open>truncating an infinite stream after the n-th element\<close>
\<comment> \<open>n is of type of natural numbers enriched by Infinity\<close>
definition
  inf_truncate_plus :: "'a istream \<Rightarrow> natInf \<Rightarrow> 'a stream" 
 where
 "inf_truncate_plus s n 
  \<equiv> 
  case n of (Fin i) \<Rightarrow> FinT (inf_truncate s i)
           | \<infinity>     \<Rightarrow> InfT s"

\<comment> \<open>concatanation of a finite and an infinite stream\<close>
definition
    fin_inf_append :: 
        "'a list \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)"
where
"fin_inf_append us s \<equiv>  
 (\<lambda> i. ( if (i < (length us))
         then (nth us i)
         else s (i - (length us)) ))" 
 
\<comment> \<open>insuring that the infinite timed stream is time-synchronous\<close>
definition
   ts :: "'a istream \<Rightarrow> bool"
where
"ts s \<equiv>  \<forall> i. (length (s i) = 1)"

\<comment> \<open>insuring that each time interval of an infinite timed stream contains at most n data elements\<close>
definition
  msg :: "nat \<Rightarrow> 'a istream \<Rightarrow> bool"
where
 "msg n s \<equiv>  \<forall> t. length (s t) \<le> n"

\<comment> \<open>insuring that each time interval of a finite timed stream contains at most n data elements\<close>
primrec
  fin_msg :: "nat \<Rightarrow> 'a list list \<Rightarrow> bool"
where   
 "fin_msg n [] = True" |
 "fin_msg n (x#xs) = (((length x) \<le> n) \<and> (fin_msg n xs))" 

\<comment> \<open>making a finite timed stream to a finite untimed stream\<close>
definition
   fin_make_untimed :: "'a fstream  \<Rightarrow> 'a list"
where
  "fin_make_untimed x \<equiv>  concat x"

\<comment> \<open>making an infinite timed stream to an infinite untimed stream\<close>
\<comment> \<open>(auxiliary function)\<close>
primrec
  inf_make_untimed1 :: "'a istream \<Rightarrow> nat \<Rightarrow> 'a "
where 
inf_make_untimed1_0:
  "inf_make_untimed1 s 0 =  hd (s (LEAST i.(s i) \<noteq> []))"  |
inf_make_untimed1_Suc:
  "inf_make_untimed1 s (Suc k) =
    ( if ((Suc k) < length (s 0))
      then nth (s 0) (Suc k)
      else ( if (s 0) = []
             then (inf_make_untimed1 (inf_tl (inf_drop 
                          (LEAST i. \<forall> j. j < i \<longrightarrow> (s j) = [])
                           s)) k )
             else inf_make_untimed1 (inf_tl s) k ))"
             
\<comment> \<open>making an infinite timed stream to an infinite untimed stream\<close>
\<comment> \<open>(main function)\<close>
definition
   inf_make_untimed :: "'a istream \<Rightarrow> (nat \<Rightarrow> 'a) "
where
  "inf_make_untimed s
   \<equiv> 
   \<lambda> i. inf_make_untimed1 s i"

\<comment> \<open>making a (general) stream untimed\<close>
definition
    make_untimed :: "'a stream  \<Rightarrow> 'a stream"
where
   "make_untimed s \<equiv> 
      case s of (FinT x) \<Rightarrow> FinU (fin_make_untimed x)
              | (FinU x) \<Rightarrow> FinU x
              | (InfT x) \<Rightarrow> 
                (if (\<exists> i.\<forall> j. i < j \<longrightarrow> (x j) = [])
                 then FinU (fin_make_untimed (inf_truncate x 
                             (LEAST i.\<forall> j. i < j \<longrightarrow> (x j) = [])))
                 else InfU (inf_make_untimed x))
              | (InfU x) \<Rightarrow> InfU x"


\<comment> \<open>finding the index of the time interval that contains the k-th data element\<close>
\<comment> \<open>defined over a finite timed stream\<close>
primrec
  fin_tm :: "'a fstream \<Rightarrow> nat \<Rightarrow> nat"
where
  "fin_tm [] k = k" |
  "fin_tm (x#xs) k = 
    (if k = 0
     then 0
     else (if (k \<le> length x)
           then (Suc 0)
           else Suc(fin_tm xs (k - length x))))"

\<comment> \<open>auxiliary lemma for the definition of the truncate operator\<close>
lemma inf_tm_hint1:
  assumes "i2 = Suc i - length a"
      and "\<not> Suc i \<le> length a" 
      and "a \<noteq> []" 
  shows "i2 < Suc i"
using assms
by auto


\<comment> \<open>filtering a finite timed stream\<close>
definition
   finT_filter :: "'a set => 'a fstream => 'a fstream"   
where 
  "finT_filter m s \<equiv>  map (\<lambda> s. filter (\<lambda> y. y \<in> m) s) s"

\<comment> \<open>filtering an infinite timed stream\<close>
definition
   infT_filter :: "'a set => 'a istream => 'a istream"  
where
  "infT_filter m s \<equiv>  (\<lambda>i.( filter (\<lambda> x. x \<in> m) (s i)))"

\<comment> \<open>removing duplications from a finite timed stream\<close>
definition
   finT_remdups :: "'a fstream => 'a fstream"
where  
  "finT_remdups s \<equiv>  map (\<lambda> s. remdups s) s"

\<comment> \<open>removing duplications from an infinite timed stream\<close>
definition
   infT_remdups :: "'a istream => 'a istream"  
where
  "infT_remdups s \<equiv>  (\<lambda>i.( remdups (s i)))"

\<comment> \<open>removing duplications from a time interval of a stream\<close>
primrec
   fst_remdups :: "'a list \<Rightarrow> 'a list"
where
 "fst_remdups [] = []" |
 "fst_remdups (x#xs) = 
    (if xs = [] 
     then [x]
     else (if x = (hd xs)
           then fst_remdups xs
           else (x#xs)))"

\<comment> \<open>time interval operator\<close>
definition
  ti :: "'a fstream \<Rightarrow> nat \<Rightarrow> 'a list"
where
 "ti s i \<equiv>  
    (if s = []
     then []
     else (nth s i))"

\<comment> \<open>insuring that a sheaf of channels is correctly defined\<close>
definition
   CorrectSheaf :: "nat \<Rightarrow> bool"
where
  "CorrectSheaf n \<equiv> 0 < n"
 
\<comment> \<open>insuring that all channels in a sheaf are disjunct\<close>
\<comment> \<open>indices in the sheaf are represented using an extra specified set\<close>
definition
   inf_disjS :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a istream) \<Rightarrow> bool"
where
  "inf_disjS IdSet nS
   \<equiv>
   \<forall> (t::nat) i j. (i:IdSet) \<and> (j:IdSet) \<and>  
   ((nS i) t) \<noteq> []  \<longrightarrow> ((nS j) t) = []"  

\<comment> \<open>insuring that all channels in a sheaf are disjunct\<close>
\<comment> \<open>indices in the sheaf are represented using natural numbers\<close>
definition              
   inf_disj :: "nat \<Rightarrow> (nat \<Rightarrow> 'a istream) \<Rightarrow> bool"
where
  "inf_disj n nS
   \<equiv>
   \<forall> (t::nat) (i::nat) (j::nat). 
   i < n  \<and>  j < n \<and> i \<noteq> j \<and> ((nS i) t) \<noteq> []  \<longrightarrow> 
   ((nS j) t) = []"  

\<comment> \<open>taking the prefix of n data elements from a finite timed stream\<close>
\<comment> \<open>(defined over natural numbers)\<close>
fun fin_get_prefix  :: "('a fstream \<times> nat) \<Rightarrow> 'a fstream"
where
  "fin_get_prefix([], n) = []" |
  "fin_get_prefix(x#xs, i) = 
     ( if (length x) < i 
       then x # fin_get_prefix(xs, (i - (length x)))
       else [take i x] ) "

\<comment> \<open>taking the prefix of n data elements from a finite timed stream\<close>
\<comment> \<open>(defined over natural numbers enriched by Infinity)\<close>
definition
  fin_get_prefix_plus :: "'a fstream \<Rightarrow> natInf \<Rightarrow> 'a fstream"
where
 "fin_get_prefix_plus s n 
  \<equiv> 
  case n of (Fin i) \<Rightarrow> fin_get_prefix(s, i)
           | \<infinity>      \<Rightarrow> s "

\<comment> \<open>auxiliary lemmas\<close>
lemma length_inf_drop_hint1: 
  assumes "s k \<noteq> []"
  shows    "length (inf_drop k s 0) \<noteq> 0"
using assms
by (auto simp: inf_drop_def)

lemma length_inf_drop_hint2:
"(s 0 \<noteq> [] \<longrightarrow> length (inf_drop 0 s 0) < Suc i 
  \<longrightarrow> Suc i - length (inf_drop 0 s 0) < Suc i)"
  by (simp add: inf_drop_def list_length_hint1)

\<comment> \<open>taking the prefix of n data elements from an infinite timed stream\<close>
\<comment> \<open>(defined over natural numbers)\<close>
fun infT_get_prefix  :: "('a istream \<times> nat) \<Rightarrow> 'a fstream"
where   
  "infT_get_prefix(s, 0) = []"
|
  "infT_get_prefix(s, Suc i) = 
    ( if (s 0) = []
      then ( if (\<forall> i. s i = [])
             then []
             else (let 
                     k = (LEAST k. s k \<noteq> [] \<and> (\<forall>i. i < k \<longrightarrow> s i = []));
                     s2 = inf_drop (k+1) s
                   in (if (length (s k)=0) 
                       then [] 
                       else (if (length (s k) < (Suc i)) 
                             then s k # infT_get_prefix (s2,Suc i - length (s k))
                             else [take (Suc i) (s k)] )))
           )
      else 
        (if ((length (s 0)) < (Suc i)) 
         then (s 0) # infT_get_prefix( inf_drop 1 s, (Suc i) - (length (s 0)))
         else [take (Suc i) (s 0)] 
         )
     )"

\<comment> \<open>taking the prefix of n data elements from an infinite untimed stream\<close>
\<comment> \<open>(defined over natural numbers)\<close>
primrec
  infU_get_prefix  :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list"
where
  "infU_get_prefix s 0 = []" |
  "infU_get_prefix s (Suc i) 
         = (infU_get_prefix s i) @ [s i]"

\<comment> \<open>taking the prefix of n data elements from an infinite timed stream\<close>
\<comment> \<open>(defined over natural numbers enriched by Infinity)\<close>
definition
  infT_get_prefix_plus :: "'a istream \<Rightarrow> natInf \<Rightarrow> 'a stream"
where
"infT_get_prefix_plus s n 
  \<equiv> 
  case n of (Fin i) \<Rightarrow> FinT (infT_get_prefix(s, i)) 
           | \<infinity>     \<Rightarrow> InfT s"

\<comment> \<open>taking the prefix of n data elements from an infinite untimed stream\<close>
\<comment> \<open>(defined over natural numbers enriched by Infinity)\<close>
definition
  infU_get_prefix_plus :: "(nat \<Rightarrow> 'a) \<Rightarrow> natInf \<Rightarrow> 'a stream"
where
 "infU_get_prefix_plus s n 
  \<equiv> 
  case n of (Fin i) \<Rightarrow> FinU (infU_get_prefix s i) 
           | \<infinity>     \<Rightarrow> InfU s"

\<comment> \<open>taking the prefix of n data elements from an infinite stream\<close>
\<comment> \<open>(defined over natural numbers enriched by Infinity)\<close>
definition
  take_plus :: "natInf \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
 "take_plus n s 
  \<equiv> 
  case n of (Fin i) \<Rightarrow> (take i s) 
           | \<infinity>      \<Rightarrow> s"

\<comment> \<open>taking the prefix of n data elements from a (general) stream\<close>
\<comment> \<open>(defined over natural numbers enriched by Infinity)\<close>
definition 
   get_prefix :: "'a stream \<Rightarrow> natInf \<Rightarrow> 'a stream"
where
   "get_prefix s k \<equiv> 
        case s of  (FinT x) \<Rightarrow> FinT (fin_get_prefix_plus x k)
                 | (FinU x) \<Rightarrow> FinU (take_plus k x)
                 | (InfT x) \<Rightarrow> infT_get_prefix_plus x k
                 | (InfU x) \<Rightarrow> infU_get_prefix_plus x k"

\<comment> \<open>merging time intervals of two finite timed streams\<close>
primrec
   fin_merge_ti :: "'a fstream \<Rightarrow> 'a fstream \<Rightarrow> 'a fstream"
where
 "fin_merge_ti [] y = y" |
 "fin_merge_ti (x#xs) y = 
    ( case y of [] \<Rightarrow> (x#xs)
         | (z#zs) \<Rightarrow> (x@z) # (fin_merge_ti xs zs))"

\<comment> \<open>merging time intervals of two infinite timed streams\<close>
definition
 inf_merge_ti :: "'a istream \<Rightarrow> 'a istream \<Rightarrow> 'a istream"
where
 "inf_merge_ti x y 
  \<equiv> 
  \<lambda> i. (x i)@(y i)"

\<comment> \<open>the last time interval of a finite timed stream\<close>
primrec
  fin_last_ti :: "('a list) list \<Rightarrow> nat \<Rightarrow> 'a list"
where   
 "fin_last_ti s 0 = hd s" |
 "fin_last_ti s (Suc i) = 
     ( if s!(Suc i) \<noteq> []
       then s!(Suc i) 
       else fin_last_ti s i)"

\<comment> \<open>the last nonempty time interval of a finite timed stream\<close>
\<comment> \<open>(can be applied to the streams which time intervals are empty from some moment)\<close>
primrec
  inf_last_ti :: "'a istream \<Rightarrow> nat \<Rightarrow> 'a list"
where  
 "inf_last_ti s 0 = s 0" |
 "inf_last_ti s (Suc i) = 
     ( if s (Suc i) \<noteq> []
       then s (Suc i) 
       else inf_last_ti s i)"


subsection \<open>Properties of operators\<close>

lemma inf_last_ti_nonempty_k:
  assumes "inf_last_ti dt t \<noteq> []"
  shows    "inf_last_ti dt (t + k) \<noteq> []"
using assms  
by (induct k, auto)

lemma inf_last_ti_nonempty:
  assumes "s t \<noteq> []"
  shows    "inf_last_ti s (t + k) \<noteq> []"
using assms  
by (induct k, auto, induct t, auto)

lemma arith_sum_t2k:
"t + 2 + k = (Suc t) + (Suc k)" 
by arith 

lemma inf_last_ti_Suc2:
  assumes "dt (Suc t) \<noteq> [] \<or> dt (Suc (Suc t)) \<noteq> []"
  shows    "inf_last_ti dt (t + 2 + k) \<noteq> []"
proof (cases "dt (Suc t) \<noteq> []")
  assume a1:"dt (Suc t) \<noteq> []"
  from a1 have sg2:"inf_last_ti dt ((Suc t) + (Suc k)) \<noteq> []" 
    by (rule inf_last_ti_nonempty)
  from sg2 show ?thesis by (simp add: arith_sum_t2k) 
next
  assume a2:"\<not> dt (Suc t) \<noteq> []"
  from a2 and assms have sg1:"dt (Suc (Suc t)) \<noteq> []" by simp
  from sg1 have sg2:"inf_last_ti dt (Suc (Suc t) + k) \<noteq> []" 
    by (rule inf_last_ti_nonempty)
  from sg2 show ?thesis by auto
qed


subsubsection \<open>Lemmas for concatenation operator\<close>

lemma fin_length_append:
  "fin_length (x@y) = (fin_length x) + (fin_length y)"
by (induct x, auto)

lemma fin_append_Nil:  "fin_inf_append [] z = z"
by (simp add: fin_inf_append_def)

lemma correct_fin_inf_append1:
  assumes "s1 = fin_inf_append [x] s"
  shows    "s1 (Suc i) = s i"
using assms  
by (simp add: fin_inf_append_def)

lemma correct_fin_inf_append2:
  "fin_inf_append [x] s (Suc i) = s i"
by (simp add: fin_inf_append_def)

lemma fin_append_com_Nil1:
  "fin_inf_append [] (fin_inf_append y z) 
   = fin_inf_append ([] @ y) z"
by (simp add: fin_append_Nil)

lemma fin_append_com_Nil2:
  "fin_inf_append x (fin_inf_append [] z) 
  = fin_inf_append (x @ []) z"
by (simp add: fin_append_Nil)

lemma fin_append_com_i:
  "fin_inf_append x (fin_inf_append y z) i = fin_inf_append (x @ y) z i "
proof (cases x)
  assume Nil:"x = []"
  thus ?thesis by (simp add: fin_append_com_Nil1)
next
  fix a l assume Cons:"x = a # l"
  thus ?thesis
  proof (cases y)
    assume "y = []"
    thus ?thesis by (simp add: fin_append_com_Nil2)
  next
    fix aa la assume Cons2:"y = aa # la"
    show ?thesis 
    apply (simp add: fin_inf_append_def, auto, simp add: list_nth_append0)
    by (simp add: nth_append)
  qed
qed


subsubsection \<open>Lemmas for operators $ts$ and $msg$\<close>

lemma ts_msg1:
  assumes "ts p"
  shows    "msg 1 p"
using assms 
by (simp add: ts_def msg_def)

lemma ts_inf_tl:
  assumes "ts x"
  shows    "ts (inf_tl x)"
using assms  
by (simp add: ts_def inf_tl_def)

lemma ts_length_hint1:
 assumes "ts x"
 shows    "x i \<noteq> []"
proof - 
  from assms have sg1:"length (x i) = Suc 0"  by (simp add: ts_def)
  thus ?thesis by auto
qed

lemma ts_length_hint2:
 assumes "ts x"
 shows    "length (x i) = Suc (0::nat)"
using assms
by (simp add: ts_def)

lemma ts_Least_0:
  assumes "ts x"
  shows    "(LEAST i. (x i) \<noteq> [] ) = (0::nat)"
proof - 
  from assms have sg1:"x 0 \<noteq> []" by (rule ts_length_hint1)
  thus ?thesis 
  apply (simp add: Least_def)
  by auto
qed

lemma inf_tl_Suc: "inf_tl x i = x (Suc i)"
by (simp add: inf_tl_def) 

lemma ts_Least_Suc0:
  assumes "ts x"
  shows    "(LEAST i. x (Suc i) \<noteq> []) = 0"
proof -
  from assms have "x (Suc 0) \<noteq> []" by (simp add: ts_length_hint1)
  thus ?thesis by (simp add: Least_def, auto)
qed

lemma ts_inf_make_untimed_inf_tl:
  assumes "ts x"
  shows     "inf_make_untimed (inf_tl x) i = inf_make_untimed x (Suc i)"
using assms
apply (simp add: inf_make_untimed_def)
by (metis Suc_less_eq gr_implies_not0 ts_length_hint1 ts_length_hint2) 

lemma ts_inf_make_untimed1_inf_tl:
  assumes "ts x"
  shows    "inf_make_untimed1 (inf_tl x) i = inf_make_untimed1 x (Suc i)"
using assms
by (metis inf_make_untimed_def ts_inf_make_untimed_inf_tl)

lemma msg_nonempty1:
  assumes h1:"msg (Suc 0) a" 
         and h2:"a t = aa # l"
  shows "l = []"
proof - 
  from h1 have "length (a t) \<le> Suc 0" by (simp add: msg_def)
  from h2 and this show ?thesis by auto
qed

lemma msg_nonempty2:
  assumes h1:"msg (Suc 0) a" 
         and h2:"a t  \<noteq> []"
  shows "length (a t) = (Suc 0)"
proof - 
  from h1 have sg1:"length (a t) \<le> Suc 0" by (simp add: msg_def)
  from h2 have sg2:"length (a t) \<noteq> 0" by auto
  from sg1 and sg2 show ?thesis by arith 
qed


subsubsection \<open>Lemmas for $inf\_truncate$\<close>

lemma inf_truncate_nonempty:
  assumes "z i \<noteq> []"
  shows    "inf_truncate z i \<noteq> []"
proof (induct i)
    case 0
    from assms  show ?case by auto
  next
    case (Suc i)
     from assms show ?case by auto
qed


lemma concat_inf_truncate_nonempty:
  assumes  "z i \<noteq> []"
  shows      "concat (inf_truncate z i) \<noteq> []"
using assms
proof (induct i)
    case 0
    thus ?case by auto
  next
    case (Suc i)
    thus ?case by auto
qed
  
lemma concat_inf_truncate_nonempty_a:
  assumes "z i = [a]" 
  shows    "concat (inf_truncate z i) \<noteq> []"
using assms
by (metis concat_inf_truncate_nonempty list.distinct(1))

lemma concat_inf_truncate_nonempty_el:
  assumes "z i \<noteq> []" 
  shows    "concat (inf_truncate z i) \<noteq> []"
using assms
by (metis concat_inf_truncate_nonempty)

lemma inf_truncate_append:
  "(inf_truncate z i @ [z (Suc i)]) = inf_truncate z (Suc i)"
by (metis inf_truncate.simps(2))


subsubsection \<open>Lemmas for $fin\_make\_untimed$\<close> 

lemma fin_make_untimed_append:
  assumes "fin_make_untimed x \<noteq> []"
  shows    "fin_make_untimed (x @ y) \<noteq> []"
using assms by (simp add: fin_make_untimed_def)


lemma fin_make_untimed_inf_truncate_Nonempty:
  assumes "z k \<noteq> []"
         and "k \<le> i"
  shows "fin_make_untimed (inf_truncate z i) \<noteq> []"
using assms
  apply (simp add: fin_make_untimed_def)
  proof (induct i)
    case 0
    thus ?case  by auto
  next
    case (Suc i)
    thus ?case 
    proof cases
      assume "k \<le> i"
      from Suc and this show "\<exists>xs\<in>set (inf_truncate z (Suc i)). xs \<noteq> []"
        by auto
    next
      assume "\<not> k \<le> i"
      from Suc and this have "k = Suc i" by arith
      from Suc and this show "\<exists>xs\<in>set (inf_truncate z (Suc i)). xs \<noteq> []"
        by auto
     qed
qed

lemma last_fin_make_untimed_append:
  "last (fin_make_untimed (z @ [[a]])) = a"
by (simp add: fin_make_untimed_def)

lemma last_fin_make_untimed_inf_truncate:
  assumes "z i = [a]"
  shows    "last (fin_make_untimed (inf_truncate z i)) = a"
using assms
proof (induction i)
   case 0  thus ?case by (simp add: fin_make_untimed_def)
next
   case (Suc i)  thus ?case by (simp add: fin_make_untimed_def)
qed

lemma fin_make_untimed_append_empty:
  "fin_make_untimed (z @ [[]]) = fin_make_untimed z"
by (simp add: fin_make_untimed_def)

lemma fin_make_untimed_inf_truncate_append_a:
  "fin_make_untimed (inf_truncate z i @ [[a]]) ! 
  (length (fin_make_untimed (inf_truncate z i @ [[a]])) - Suc 0) = a"
by (simp add: fin_make_untimed_def)

lemma fin_make_untimed_inf_truncate_Nonempty_all:
  assumes "z k \<noteq> []" 
  shows    "\<forall> i. k \<le> i \<longrightarrow> fin_make_untimed (inf_truncate z i) \<noteq> []"
using assms by (simp add:  fin_make_untimed_inf_truncate_Nonempty)

lemma fin_make_untimed_inf_truncate_Nonempty_all0:
  assumes "z 0 \<noteq> []"
  shows    "\<forall> i. fin_make_untimed (inf_truncate z i) \<noteq> []"
using assms by (simp add: fin_make_untimed_inf_truncate_Nonempty)

lemma fin_make_untimed_inf_truncate_Nonempty_all0a:
  assumes "z 0 = [a]"
  shows    "\<forall> i. fin_make_untimed (inf_truncate z i) \<noteq> []"
using assms by (simp add: fin_make_untimed_inf_truncate_Nonempty_all0)

lemma fin_make_untimed_inf_truncate_Nonempty_all_app:
  assumes "z 0 = [a]" 
  shows    "\<forall> i. fin_make_untimed (inf_truncate z i @ [z (Suc i)]) \<noteq> []"
proof 
  fix i
  from assms have "fin_make_untimed (inf_truncate z i) \<noteq> []"
    by (simp add: fin_make_untimed_inf_truncate_Nonempty_all0a)
  from assms and this show 
    "fin_make_untimed (inf_truncate z i @ [z (Suc i)]) \<noteq> []"
    by (simp add: fin_make_untimed_append)
qed

lemma fin_make_untimed_nth_length:
  assumes "z i = [a]"
  shows 
  "fin_make_untimed (inf_truncate z i) ! 
     (length (fin_make_untimed (inf_truncate z i)) - Suc 0)
    = a"
proof - 
from assms have sg1:"last (fin_make_untimed (inf_truncate z i)) = a"
  by (simp add: last_fin_make_untimed_inf_truncate)
from assms have sg2:"concat (inf_truncate z i) \<noteq> []"
  by (rule concat_inf_truncate_nonempty_a)
from assms and sg1 and sg2 show ?thesis 
  by (simp add: fin_make_untimed_def last_nth_length)
qed


subsubsection \<open>Lemmas for $inf\_disj$ and $inf\_disjS$\<close> 

lemma inf_disj_index:
  assumes h1:"inf_disj n nS"
         and "nS k t \<noteq> []"
         and "k < n"
  shows  "(SOME i. i < n \<and>  nS i t \<noteq> []) = k"
proof - 
  from h1 have "\<forall> j. k < n \<and> j < n \<and> k \<noteq> j \<and> nS k t \<noteq> [] \<longrightarrow> nS j t = []"
    by (simp add: inf_disj_def, auto)
  from this and assms show ?thesis by auto
qed
 
lemma inf_disjS_index:
  assumes h1:"inf_disjS IdSet nS"
      and "k:IdSet"
      and "nS k t \<noteq> []"
  shows "(SOME i. (i:IdSet) \<and> nSend i t \<noteq> []) = k"
proof -
  from h1 have "\<forall> j. k \<in> IdSet \<and> j \<in> IdSet \<and> nS k t \<noteq> [] \<longrightarrow> nS j t = []"
    by (simp add: inf_disjS_def, auto)
  from this and assms show ?thesis by auto
qed

end
