(*
Title:  Allen's qualitative temporal calculus
Author:  Fadoua Ghourabi (fadouaghourabi@gmail.com)
Affiliation: Ochanomizu University, Japan
*)

section \<open>Time interval relations\<close>


theory allen

imports

  Main axioms 
  "HOL-Eisbach.Eisbach_Tools"


begin

section \<open>Basic relations\<close>

text\<open>We  define 7 binary relations  between time intervals. 
Relations e, m, b, ov, d, s and f stand for equal, meets, before, overlaps, during, starts and finishes, respectively.\<close>

class arelations = interval + 
 fixes 
  e::"('a\<times>'a) set" and
  m::"('a\<times>'a) set" and 
  b::"('a\<times>'a) set" and
  ov::"('a\<times>'a) set" and
  d::"('a\<times>'a) set" and
  s::"('a\<times>'a) set" and
  f::"('a\<times>'a) set"  
assumes
  e:"(p,q) \<in> e = (p = q)" and
  m:"(p,q) \<in> m = p\<parallel>q" and
  b:"(p,q) \<in> b = (\<exists>t::'a. p\<parallel>t \<and> t\<parallel>q)" and
  ov:"(p,q) \<in> ov = (\<exists>k l u v t::'a. 
                   (k\<parallel>p \<and> p\<parallel>u \<and> u\<parallel>v) \<and> (k\<parallel>l \<and> l\<parallel>q \<and> q\<parallel>v) \<and> (l\<parallel>t \<and> t\<parallel>u))" and
  s:"(p,q) \<in> s =  (\<exists>k u v::'a. k\<parallel>p \<and> p\<parallel>u \<and> u\<parallel>v \<and> k\<parallel>q \<and> q\<parallel>v)" and
  f:"(p,q) \<in> f = (\<exists>k l  u ::'a. k\<parallel>l \<and> l\<parallel>p \<and> p\<parallel>u \<and> k\<parallel>q \<and> q\<parallel>u)" and
  d:"(p,q) \<in> d = (\<exists>k l u v::'a. k\<parallel>l \<and> l\<parallel>p \<and> p\<parallel>u \<and>u\<parallel>v \<and> k\<parallel>q \<and> q\<parallel>v)" 
 

(** e compositions **)
subsection \<open>e-composition\<close>
text \<open>Relation e is the identity relation for composition.\<close>

lemma cer:
assumes  "r \<in> {e,m,b,ov,s,f,d,m^-1,b^-1,ov^-1,s^-1,f^-1,d^-1}" 
shows "e O r = r"
proof -
  { fix x y assume a:"(x,y) \<in> e O r" 
    then obtain z where "(x,z) \<in> e" and "(z,y) \<in> r" by auto
    from \<open>(x,z) \<in> e\<close> have "x = z" using e by auto
    with \<open>(z,y)\<in> r\<close> have "(x,y) \<in> r" by simp} note c1 = this
  
 { fix x y assume a:"(x,y) \<in>  r"
   have "(x,x) \<in> e" using e by auto
   with a have "(x,y) \<in> e O r" by blast} note c2 = this
 
 from c1 c2 show ?thesis by auto
qed

lemma cre:
assumes  "r \<in> {e,m,b,ov,s,f,d,m^-1,b^-1,ov^-1,s^-1,f^-1,d^-1}"
shows " r O e = r"
proof -
  { fix x y assume a:"(x,y) \<in> r O e" 
    then obtain z where "(x,z) \<in> r" and "(z,y) \<in> e" by auto
    from \<open>(z,y) \<in> e\<close> have "z = y" using e by auto
    with \<open>(x,z)\<in> r\<close> have "(x,y) \<in> r" by simp} note c1 = this
  
 { fix x y assume a:"(x,y) \<in>  r"
   have "(y,y) \<in> e" using e by auto
   with a have "(x,y) \<in> r O e" by blast} note c2 = this
 
 from c1 c2 show ?thesis by auto
qed

lemmas ceb = cer[of b]
lemmas cebi = cer[of "b^-1"]
lemmas cem = cer[of m]
lemmas cemi = cer[of "m^-1"]
lemmas cee = cer[of e]
lemmas ces = cer[of s]
lemmas cesi = cer[of "s^-1"]
lemmas cef = cer[of f]
lemmas cefi = cer[of "f^-1"]
lemmas ceov = cer[of ov]
lemmas ceovi = cer[of "ov^-1"]
lemmas ced = cer[of d]
lemmas cedi = cer[of "d^-1"]
lemmas cbe = cre[of b]
lemmas cbie = cre[of "b^-1"]
lemmas cme = cre[of m]
lemmas cmie = cre[of "m^-1"]
lemmas cse = cre[of s]
lemmas csie = cre[of "s^-1"]
lemmas cfe = cre[of f]
lemmas cfie = cre[of "f^-1"]
lemmas cove = cre[of ov]
lemmas covie = cre[of "ov^-1"]
lemmas cde = cre[of d]
lemmas cdie = cre[of "d^-1"]

(*******)

(* composition with single relation *)
subsection \<open>r-composition\<close>
text \<open>We prove compositions of the form $r_1 \circ r_2 \subseteq r$, where $r$ is a basic relation.\<close>

method (in arelations) r_compose uses r1 r2 r3 = ((auto, (subst (asm) r1 ), (subst (asm) r2), (subst r3)) ,  (meson M5exist_var))


lemma (in arelations) cbb:"b O b \<subseteq> b"
  by (r_compose r1:b r2:b r3:b)

lemma  (in arelations)  cbm:"b O m \<subseteq> b"
  by (r_compose r1:b r2:m r3:b)

lemma cbov:"b O ov \<subseteq> b"
  apply (auto simp:b ov)
  using M1 M5exist_var by blast

lemma cbfi:"b O f^-1 \<subseteq> b"
  apply (auto simp:b f)
  by (meson M1 M5exist_var)

lemma cbdi:"b O d^-1 \<subseteq> b"
  apply (auto simp: b d)
  by (meson M1 M5exist_var)
 
lemma cbs:"b O s \<subseteq> b"
  apply (auto simp: b s)
  by (meson M1 M5exist_var)

lemma cbsi:"b O s^-1 \<subseteq> b"
  apply (auto simp: b s)
  by (meson M1 M5exist_var)

lemma (in arelations) cmb:"m O b \<subseteq> b"
  by (r_compose r1:m r2:b r3:b)

lemma cmm:"m O m \<subseteq> b"
  by (auto simp: b m)

lemma cmov:"m O ov \<subseteq> b"
  apply (auto simp:b m ov)
  using M1 M5exist_var by blast

lemma cmfi:"m O f^-1 \<subseteq> b"
  apply (r_compose r1:m r2:f r3:b)
  by (meson M1)

lemma cmdi:"m O d^-1 \<subseteq> b"
  apply (auto simp add:m d b)
  using M1 by blast

lemma cms:"m O s \<subseteq> m"
  apply (auto simp add:m s)
  using M1 by auto

lemma cmsi:"m O s^-1 \<subseteq> m"
  apply (auto simp add:m s)
  using M1 by blast

lemma covb:"ov O b \<subseteq> b"
  apply (auto simp:ov b)
  using M1 M5exist_var by blast

lemma covm:"ov O m \<subseteq> b"
  apply (auto simp:ov m b)
  using M1 by blast

lemma covs:"ov O s \<subseteq> ov" 
proof
  fix p::"'a\<times>'a" assume "p \<in> ov O s" then obtain x y z where p:"p = (x,z)" and xyov:"(x,y)\<in> ov" and yzs:"(y,z) \<in> s" by auto
  from xyov obtain r u v t k where rx:"r\<parallel>x" and xu:"x\<parallel>u" and uv:"u\<parallel>v" and rt:"r\<parallel>t" and tk:"t\<parallel>k" and ty:"t\<parallel>y" and yv:"y\<parallel>v" and ku:"k\<parallel>u" using ov by blast
  from yzs obtain l1 l2 where yl1:"y\<parallel>l1" and l1l2:"l1\<parallel>l2" and zl2:"z\<parallel>l2" using s by blast
  from uv yl1 yv have "u\<parallel>l1" using M1 by blast
  with xu l1l2 obtain ul1 where xul1:"x\<parallel>ul1" and ul1l2:"ul1\<parallel>l2" using M5exist_var by blast
  from ku xu xul1 l1l2 have kul1:"k\<parallel>ul1" using M1 by blast
  from ty yzs have "t\<parallel>z" using s M1 by blast
  with rx rt xul1 ul1l2 zl2 tk kul1 have "(x,z) \<in> ov" using ov by blast
  with p show "p \<in> ov" by simp
qed

lemma cfib:"f^-1 O b \<subseteq> b" 
  apply (auto simp:f b)
  using M1 by blast

lemma cfim:"f^-1 O m \<subseteq> m"
  apply (auto simp:f m)
  using M1 by auto

lemma cfiov:"f^-1 O ov \<subseteq> ov" 
proof 
    fix p::"'a\<times>'a" assume "p \<in> f^-1 O ov" then obtain x y z where p:"p = (x,z)" and xyfi:"(x,y)\<in> f^-1" and yzov:"(y,z) \<in> ov" by auto
    from xyfi yzov obtain t' r u   where tpr:"t'\<parallel>r" and ry:"r\<parallel>y" and yu:"y\<parallel>u" and tpx:"t'\<parallel>x" and xu:"x\<parallel>u"  using f  by blast
    from yzov  ry  obtain v k t u' where yup:"y\<parallel>u'" and upv:"u'\<parallel>v" and rk:"r\<parallel>k" and kz:"k\<parallel>z" and zv:"z\<parallel>v" and kt:"k\<parallel>t" and tup:"t\<parallel>u'" 
    using ov using M1 by blast
    from yu xu yup have xup:"x\<parallel>u'" using M1 by blast
    from tpr rk kt obtain r' where tprp:"t'\<parallel>r'" and rpt:"r'\<parallel>t" using M5exist_var by blast
    from kt rpt kz have rpz:"r'\<parallel>z" using M1 by blast
    from tprp rpz rpt tpx xup zv upv tup have "(x,z) \<in> ov" using ov by blast
    with p show "p \<in> ov" by simp
qed

lemma cfifi:"f^-1 O f^-1 \<subseteq> f^-1"
proof
  fix x::"'a\<times>'a" assume "x \<in> f^-1 O f^-1" then obtain p q z where x:"x = (p, q)" and "(p,z) \<in> f^-1" and "(z,q) \<in> f^-1" by auto
  from \<open>(p,z) \<in> f^-1\<close> obtain k l u  where kp:"k\<parallel>p" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and pu:"p\<parallel>u" and zu:"z\<parallel>u"  using f  by blast
  from \<open>(z,q) \<in> f^-1\<close> obtain k' u' l' where kpz:"k'\<parallel>z" and kplp:"k'\<parallel>l'" and lpq:"l'\<parallel>q" and qup:"q\<parallel>u'" and zup:"z\<parallel>u'"  using f  by blast
  from zu zup pu have "p\<parallel>u'" using M1 by blast
  from lz kpz kplp have "l\<parallel>l'" using M1 by blast
  with kl lpq obtain ll where "k\<parallel>ll" and "ll\<parallel>q" using M5exist_var by blast
  with kp \<open>p\<parallel>u'\<close> qup show "x \<in> f^-1" using x f by blast
qed

lemma cfidi:"f^-1 O d^-1 \<subseteq> d^-1"
proof
  fix x::"'a\<times>'a" assume "x : f^-1 O d^-1" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> f^-1" and "(z,q) \<in> d^-1" by auto
  then obtain k l u where kp:"k \<parallel> p" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and pu:"p \<parallel>u" and  zu:"z\<parallel>u" using f  by blast
  obtain k' l' u' v' where kpz:"k' \<parallel>z" and kplp:"k' \<parallel>l'" and lpq:"l' \<parallel>q" and  qup:"q \<parallel>u'" and  upvp:"u'\<parallel>v'" and zvp:"z\<parallel>v'" using d \<open>(z,q)\<in>d^-1\<close> by blast
  from lz kpz kplp have "l\<parallel>l'" using M1 by blast
  with kl lpq obtain ll where "k\<parallel>ll" and "ll\<parallel>q" using M5exist_var by blast
  moreover from zu zvp upvp have "u' \<parallel> u " using M1 by blast
  ultimately show "x \<in> d^-1" using x kp pu qup d  by blast
qed

lemma cfis:"f^-1 O s \<subseteq> ov"
proof
   fix x::"'a\<times>'a" assume "x \<in> f^-1 O s" then obtain p q z where x:"x = (p,q)" and "(p,z)\<in> f^-1" and "(z,q) \<in> s" by auto
   from \<open>(p,z)\<in> f^-1\<close> obtain k l u where kp:"k\<parallel>p" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and pu:"p\<parallel>u" and zu:"z\<parallel>u" using f by blast
   from \<open>(z,q)\<in> s\<close> obtain k' u' v' where kpz:"k'\<parallel>z" and kpq:"k'\<parallel>q" and zup:"z\<parallel>u'" and upvp:"u'\<parallel>v'" and qvp:"q\<parallel>v'" using s M1 by blast
   from pu zu zup have pup:"p\<parallel>u'" using M1 by blast
   moreover from lz kpz kpq have lq:"l\<parallel>q" using M1 by blast
   ultimately show "x \<in> ov" using x lz zup kp kl upvp upvp ov qvp by blast
qed

lemma cfisi:"f^-1 O s^-1 \<subseteq> d^-1"
proof
  fix x::"'a\<times>'a" assume "x \<in> f^-1 O s^-1" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> f^-1" and "(z,q) \<in> s^-1" by auto
  then obtain k l u where kp:"k \<parallel> p" and kl:"k\<parallel>l" and lz:"l\<parallel>z"  and pu:"p \<parallel>u" and  zu:"z\<parallel>u" using f  by blast
  obtain k' u' v' where kpz:"k' \<parallel>z" and kpq:"k' \<parallel>q" and qup:"q \<parallel>u'" and  upvp:"u'\<parallel>v'" and  zvp:"z\<parallel>v'" using s \<open>(z,q): s^-1\<close> by blast
  from zu zvp upvp have "u'\<parallel>u" using M1 by blast
  moreover from lz kpz kpq have "l \<parallel>q " using M1 by blast
  ultimately show "x \<in> d^-1" using x d kl kp qup  pu  by blast
qed

lemma cdifi:"d^-1 O f^-1 \<subseteq> d^-1"
proof
  fix x::"'a\<times>'a" assume "x : d^-1 O f^-1" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> d^-1" and "(z,q) \<in> f^-1" by auto
  then obtain k l u v  where kp:"k \<parallel> p" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and zu:"z \<parallel>u" and uv:"u\<parallel>v" and pv:"p\<parallel>v" using d  by blast
  obtain k' l' u' where kpz:"k' \<parallel>z" and kplp:"k' \<parallel>l'" and lpq:"l' \<parallel>q" and  qup:"q \<parallel>u'" and zup:"z\<parallel>u'" using f \<open>(z,q): f^-1\<close> by blast
  from lz kpz kplp  have "l\<parallel>l'" using M1 by blast
  with kl lpq obtain ll where "k\<parallel>ll" and "ll\<parallel>q" using M5exist_var by blast
  moreover from zu qup zup have "q \<parallel> u " using M1 by blast
  ultimately show "x \<in> d^-1" using x d kp uv pv  by blast
qed

lemma cdidi:"d^-1 O d^-1 \<subseteq> d^-1" 
proof
  fix x::"'a\<times>'a" assume "x : d^-1 O d^-1" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> d^-1" and "(z,q) \<in> d^-1" by auto
  then obtain k l u v where kp:"k \<parallel> p" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and zu:"z \<parallel>u" and uv:"u\<parallel>v" and pv:"p\<parallel>v" using d  by blast
  obtain k' l' u' v' where kpz:"k' \<parallel>z" and kplp:"k' \<parallel>l'" and lpq:"l' \<parallel>q" and  qup:"q \<parallel>u'" and upvp:"u' \<parallel>v'" and zvp:"z \<parallel>v'" using d \<open>(z,q): d^-1\<close> by blast
  from lz kpz kplp  have "l\<parallel>l'" using M1 by blast
  with kl lpq obtain ll where "k\<parallel>ll" and "ll\<parallel>q" using M5exist_var by blast
  moreover from zvp zu upvp have "u' \<parallel> u " using M1 by blast
  moreover with qup uv obtain uu where "q\<parallel>uu" and "uu\<parallel>v" using M5exist_var  by blast
  ultimately show "x \<in> d^-1" using x d kp pv   by blast
qed

lemma cdisi:"d^-1 O s^-1 \<subseteq> d^-1"
proof
  fix x::"'a\<times>'a" assume "x : d^-1 O s^-1" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> d^-1" and "(z,q) \<in> s^-1" by auto
  then obtain k l  u v where kp:"k \<parallel>p" and kl:"k\<parallel>l"  and lz:"l\<parallel>z" and zu:"z\<parallel>u" and uv:"u\<parallel>v" and pv:"p\<parallel>v" using d by blast
  obtain k' u' v' where kpz:"k' \<parallel>z" and kpq:"k' \<parallel>q" and  qup:"q \<parallel>u'" and upvp:"u' \<parallel>v'" and zvp:"z \<parallel>v'" using s \<open>(z,q): s^-1\<close> by blast
  from upvp zvp zu have "u'\<parallel>u" using M1 by blast
  with qup uv obtain uu where "q\<parallel>uu" and "uu\<parallel>v" using M5exist_var by blast
  moreover from kpz lz kpq have "l \<parallel>q " using M1 by blast
  ultimately show "x \<in> d^-1" using x d kp kl pv  by blast
qed

lemma csb:"s O b \<subseteq> b"
apply (auto simp:s b)
using M1 M5exist_var by blast

lemma csm:"s O m \<subseteq> b"
apply (auto simp:s m b)
using M1 by blast

lemma css:"s O s \<subseteq> s"
proof
  fix x::"'a\<times>'a" assume "x \<in> s O s" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> s" and "(z,q) \<in> s" by auto
  from \<open>(p,z) \<in> s\<close> obtain k u v where kp:"k\<parallel>p" and kz:"k\<parallel>z" and pu:"p\<parallel>u" and uv:"u\<parallel>v" and zv:"z\<parallel>v" using s by blast
  from \<open>(z,q) \<in> s\<close> obtain k' u' v' where kpq:"k'\<parallel>q" and kpz:"k'\<parallel>z" and zup:"z\<parallel>u'" and upvp:"u'\<parallel>v'" and qvp:"q\<parallel>v'" using s by blast
  from kp kpz kz have "k'\<parallel>p" using M1 by blast
  moreover from uv zup zv have "u\<parallel>u'" using M1 by blast
  moreover with pu upvp obtain uu where "p\<parallel>uu" and "uu\<parallel>v'" using M5exist_var by blast
  ultimately show "x \<in> s" using x s kpq qvp  by blast
qed

lemma csifi:"s^-1 O f^-1 \<subseteq> d^-1"
proof
  fix x::"'a\<times>'a" assume "x : s^-1 O f^-1" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> s^-1" and "(z,q) \<in> f^-1" by auto
  then obtain k u v where kp:"k \<parallel> p" and kz:"k\<parallel>z" and zu:"z \<parallel>u" and uv:"u\<parallel>v" and pv:"p\<parallel>v" using s  by blast
  obtain k' l' u' where kpz:"k' \<parallel>z" and kplp:"k' \<parallel>l'" and lpq:"l' \<parallel>q"  and zup:"z\<parallel>u'" and qup:"q\<parallel>u'" using f \<open>(z,q): f^-1\<close> by blast
  from kz kpz kplp have "k\<parallel>l'" using M1 by blast
  moreover from qup zup zu have "q \<parallel> u " using M1 by blast
  ultimately show "x \<in> d^-1" using x d kp lpq pv uv by blast
qed

lemma csidi:"s^-1 O d^-1 \<subseteq> d^-1"
proof
  fix x::"'a\<times>'a" assume "x : s^-1 O d^-1" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> s^-1" and "(z,q) \<in> d^-1" by auto
  then obtain k u v where kp:"k \<parallel> p" and kz:"k\<parallel>z"  and zu:"z \<parallel>u" and uv:"u\<parallel>v" and pv:"p\<parallel>v" using s  by blast
  obtain k' l' u' v' where kpz:"k' \<parallel>z" and kplp:"k' \<parallel>l'" and lpq:"l'\<parallel>q" and qup:"q \<parallel>u'" and upvp:"u' \<parallel>v'" and zvp:"z\<parallel>v'" using d \<open>(z,q): d^-1\<close> by blast
  from zvp upvp zu have "u'\<parallel>u" using M1 by blast
  with qup uv obtain uu where "q\<parallel>uu" and "uu\<parallel>v" using M5exist_var by blast
  moreover from kz kpz kplp have "k \<parallel>l' " using M1 by blast
  ultimately show "x \<in> d^-1" using x d kp lpq pv  by blast
qed

lemma cdb:"d O b \<subseteq> b"
apply (auto simp:d b)
using M1 M5exist_var by blast

lemma cdm:"d O m \<subseteq> b"
apply (auto simp:d m b)
using M1 by blast

lemma cfb:"f O b \<subseteq> b"
apply (auto simp:f b)
using M1 by blast

lemma cfm:"f O m \<subseteq> m"
proof 
  fix x::"'a\<times>'a" assume "x \<in> f O m" then obtain p q z where x:"x = (p,q)" and 1:"(p,z) \<in> f" and 2:"(z,q) \<in> m" by auto
  from 1 obtain u where pu:"p\<parallel>u" and zu:"z\<parallel>u" using f by auto
  with 2   have "(p,q) \<in> m" using M1 m by blast
  thus "x\<in> m" using x by auto
qed


(* ========= $\alpah_1$ compositions ============ *)
subsection \<open>$\alpha$-composition\<close>
text \<open>We prove compositions of the form $r_1 \circ r_2 \subseteq s \cup ov \cup d$.\<close>


lemma (in arelations) cmd:"m O d \<subseteq> s \<union> ov \<union> d"
proof 
  fix x::"'a\<times>'a" assume a:"x \<in> m O d" then obtain p q z where x:"x =(p,q)" and 1:"(p,z) \<in> m" and 2:"(z,q) \<in> d" by auto
  then obtain k l u v  where pz:"p\<parallel>z" and kq:"k\<parallel>q" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and zu:"z\<parallel>u" and uv:"u\<parallel>v" and qv:"q\<parallel>v" using m d by blast
  obtain k' where kpp:"k'\<parallel>p" using M3 meets_wd pz by blast
  from pz zu uv obtain zu where pzu:"p\<parallel>zu" and zuv:"zu\<parallel>v" using M5exist_var  by blast
  from kpp kq have "k'\<parallel>q \<oplus> ((\<exists>t. k'\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast 
  then have "(?A\<and>\<not>?B\<and>\<not>?C)\<or>(\<not>?A\<and>?B\<and>\<not>?C)\<or>(\<not>?A\<and>\<not>?B\<and>?C)"  using local.meets_atrans xor_distr_L[of ?A ?B ?C]  by blast
  thus "x \<in> s \<union> ov \<union> d"    
  proof (elim disjE)
    {assume "(?A\<and>\<not>?B\<and>\<not>?C)" then have "?A" by simp 
     then have "(p,q) \<in> s" using  s qv kpp pzu zuv by blast
     thus ?thesis using x by simp }
    next
    {assume "(\<not>?A\<and>?B\<and>\<not>?C)" then have "?B" by simp
     then obtain t where kpt:"k'\<parallel>t" and tq:"t\<parallel>q" by auto
     moreover from kq kl tq have "t\<parallel>l" using M1 by blast
     moreover from lz pz pzu have "l\<parallel>zu" using M1 by blast
     ultimately have "(p,q) \<in> ov" using ov kpp qv pzu zuv by blast
     thus ?thesis using x by simp}
    next
    {assume "(\<not>?A\<and>\<not>?B\<and>?C)" then have "?C" by simp
     then obtain t where kt:"k\<parallel>t" and tp:"t\<parallel>p" by auto
     with kq pzu zuv qv  have "(p,q)\<in>d" using d by blast
     thus ?thesis using x by simp}
  qed
qed

lemma (in arelations) cmf:"m O f \<subseteq> s \<union> ov \<union> d"
proof
  fix x::"'a\<times>'a" assume a:"x \<in> m O f" then obtain p q z where x:"x =(p,q)" and 1:"(p,z) \<in> m" and 2:"(z,q) \<in> f" by auto
  then obtain k l u   where pz:"p\<parallel>z" and kq:"k\<parallel>q" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and zu:"z\<parallel>u" and qu:"q\<parallel>u" using m f by blast
  obtain k' where kpp:"k'\<parallel>p" using M3 meets_wd pz by blast
  from kpp kq have "k'\<parallel>q \<oplus> ((\<exists>t. k'\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast 
  then have "(?A\<and>\<not>?B\<and>\<not>?C)\<or>(\<not>?A\<and>?B\<and>\<not>?C)\<or>(\<not>?A\<and>\<not>?B\<and>?C)" using local.meets_atrans xor_distr_L[of ?A ?B ?C]  by blast
  thus "x \<in> s \<union> ov \<union> d"    
  proof (elim disjE)
    {assume "(?A\<and>\<not>?B\<and>\<not>?C)" then have "?A" by simp 
     then have "(p,q) \<in> s" using  s qu kpp pz zu by blast
     thus ?thesis using x by simp }
    next
    {assume "(\<not>?A\<and>?B\<and>\<not>?C)" then have "?B" by simp
     then obtain t where kpt:"k'\<parallel>t" and tq:"t\<parallel>q" by auto
     moreover from kq kl tq have "t\<parallel>l" using M1 by blast 
     moreover from lz pz pz have "l\<parallel>z" using M1 by blast
     ultimately have "(p,q) \<in> ov" using ov kpp qu pz zu by blast
     thus ?thesis using x by simp}
    next
    {assume "(\<not>?A\<and>\<not>?B\<and>?C)" then have "?C" by simp
     then obtain t where kt:"k\<parallel>t" and tp:"t\<parallel>p" by auto
     with kq pz zu qu  have "(p,q)\<in>d" using d by blast
     thus ?thesis using x by simp}
  qed
qed

lemma cmovi:"m O ov^-1  \<subseteq> s \<union> ov \<union> d"
proof 
  fix x::"'a\<times>'a" assume a:"x \<in> m O ov^-1" then obtain p q z where x:"x =(p,q)" and 1:"(p,z) \<in> m" and 2:"(z,q) \<in> ov^-1" by auto
  then obtain k l c u v  where pz:"p\<parallel>z" and kq:"k\<parallel>q" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and qu:"q\<parallel>u" and uv:"u\<parallel>v" and zv:"z\<parallel>v" and lc:"l\<parallel>c" and cu:"c\<parallel>u" using m ov by blast
  obtain k' where kpp:"k'\<parallel>p" using M3 meets_wd pz by blast
  from lz lc pz have pc:"p\<parallel>c" using M1 by auto
  from kpp kq have "k'\<parallel>q \<oplus> ((\<exists>t. k'\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast 
  then have "(?A\<and>\<not>?B\<and>\<not>?C)\<or>(\<not>?A\<and>?B\<and>\<not>?C)\<or>(\<not>?A\<and>\<not>?B\<and>?C)" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> s \<union> ov \<union> d"    
  proof (elim disjE)
    {assume "(?A\<and>\<not>?B\<and>\<not>?C)" then have "?A" by simp 
     then have "(p,q) \<in> s" using s kpp qu cu pc by blast
     thus ?thesis using x by simp }
    next
    {assume "(\<not>?A\<and>?B\<and>\<not>?C)" then have "?B" by simp
     then obtain t where kpt:"k'\<parallel>t" and tq:"t\<parallel>q" by auto
     moreover from kq kl tq have "t\<parallel>l" using M1 by auto
     ultimately have "(p,q) \<in> ov" using ov kpp qu cu lc pc by blast
     thus ?thesis using x by simp}
    next
    {assume "(\<not>?A\<and>\<not>?B\<and>?C)" then have "?C" by simp
     then obtain t where kt:"k\<parallel>t" and tp:"t\<parallel>p" by auto
     then  have "(p,q)\<in>d" using d kq cu qu pc by blast
     thus ?thesis using x by simp}
  qed
qed

lemma covd:"ov O d \<subseteq> s \<union> ov \<union> d"
proof
  fix x::"'a\<times>'a" assume "x \<in> ov O d" then obtain p q z where x:"x=(p,q)" and "(p,z) \<in> ov" and "(z,q) \<in> d" by auto
  from \<open>(p,z) \<in> ov\<close> obtain k u v l c where kp:"k\<parallel>p" and pu:"p\<parallel>u" and uv:"u\<parallel>v" and zv:"z\<parallel>v" and lc:"l\<parallel>c" and cu:"c\<parallel>u" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and cu:"c\<parallel>u" using ov by blast
  from \<open>(z,q) \<in> d\<close> obtain k' l' u' v' where kpq:"k'\<parallel>q" and kplp:"k'\<parallel>l'" and lpz:"l'\<parallel>z" and qvp:"q\<parallel>v'" and zup:"z\<parallel>u'" and upvp:"u'\<parallel>v'" using d by blast
  from uv zv zup have "u\<parallel>u'" using M1 by auto
  from pu upvp obtain uu where puu:"p\<parallel>uu" and uuvp:"uu\<parallel>v'" using \<open>u\<parallel>u'\<close> using M5exist_var by blast
  from kp kpq have "k\<parallel>q \<oplus> ((\<exists>t. k\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in>  s \<union> ov \<union> d"
  proof (elim disjE)
    { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
      then have "(p,q) \<in> s" using s kp qvp puu uuvp by blast
      thus ?thesis using x by blast}
    next
    { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
      then obtain t where kt:"k\<parallel>t" and tq:"t\<parallel>q" by auto
      from cu pu puu have "c\<parallel>uu" using M1 by auto
      moreover from kpq tq kplp have "t\<parallel>l'" using M1 by auto
      moreover from lpz lz lc have lpc:"l'\<parallel>c" using M1 by auto
      ultimately obtain lc where "t\<parallel>lc" and "lc\<parallel>uu" using M5exist_var by blast
      then have "(p,q) \<in> ov" using ov kp kt tq puu uuvp qvp  by blast
      thus ?thesis using x by auto}
    next
    { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
      then obtain t where "k'\<parallel>t" and "t\<parallel>p" by auto
      with puu uuvp qvp kpq have "(p,q) \<in> d" using d by blast
      thus ?thesis using x by auto}
  qed
qed


lemma covf:"ov O f \<subseteq> s \<union> ov \<union> d"
proof
  fix x::"'a\<times>'a" assume "x \<in> ov O f" then obtain p q z where x:"x=(p,q)" and "(p,z) \<in> ov" and "(z,q) \<in> f" by auto
  from \<open>(p,z) \<in> ov\<close> obtain k u v l c where kp:"k\<parallel>p" and pu:"p\<parallel>u" and uv:"u\<parallel>v" and zv:"z\<parallel>v" and lc:"l\<parallel>c" and cu:"c\<parallel>u" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and cu:"c\<parallel>u" using ov by blast
  from \<open>(z,q) \<in> f\<close> obtain k' l' u'  where kpq:"k'\<parallel>q" and kplp:"k'\<parallel>l'" and lpz:"l'\<parallel>z" and qup:"q\<parallel>u'" and zup:"z\<parallel>u'" using f by blast
  from uv zv zup have uu:"u\<parallel>u'" using M1 by auto
  from kp kpq have "k\<parallel>q \<oplus> ((\<exists>t. k\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in>  s \<union> ov \<union> d"
  proof (elim disjE)
    { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
      then have "(p,q) \<in> s" using s kp qup uu pu by blast
      thus ?thesis using x by blast}
    next
    { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
      then obtain t where kt:"k\<parallel>t" and tq:"t\<parallel>q" by auto
      moreover from kpq tq kplp have "t\<parallel>l'" using M1 by auto
      moreover from lpz lz lc have lpc:"l'\<parallel>c" using M1 by auto
      ultimately obtain lc where "t\<parallel>lc" and "lc\<parallel>u" using cu M5exist_var by blast
      then have "(p,q) \<in> ov" using ov kp kt tq pu uu qup  by blast
      thus ?thesis using x by auto}
    next
    { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
      then obtain t where "k'\<parallel>t" and "t\<parallel>p" by auto
      with pu uu qup kpq have "(p,q) \<in> d" using d by blast
      thus ?thesis using x by auto}
  qed
qed

lemma cfid:"f^-1 O d \<subseteq> s \<union> ov \<union> d"
proof
  fix x::"'a\<times>'a" assume "x \<in> f^-1 O d" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> f^-1" and "(z,q)\<in> d" by auto
  from \<open>(p,z) \<in> f^-1\<close> obtain k l u where "k\<parallel>l" and "l\<parallel>z" and kp:"k\<parallel>p" and pu:"p\<parallel>u" and zu:"z\<parallel>u" using f by blast
  from \<open>(z,q) \<in> d\<close> obtain k' l' u' v where kplp:"k'\<parallel>l'" and kpq:"k'\<parallel>q" and lpz:"l'\<parallel>z" and zup:"z\<parallel>u'" and upv:"u'\<parallel>v" and qv:"q\<parallel>v" using d by blast
  from pu zu zup have pup:"p\<parallel>u'" using M1 by blast
  from kp kpq have "k\<parallel>q \<oplus> ((\<exists>t. k\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> s \<union> ov \<union> d"
  proof (elim disjE)
    { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
      with pup upv kp qv have "(p,q) \<in> s" using s by blast
      thus ?thesis using x by auto}
    next
    { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
      then obtain t where kt:"k\<parallel>t" and tq:"t\<parallel>q" by auto
      from tq kpq kplp have "t\<parallel>l'" using M1 by blast
      with lpz zup obtain lpz where "t\<parallel>lpz" and "lpz\<parallel>u'" using M5exist_var by blast
      with kp pup upv kt tq qv have "(p,q)\<in>ov" using ov by blast
      thus ?thesis using x by blast}
       next
    { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
      then obtain t where "k'\<parallel>t" and "t\<parallel>p" by auto
      with pup upv kpq qv have "(p,q) \<in> d" using d by blast
      thus ?thesis using x by auto}
    qed
qed

lemma cfov:"f O ov \<subseteq> ov \<union> s \<union> d"
proof
    fix x::"'a\<times>'a" assume "x \<in> f O ov" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> f" and "(z,q)\<in> ov" by auto
    from \<open>(p,z) \<in> f\<close> obtain  k l u where "k\<parallel>l" and kz:"k\<parallel>z" and lp:"l\<parallel>p" and pu:"p\<parallel>u" and zu:"z\<parallel>u" using f by blast
    from \<open>(z,q) \<in> ov\<close> obtain k' l' c  u' v where "k'\<parallel>l'" and kpz:"k'\<parallel>z" and lpq:"l'\<parallel> q" and  zup:"z\<parallel>u'" and upv:"u'\<parallel>v" and qv:"q\<parallel>v" and lpc:"l'\<parallel>c" and cup:"c\<parallel>u'"  using  ov by blast
    from pu zu zup have pup:"p\<parallel>u'" using M1 by blast
    from lp lpq have "l\<parallel>q \<oplus> ((\<exists>t. l\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. l'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
    then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
    thus "x \<in> ov \<union> s \<union> d"
    proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with  lp pup upv qv have "(p,q) \<in> s" using s by blast
        thus ?thesis using x by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
      then obtain t where lt:"l\<parallel>t" and tq:"t\<parallel>q" by auto
      from tq lpq lpc have "t\<parallel>c" using M1 by blast
      with lp lt tq pup upv qv cup have "(p,q)\<in>ov" using ov by blast
      thus ?thesis using x by blast}
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
      then obtain t where "l'\<parallel>t" and "t\<parallel>p" by auto
      with lpq pup upv qv have "(p,q) \<in> d" using d by blast
      thus ?thesis using x by auto}
    qed
qed

(* ========= $\alpha_2$ composition ========== *)
text \<open>We prove compositions of the form $r_1 \circ r_2 \subseteq ov \cup f^{-1} \cup d^{-1}$.\<close>

lemma covsi:"ov O s^-1 \<subseteq> ov \<union> f^-1 \<union> d^-1"
proof
    fix x::"'a\<times>'a" assume "x \<in> ov O s^-1" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> ov" and "(z,q) \<in> s^-1" by auto
    from \<open>(p,z) \<in> ov\<close> obtain k l c u  where kp:"k\<parallel>p" and pu:"p\<parallel>u" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and lc:"l\<parallel>c" and cu:"c\<parallel>u" using ov by blast
    from \<open>(z,q) \<in> s^-1\<close> obtain k' u' v' where kpz:"k'\<parallel>z" and kpq:"k'\<parallel>q" and kpz:"k'\<parallel>z" and  zup:"z\<parallel>u'"  and qvp:"q\<parallel>v'" using s by blast
    from lz kpz kpq have lq:"l\<parallel>q" using M1 by blast
    from pu qvp have "p\<parallel>v' \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>v') \<oplus> (\<exists>t. q\<parallel>t \<and> t\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
    then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
    thus "x \<in> ov \<union> f^-1 \<union> d^-1"
    proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with qvp kp kl lq have "(p,q) \<in> f^-1" using f by blast
        thus ?thesis using x by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where ptp:"p\<parallel>t" and "t\<parallel>v'" by auto
        moreover with pu cu have "c\<parallel>t" using M1 by blast
        ultimately have "(p,q)\<in> ov" using kp kl lc cu lq qvp  ov by blast
        thus ?thesis using x by auto}        
     next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where qt:"q\<parallel>t" and "t\<parallel>u" by auto
        with kp kl lq pu  have "(p,q) \<in> d^-1" using d by blast 
        thus ?thesis using x by auto}
      qed
qed


lemma cdim:"d^-1 O m \<subseteq>  ov \<union> d^-1 \<union> f^-1"
proof 
    fix x::"'a\<times>'a" assume "x \<in> d^-1 O m" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> d^-1" and "(z,q) \<in> m" by auto
    from \<open>(p,z) \<in> d^-1\<close> obtain k l u v where kp:"k\<parallel>p" and pv:"p\<parallel>v" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and zu:"z\<parallel>u" and uv:"u\<parallel>v" using d by blast
    from \<open>(z,q) \<in> m\<close>  have zq:"z\<parallel>q" using m by blast
    obtain v' where qvp:"q\<parallel>v'" using M3 meets_wd zq by blast
    from kl lz zq obtain lz where klz:"k\<parallel>lz" and lzq:"lz\<parallel>q" using M5exist_var  by blast
    from pv qvp have "p\<parallel>v' \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>v') \<oplus> (\<exists>t. q\<parallel>t \<and> t\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
    then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
    thus "x \<in>  ov \<union> d^-1 \<union> f^-1"
    proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with qvp kp klz lzq\<open>?A\<close> have "(p,q) \<in> f^-1" using f by blast
        thus ?thesis using x by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where pt:"p\<parallel>t" and tvp:"t\<parallel>v'" by auto
        from zq lzq zu have "lz\<parallel>u" using M1 by auto
        moreover from pt pv uv have "u\<parallel>t" using M1 by auto
        ultimately have "(p,q)\<in> ov" using kp klz lzq pt tvp qvp ov by blast
        thus ?thesis using x by auto}        
     next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where qt:"q\<parallel>t" and "t\<parallel>v" by auto
        with kp klz lzq pv have "(p,q) \<in> d^-1" using d by blast 
        thus ?thesis using x by auto}
      qed
qed

lemma cdiov:"d^-1 O ov \<subseteq> ov \<union> f^-1 \<union> d^-1"
proof
    fix x::"'a\<times>'a" assume "x \<in> d^-1 O ov" then obtain p q r where x:"x = (p,r)" and "(p,q) \<in> d^-1" and "(q,r) \<in> ov" by auto
    from \<open>(p,q) \<in> d^-1\<close> obtain u v k l  where kp:"k\<parallel>p" and pv:"p\<parallel>v" and kl:"k\<parallel>l" and lq:"l\<parallel>q"  and qu:"q\<parallel>u" and uv:"u\<parallel>v" using d by blast
    from \<open>(q,r) \<in> ov\<close> obtain k' l' t u' v' where lpr:"l'\<parallel>r" and kpq:"k'\<parallel>q" and kplp:"k'\<parallel>l'" and qup:"q\<parallel>u'" and "u'\<parallel>v'" and rvp:"r\<parallel>v'" and lpt:"l'\<parallel>t" and tup:"t\<parallel>u'" using ov by blast
    from lq kplp kpq have "l\<parallel>l'" using M1 by blast
    with kl lpr  obtain ll where  kll:"k\<parallel>ll" and llr:"ll\<parallel>r"  using M5exist_var by blast
    from pv rvp have "p\<parallel>v' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>v') \<oplus> (\<exists>t'. r\<parallel>t' \<and> t'\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
    then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
    thus "x \<in> ov \<union> f^-1 \<union> d^-1"
    proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with rvp llr kp kll have "(p,r) \<in> f^-1" using f by blast
        thus ?thesis using x by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t' where ptp:"p\<parallel>t'" and tpvp:"t'\<parallel>v'" by auto
        moreover from lpt lpr llr have llt:"ll\<parallel>t" using M1 by blast
        moreover from ptp uv pv have utp:"u\<parallel>t'" using M1 by blast
        moreover from qu tup qup have "t\<parallel>u" using M1 by blast
        moreover with utp llt obtain tu where "ll\<parallel>tu" and "tu\<parallel>t'" using M5exist_var by blast
        with kp ptp tpvp kll llr rvp  have "(p,r)\<in> ov" using  ov by blast
        thus ?thesis using x by auto}        
     next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t' where rtp:"r\<parallel>t'" and "t'\<parallel>v" by auto
        with kll llr kp pv have "(p,r) \<in> d^-1" using d by blast 
        thus ?thesis using x by auto}
      qed
qed

lemma cdis:"d^-1 O s \<subseteq> ov \<union> f^-1 \<union> d^-1"
proof
  fix x::"'a\<times>'a" assume "x \<in> d^-1 O s" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> d^-1" and "(z,q) \<in> s" by auto
  from \<open>(p,z)\<in>d^-1\<close> obtain k l u v where kl:"k\<parallel>l" and lz:"l\<parallel>z" and kp:"k\<parallel>p" and zu:"z\<parallel>u" and uv:"u\<parallel>v" and pv:"p\<parallel>v" using d by blast
  from \<open>(z,q) \<in> s\<close> obtain l'  v' where lpz:"l'\<parallel>z" and lpq:"l'\<parallel>q" and qvp:"q\<parallel>v'" using s by blast
  from lz lpz lpq have lq:"l\<parallel>q" using M1 by blast
  from pv qvp have "p\<parallel>v' \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>v') \<oplus> (\<exists>t. q\<parallel>t \<and> t\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> ov \<union> f^-1 \<union> d^-1"
    proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with kl lq qvp kp have "(p,q) \<in> f^-1" using f by blast
        thus ?thesis using x by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where pt:"p\<parallel>t" and tvp:"t\<parallel>v'" by auto
        from pt pv uv have "u\<parallel>t" using M1 by blast
        with lz zu obtain zu where "l\<parallel>zu" and "zu\<parallel>t" using M5exist_var by blast
        with kp pt tvp kl lq qvp have "(p,q) \<in> ov" using ov by blast
        thus ?thesis using x by auto}
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where "q\<parallel>t" and "t\<parallel>v" by auto
        with kl lq kp pv have "(p,q)\<in>d^-1" using d by blast
        thus ?thesis using x by auto}
      qed
qed

lemma csim:"s^-1 O m \<subseteq> ov \<union> f^-1 \<union> d^-1"
proof 
  fix x::"'a\<times>'a" assume "x \<in> s^-1 O m" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> s^-1" and "(z,q) \<in> m" by auto
  from \<open>(p,z)\<in>s^-1\<close> obtain k u v where kp:"k\<parallel>p" and kz:"k\<parallel>z" and zu:"z\<parallel>u" and uv:"u\<parallel>v" and pv:"p\<parallel>v" using s by blast
  from \<open>(z,q) \<in> m\<close> have zq:"z\<parallel>q" using m by auto
  obtain v' where qvp:"q\<parallel>v'" using M3 meets_wd zq by blast
  from pv qvp have "p\<parallel>v' \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>v') \<oplus> (\<exists>t. q\<parallel>t \<and> t\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> ov \<union> f^-1 \<union> d^-1"
    proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with kp kz zq qvp have "(p,q) \<in> f^-1" using f by blast
        thus ?thesis using x by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where pt:"p\<parallel>t" and tvp:"t\<parallel>v'" by auto
        from pt pv uv have "u\<parallel>t" using M1 by blast
        with kp pt tvp kz zq qvp zu  have "(p,q) \<in> ov" using ov by blast
        thus ?thesis using x by auto}
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where "q\<parallel>t" and "t\<parallel>v" by auto
        with kp kz zq pv have "(p,q)\<in>d^-1" using d by blast
        thus ?thesis using x by auto}
      qed
qed
 
lemma csiov:"s^-1 O ov \<subseteq> ov \<union> f^-1 \<union> d^-1"
proof 
  fix x::"'a\<times>'a" assume "x \<in> s^-1 O ov" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> s^-1" and "(z,q) \<in> ov" by auto
  from \<open>(p,z)\<in>s^-1\<close> obtain k u v where kp:"k\<parallel>p" and kz:"k\<parallel>z" and zu:"z\<parallel>u" and uv:"u\<parallel>v" and pv:"p\<parallel>v" using s by blast
  from \<open>(z,q) \<in> ov\<close> obtain k' l' u' v' c where kpz:"k'\<parallel>z" and zup:"z\<parallel>u'" and upvp:"u'\<parallel>v'" and kplp:"k'\<parallel>l'" and lpq:"l'\<parallel>q" and qvp:"q\<parallel>v'" and lpc:"l'\<parallel>c" and cup:"c\<parallel>u'" using ov by blast
  from kz kpz kplp have klp:"k\<parallel>l'" using M1 by auto
  from pv qvp have "p\<parallel>v' \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>v') \<oplus> (\<exists>t. q\<parallel>t \<and> t\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> ov \<union> f^-1 \<union> d^-1"
    proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with kp kplp lpq qvp klp have "(p,q) \<in> f^-1" using f by blast
        thus ?thesis using x by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where pt:"p\<parallel>t" and tvp:"t\<parallel>v'" by auto
        from pt pv uv have "u\<parallel>t" using M1 by blast
        moreover from cup zup zu have cu:"c\<parallel>u" using M1 by auto
        ultimately obtain cu where "l'\<parallel>cu" and "cu\<parallel>t" using lpc M5exist_var by blast
        with kp pt tvp klp lpq qvp have "(p,q) \<in> ov" using ov by blast
        thus ?thesis using x by auto}
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where "q\<parallel>t" and "t\<parallel>v" by auto
        with kp klp lpq pv have "(p,q)\<in>d^-1" using d by blast
        thus ?thesis using x by auto}
      qed
qed

lemma covim:"ov^-1 O m \<subseteq> ov \<union> f^-1 \<union> d^-1"
proof
    fix x::"'a\<times>'a" assume "x \<in> ov^-1 O m" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> ov^-1" and "(z,q) \<in> m" by auto
    from \<open>(p,z) \<in> ov^-1\<close> obtain k l c u v  where kz:"k\<parallel>z" and zu:"z\<parallel>u" and kl:"k\<parallel>l" and lp:"l\<parallel>p" and lc:"l\<parallel>c" and cu:"c\<parallel>u" and pv:"p\<parallel>v" and uv:"u\<parallel>v" using ov by blast
    from \<open>(z,q) \<in> m\<close>  have zq:"z\<parallel>q" using m by auto
    obtain v' where qvp:"q\<parallel>v'" using M3 meets_wd zq by blast
    from zu zq cu have cq:"c\<parallel>q" using M1 by blast
    from pv qvp have "p\<parallel>v' \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>v') \<oplus> (\<exists>t. q\<parallel>t \<and> t\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
    then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
    thus "x \<in> ov \<union> f^-1 \<union> d^-1"
    proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with lp lc cq qvp have "(p,q) \<in> f^-1" using f by blast
        thus ?thesis using x by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where ptp:"p\<parallel>t" and "t\<parallel>v'" by auto
        moreover with pv uv have "u\<parallel>t" using M1 by blast
        ultimately have "(p,q)\<in> ov" using lp lc cq qvp cu ov by blast
        thus ?thesis using x by auto}        
     next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where qt:"q\<parallel>t" and "t\<parallel>v" by auto
        with lp lc cq pv have "(p,q) \<in> d^-1" using d by blast 
        thus ?thesis using x by auto}
      qed
qed

(* =========$\alpha_3$ compositions========== *)
text \<open>We prove compositions of the form $r_1 \circ r_2 \subseteq b \cup m \cup ov$.\<close>

lemma covov:"ov O ov \<subseteq> b \<union> m \<union> ov"
proof
   fix x::"'a\<times>'a" assume "x \<in> ov O ov" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> ov" and "(z,q)\<in> ov" by auto
   from \<open>(p,z) \<in> ov\<close> obtain k u l t v where kp:"k\<parallel>p" and pu:"p\<parallel>u" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and "l\<parallel>t" and "t\<parallel>u" and uv:"u\<parallel>v" and zv:"z\<parallel>v" using ov by blast
   from  \<open>(z,q) \<in> ov\<close> obtain k' l' y u' v' where kplp:"k'\<parallel>l'" and kpz:"k'\<parallel>z" and lpq:"l'\<parallel>q" and lpy:"l'\<parallel>y" and "y\<parallel>u'" and zup:"z\<parallel>u'" and upvp:"u'\<parallel>v'" and qvp:"q\<parallel>v'" using ov by blast
   from lz kplp kpz have llp:"l\<parallel>l'" using M1 by blast
   from uv zv zup have "u\<parallel>u'" using M1 by blast
   with pu upvp obtain uu where puu:"p\<parallel>uu" and uuv:"uu\<parallel>v'" using M5exist_var by blast
   from puu lpq have "p\<parallel>q \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>q) \<oplus> (\<exists>t'. l'\<parallel>t' \<and> t'\<parallel>uu))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
    then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
    thus "x \<in> b \<union> m \<union> ov"
    proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        then have "(p,q) \<in> m" using m by auto
        thus ?thesis using x by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then have "(p,q) \<in> b" using b by auto
        thus ?thesis using x by auto}
     next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t' where lptp:"l'\<parallel>t'" and "t'\<parallel>uu" by auto
        from kl llp lpq obtain ll where  kll:"k\<parallel>ll" and llq:"ll\<parallel>q" using M5exist_var by blast
        with lpq lptp  have "ll\<parallel>t'" using M1 by blast
        with kp puu uuv kll llq qvp \<open>t'\<parallel>uu\<close> have "(p,q) \<in> ov" using ov by blast
        thus ?thesis using x by auto}
      qed
qed

lemma covfi:"ov O f^-1 \<subseteq> b \<union> m \<union> ov"
proof
   fix x::"'a\<times>'a" assume "x \<in> ov O f^-1" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> ov" and "(z,q)\<in> f^-1" by auto
   from \<open>(p,z) \<in> ov\<close> obtain k u l c v where kp:"k\<parallel>p" and pu:"p\<parallel>u" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and "l\<parallel>c" and "c\<parallel>u" and uv:"u\<parallel>v" and zv:"z\<parallel>v" using ov by blast
   from  \<open>(z,q) \<in> f^-1\<close> obtain k' l' v'  where kplp:"k'\<parallel>l'" and kpz:"k'\<parallel>z" and lpq:"l'\<parallel>q"  and qvp:"q\<parallel>v'" and zvp:"z\<parallel>v'" using f by blast
   from lz kplp kpz have llp:"l\<parallel>l'" using M1 by blast
   from  zv qvp zvp have qv:"q\<parallel>v" using M1 by blast
   from pu lpq have "p\<parallel>q \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. l'\<parallel>t \<and> t\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
    then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
    thus "x \<in> b \<union> m \<union> ov"
    proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        then have "(p,q) \<in> m" using m by auto
        thus ?thesis using x by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then have "(p,q) \<in> b" using b by auto
        thus ?thesis using x by auto}
     next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where lptp:"l'\<parallel>t" and "t\<parallel>u" by auto
        from kl llp lpq obtain ll where  kll:"k\<parallel>ll" and llr:"ll\<parallel>q" using M5exist_var by blast
        with lpq lptp  have "ll\<parallel>t" using M1 by blast
        with kp pu uv kll llr qv \<open>t\<parallel>u\<close> have "(p,q) \<in> ov" using ov by blast
        thus ?thesis using x by auto}
      qed
qed


lemma csov:"s O ov \<subseteq> b \<union> m \<union> ov"
proof
   fix x::"'a\<times>'a" assume "x \<in> s O ov" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> s" and "(z,q)\<in> ov" by auto
   from \<open>(p,z) \<in> s\<close> obtain k u v where kp:"k\<parallel>p" and kz:"k\<parallel>z" and  pu:"p\<parallel>u" and uv:"u\<parallel>v" and zv:"z\<parallel>v" using s by blast
   from  \<open>(z,q) \<in> ov\<close> obtain k' l'  u' v'   where kpz:"k'\<parallel>z"  and kplp:"k'\<parallel>l'" and lpq:"l'\<parallel>q" and zup:"z\<parallel>u'"  and qvp:"q\<parallel>v'" and upvp:"u'\<parallel>v'" using ov by blast
   from  kz kpz kplp have klp:"k\<parallel>l'" using M1 by blast
   from  uv zv zup  have uup:"u\<parallel>u'" using M1 by blast
   with pu upvp obtain uu where puu:"p\<parallel>uu" and uuvp:"uu\<parallel>v'" using M5exist_var by blast
   from pu lpq have "p\<parallel>q \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. l'\<parallel>t \<and> t\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
   then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
   thus "x \<in> b \<union> m \<union> ov"
   proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        then have "(p,q) \<in> m" using m by auto
        thus ?thesis using x by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then have "(p,q) \<in> b" using b by auto
        thus ?thesis using x by auto}
     next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where lpt:"l'\<parallel>t" and "t\<parallel>u" by auto
        with pu puu have "t\<parallel>uu" using M1 by blast
        with lpt kp puu uuvp klp lpq qvp  have "(p,q) \<in> ov" using ov by blast
        thus ?thesis using x by auto}
      qed
qed


lemma csfi:"s O f^-1 \<subseteq> b \<union> m \<union> ov"
proof
   fix x::"'a\<times>'a" assume "x \<in> s O f^-1" then obtain p q r where x:"x = (p,r)" and "(p,q) \<in> s" and "(q,r)\<in> f^-1" by auto
   from \<open>(p,q) \<in> s\<close> obtain k u v where kp:"k\<parallel>p" and kq:"k\<parallel>q" and  pu:"p\<parallel>u" and uv:"u\<parallel>v"  and qv:"q\<parallel>v"  using s by blast
   from  \<open>(q,r) \<in> f^-1\<close> obtain k' l  v'  where kpq:"k'\<parallel>q"  and kpl:"k'\<parallel>l" and lr:"l\<parallel>r"   and rvp:"r\<parallel>v'" and qvp:"q\<parallel>v'" using f by blast
   from kpq kpl kq have kl:"k\<parallel>l" using M1 by blast 
   from qvp qv uv have uvp:"u\<parallel>v'" using M1 by blast
   from pu lr have "p\<parallel>r \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>r) \<oplus> (\<exists>t'. l\<parallel>t' \<and> t'\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
   then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
   thus "x \<in> b \<union> m \<union> ov"
   proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        then have "(p,r) \<in> m" using m by auto
        thus ?thesis using x by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then have "(p,r) \<in> b" using b by auto
        thus ?thesis using x by auto}
     next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t' where ltp:"l\<parallel>t'" and "t'\<parallel>u" by auto
        with kp pu uvp kl lr rvp have "(p,r) \<in> ov" using ov by blast
        thus ?thesis using x by auto}
      qed
qed

(* =========$\alpha_4$ compositions========== *)
text \<open>We prove compositions of the form $r_1 \circ r_2 \subseteq f \cup f^{-1} \cup e$.\<close>

lemma cmmi:"m O m^-1 \<subseteq> f \<union> f^-1 \<union> e"
proof 
  fix x::"'a\<times>'a" assume a:"x \<in> m O m^-1" then obtain p q z where x:"x =(p,q)" and 1:"(p,z) \<in> m" and 2:"(z,q) \<in> m^-1" by auto
  then have pz:"p\<parallel>z" and qz:"q\<parallel>z" using m by auto
  obtain k k' where kp:"k\<parallel>p" and kpq:"k'\<parallel>q" using M3 meets_wd qz pz by blast
  from kp kpq have "k\<parallel>q \<oplus> ((\<exists>t. k\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast 
  then have "(?A\<and>\<not>?B\<and>\<not>?C)\<or>(\<not>?A\<and>?B\<and>\<not>?C)\<or>(\<not>?A\<and>\<not>?B\<and>?C)" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in>f \<union> f^-1 \<union> e"    
  proof (elim disjE)
    {assume "(?A\<and>\<not>?B\<and>\<not>?C)" then have "?A" by simp 
     then have "p = q" using M4 kp pz qz by blast 
     then have "(p,q) \<in> e" using e by auto
     thus ?thesis using x by simp }
    next
    {assume "(\<not>?A\<and>?B\<and>\<not>?C)" then have "?B" by simp
     then obtain t where kt:"k\<parallel>t" and tq:"t\<parallel>q" by auto
     then have "(p,q) \<in> f^-1" using f qz pz kp by blast
     thus ?thesis using x by simp}
    next
    {assume "(\<not>?A\<and>\<not>?B\<and>?C)" then have "?C" by simp
     then obtain t where kt:"k'\<parallel>t" and tp:"t\<parallel>p" by auto
     with kpq pz qz have "(p,q)\<in>f" using f by blast
     thus ?thesis using x by simp}
  qed
qed
  

lemma cfif:"f^-1 O f \<subseteq> e \<union> f^-1 \<union> f"
proof
  fix x::"'a\<times>'a" assume a:"x \<in> f^-1 O f" then obtain p q z where x:"x =(p,q)" and 1:"(p,z) \<in> f^-1" and 2:"(z,q) \<in> f" by auto
  from 1 obtain k l u where kp:"k\<parallel>p" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and zu:"z\<parallel>u" and pu:"p\<parallel>u" using f by blast
  from 2 obtain k' l' u' where kpq:"k'\<parallel>q" and kplp:"k'\<parallel>l'" and lpz:"l'\<parallel>z" and zup:"z\<parallel>u'" and qup:"q\<parallel>u'" using f by blast
  from zu zup qup have qu:"q\<parallel>u" using M1 by auto
  from kp kpq have "k\<parallel>q \<oplus> ((\<exists>t. k\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast 
  then have "(?A\<and>\<not>?B\<and>\<not>?C)\<or>(\<not>?A\<and>?B\<and>\<not>?C)\<or>(\<not>?A\<and>\<not>?B\<and>?C)" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> e \<union> f^-1 \<union> f"    
  proof (elim disjE)
    {assume "(?A\<and>\<not>?B\<and>\<not>?C)" then have "?A" by simp 
     then have "p = q" using M4 kp pu qu by blast 
     then have "(p,q) \<in> e" using e by auto
     thus ?thesis using x by simp }
    next
    {assume "(\<not>?A\<and>?B\<and>\<not>?C)" then have "?B" by simp
     then obtain t where kt:"k\<parallel>t" and tq:"t\<parallel>q" by auto
     then have "(p,q) \<in> f^-1" using f qu pu kp by blast
     thus ?thesis using x by simp}
    next
    {assume "(\<not>?A\<and>\<not>?B\<and>?C)" then have "?C" by simp
     then obtain t where kt:"k'\<parallel>t" and tp:"t\<parallel>p" by auto
     with kpq pu qu have "(p,q)\<in>f" using f by blast
     thus ?thesis using x by simp}
  qed
qed

lemma cffi:"f O f^-1 \<subseteq> e \<union> f \<union> f^-1"
proof
   fix x::"'a\<times>'a" assume "x \<in> f O f^-1" then obtain p q r where x:"x = (p,r)" and "(p,q)\<in>f" and "(q,r) \<in>f^-1" by auto
   from \<open>(p,q)\<in>f\<close> \<open>(q,r) \<in> f^-1\<close> obtain k k' where kp:"k\<parallel>p" and kpr:"k'\<parallel>r" using f by blast
   from \<open>(p,q)\<in>f\<close> \<open>(q,r) \<in> f^-1\<close> obtain u where pu:"p\<parallel>u" and "q\<parallel>u" and ru:"r\<parallel>u" using f M1 by blast
   from kp kpr have "k\<parallel>r \<oplus> ((\<exists>t. k\<parallel>t \<and> t\<parallel>r) \<oplus> (\<exists>t. k'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
   then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
   thus "x \<in> e \<union> f \<union> f^-1"
   proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with pu ru kp have "p = r" using M4 by auto
        thus ?thesis using x e by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where kt:"k\<parallel>t" and tr:"t\<parallel>r" by auto
        with ru kp pu show ?thesis using x f by blast}
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where rtp:"k'\<parallel>t" and "t\<parallel>p" by auto
        with kpr ru pu show ?thesis using x f by blast}
    qed
qed

(* =========$\alpha_5$ composition========== *)
text \<open>We prove compositions of the form $r_1 \circ r_2 \subseteq e \cup s \cup s^{-1}$.\<close>

lemma cssi:"s O s^-1 \<subseteq> e \<union> s \<union> s^-1"
proof
   fix x::"'a\<times>'a" assume "x \<in> s O s^-1" then obtain p q r where x:"x = (p,r)" and "(p,q)\<in>s" and "(q,r) \<in>s^-1" by auto
   from \<open>(p,q)\<in>s\<close> \<open>(q,r) \<in> s^-1\<close> obtain k  where kp:"k\<parallel>p" and kr:"k\<parallel>r" and kq:"k\<parallel>q" using s M1  by blast
   from \<open>(p,q)\<in>s\<close> \<open>(q,r) \<in> s^-1\<close> obtain u u' where pu:"p\<parallel>u" and  rup:"r\<parallel>u'" using s by blast
   then have "p\<parallel>u' \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>u') \<oplus> (\<exists>t. r\<parallel>t \<and> t\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
   then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
   thus "x \<in> e \<union> s \<union> s^-1"
   proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with rup kp kr have "p = r" using M4 by auto
        thus ?thesis using x e by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where kt:"p\<parallel>t" and tr:"t\<parallel>u'" by auto
        with rup kp kr  show ?thesis using x s by blast}
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where rtp:"r\<parallel>t" and "t\<parallel>u" by auto
        with pu kp kr show ?thesis using x s  by blast}
    qed
qed

lemma csis:"s^-1 O s \<subseteq> e \<union> s \<union> s^-1"
proof
   fix x::"'a\<times>'a" assume "x \<in> s^-1 O s" then obtain p q r where x:"x = (p,r)" and "(p,q)\<in>s^-1" and "(q,r) \<in>s" by auto
   from \<open>(p,q)\<in>s^-1\<close> \<open>(q,r) \<in> s\<close> obtain k  where kp:"k\<parallel>p" and kr:"k\<parallel>r" and kq:"k\<parallel>q" using s M1  by blast
   from \<open>(p,q)\<in>s^-1\<close> \<open>(q,r) \<in> s\<close> obtain u u' where pu:"p\<parallel>u" and  rup:"r\<parallel>u'" using s by blast
   then have "p\<parallel>u' \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>u') \<oplus> (\<exists>t. r\<parallel>t \<and> t\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
   then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
   thus "x \<in> e \<union> s \<union> s^-1"
   proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with rup kp kr have "p = r" using M4 by auto
        thus ?thesis using x e by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where kt:"p\<parallel>t" and tr:"t\<parallel>u'" by auto
        with rup kp kr  show ?thesis using x s by blast}
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where rtp:"r\<parallel>t" and "t\<parallel>u" by auto
        with pu kp kr show ?thesis using x s  by blast}
    qed
qed

lemma cmim:"m^-1 O m \<subseteq> s \<union> s^-1 \<union> e"
proof
   fix x::"'a\<times>'a" assume "x \<in> m^-1 O m" then obtain p q r where x:"x = (p,r)" and "(p,q)\<in>m^-1" and "(q,r) \<in>m" by auto
   from \<open>(p,q)\<in>m^-1\<close> \<open>(q,r) \<in> m\<close>  have qp:"q\<parallel>p" and qr:"q\<parallel>r" using m  by auto
   obtain u u'  where pu:"p\<parallel>u" and  rup:"r\<parallel>u'" using M3 meets_wd qp qr by fastforce
   then have "p\<parallel>u' \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>u') \<oplus> (\<exists>t. r\<parallel>t \<and> t\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
   then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
   thus "x \<in>  s \<union> s^-1 \<union> e"
   proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with rup qp qr have "p = r" using M4 by auto
        thus ?thesis using x e by auto}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where kt:"p\<parallel>t" and tr:"t\<parallel>u'" by auto
        with rup qp qr  show ?thesis using x s by blast}
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where rtp:"r\<parallel>t" and "t\<parallel>u" by auto
        with pu qp qr show ?thesis using x s  by blast}
    qed
qed

(* =========$\beta_1$ composition========== *)
subsection \<open>$\beta$-composition\<close>
text \<open>We prove compositions of the form $r_1 \circ r_2 \subseteq b \cup m \cup ov \cup s \cup d$.\<close>

lemma cbd:"b O d \<subseteq> b \<union> m \<union> ov \<union> s \<union> d"
proof 
  fix x::"'a\<times>'a" assume "x \<in> b O d" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> b" and "(z,q) \<in> d" by auto
  from \<open>(p,z) \<in> b\<close> obtain c where pc:"p\<parallel>c" and cz:"c\<parallel>z" using b by auto
  obtain a where ap:"a\<parallel>p" using M3 meets_wd pc by blast
  from \<open>(z,q) \<in> d\<close> obtain k l u v where "k\<parallel>l" and "l\<parallel>z" and kq:"k\<parallel>q" and zu:"z\<parallel>u" and uv:"u\<parallel>v" and qv:"q\<parallel>v" using d by blast
  from pc cz zu obtain cz where pcz:"p\<parallel>cz" and czu:"cz\<parallel>u" using M5exist_var by blast
  with uv obtain czu where pczu:"p\<parallel>czu" and czuv:"czu\<parallel>v" using M5exist_var by blast
  from ap kq  have "a\<parallel>q \<oplus> ((\<exists>t. a\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> b \<union> m \<union> ov \<union> s \<union> d"
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with ap pczu czuv uv qv have "(p,q) \<in> s" using s by blast
        thus ?thesis using x  by auto} 
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where at:"a\<parallel>t" and tq:"t\<parallel>q" by auto
        from pc  tq have "p\<parallel>q \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>q) \<oplus> (\<exists>t'. t\<parallel>t' \<and> t'\<parallel>c))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus "x \<in> b \<union> m \<union> ov \<union> s \<union> d"
        proof (elim disjE)
           { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
             thus ?thesis using x m by auto}
           next
           { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
             thus ?thesis using x b by auto}
           next
           { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
             then obtain t' where "t\<parallel>t'" and "t'\<parallel>c" by auto
             with pc pczu have "t'\<parallel>czu" using M1 by auto
             with at tq ap pczu czuv qv \<open>t\<parallel>t'\<close> have "(p,q)\<in>ov" using ov by blast
             thus ?thesis using x by auto}
        qed
        }  
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where "k\<parallel>t" and "t\<parallel>p" by auto
        with kq pczu czuv uv qv have "(p,q) \<in> d" using d by blast
        thus ?thesis using x  by auto}
       qed
qed

lemma cbf:"b O f \<subseteq> b \<union> m \<union> ov \<union> s \<union> d"
proof 
  fix x::"'a\<times>'a" assume "x \<in> b O f" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> b" and "(z,q) \<in> f" by auto
  from \<open>(p,z) \<in> b\<close> obtain c where pc:"p\<parallel>c" and cz:"c\<parallel>z" using b by auto
  obtain a where ap:"a\<parallel>p" using M3 meets_wd pc by blast
  from \<open>(z,q) \<in> f\<close> obtain k l u  where "k\<parallel>l" and "l\<parallel>z" and kq:"k\<parallel>q" and zu:"z\<parallel>u" and qu:"q\<parallel>u" using f  by blast
  from pc cz zu obtain cz where pcz:"p\<parallel>cz" and czu:"cz\<parallel>u" using M5exist_var by blast
  from ap kq  have "a\<parallel>q \<oplus> ((\<exists>t. a\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> b \<union> m \<union> ov \<union> s \<union> d"
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with ap pcz czu  qu have "(p,q) \<in> s" using s by blast
        thus ?thesis using x  by auto} 
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where at:"a\<parallel>t" and tq:"t\<parallel>q" by auto
        from pc  tq have "p\<parallel>q \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>q) \<oplus> (\<exists>t'. t\<parallel>t' \<and> t'\<parallel>c))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus "x \<in> b \<union> m \<union> ov \<union> s \<union> d"
        proof (elim disjE)
           { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
             thus ?thesis using x m by auto}
           next
           { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
             thus ?thesis using x b by auto}
           next
           { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
             then obtain t' where "t\<parallel>t'" and "t'\<parallel>c" by auto
             with pc pcz have "t'\<parallel>cz" using M1 by auto
             with at tq ap pcz czu qu \<open>t\<parallel>t'\<close> have "(p,q)\<in>ov" using ov by blast
             thus ?thesis using x by auto}
        qed
        }  
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where "k\<parallel>t" and "t\<parallel>p" by auto
        with kq pcz czu  qu have "(p,q) \<in> d" using d by blast
        thus ?thesis using x  by auto}
       qed
qed

lemma cbovi:"b O ov^-1 \<subseteq> b \<union> m \<union> ov \<union> s \<union> d"
proof 
  fix x::"'a\<times>'a" assume "x \<in> b O ov^-1" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> b" and "(z,q) \<in> ov^-1" by auto
  from \<open>(p,z) \<in> b\<close> obtain c where pc:"p\<parallel>c" and cz:"c\<parallel>z" using b by auto
  obtain a where ap:"a\<parallel>p" using M3 meets_wd pc by blast
  from \<open>(z,q) \<in> ov^-1\<close> obtain k l u v w where "k\<parallel>l" and lz:"l\<parallel>z" and kq:"k\<parallel>q" and zv:"z\<parallel>v" and qu:"q\<parallel>u" and uv:"u\<parallel>v" and lw:"l\<parallel>w" and wu:"w\<parallel>u" using ov  by blast
  from cz lz lw have "c\<parallel>w" using M1 by auto
  with pc wu obtain cw where pcw:"p\<parallel>cw" and cwu:"cw\<parallel>u" using M5exist_var by blast
  from ap kq  have "a\<parallel>q \<oplus> ((\<exists>t. a\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> b \<union> m \<union> ov \<union> s \<union> d"
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with ap qu pcw cwu  have "(p,q) \<in> s" using s by blast
        thus ?thesis using x  by auto} 
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where at:"a\<parallel>t" and tq:"t\<parallel>q" by auto
        from pc  tq have "p\<parallel>q \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>q) \<oplus> (\<exists>t'. t\<parallel>t' \<and> t'\<parallel>c))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus "x \<in> b \<union> m \<union> ov \<union> s \<union> d"
        proof (elim disjE)
           { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
             thus ?thesis using x m by auto}
           next
           { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
             thus ?thesis using x b by auto}
           next
           { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
             then obtain t' where "t\<parallel>t'" and "t'\<parallel>c" by auto
             with pc pcw have "t'\<parallel>cw" using M1 by auto
             with at tq ap pcw cwu qu \<open>t\<parallel>t'\<close> have "(p,q)\<in>ov" using ov by blast
             thus ?thesis using x by auto}
        qed
        }  
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where "k\<parallel>t" and "t\<parallel>p" by auto
        with kq pcw cwu  qu have "(p,q) \<in> d" using d by blast
        thus ?thesis using x  by auto}
       qed
qed

lemma cbmi:"b O m^-1 \<subseteq> b \<union> m \<union> ov \<union> s \<union> d"
proof 
   fix x::"'a\<times>'a" assume "x \<in> b O m^-1" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> b" and "(z,q) \<in> m^-1" by auto
   from \<open>(p,z) \<in> b\<close> obtain c where pc:"p\<parallel>c" and cz:"c\<parallel>z" using b by auto
   obtain k where kp:"k\<parallel>p" using M3 meets_wd pc by blast
   from \<open>(z,q) \<in> m^-1\<close> have qz:"q\<parallel>z" using m by auto
   obtain k' where kpq:"k'\<parallel>q" using M3 meets_wd qz by blast 
   from kp kpq  have "k\<parallel>q \<oplus> ((\<exists>t. k\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
   then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
   thus "x \<in> b \<union> m \<union> ov \<union> s \<union> d"
   proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with kp pc cz qz  have "(p,q) \<in> s" using s by blast
        thus ?thesis using x  by auto} 
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where kt:"k\<parallel>t" and tq:"t\<parallel>q" by auto
        from pc tq have "p\<parallel>q \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>q) \<oplus> (\<exists>t'. t\<parallel>t' \<and> t'\<parallel>c))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus "x \<in> b \<union> m \<union> ov \<union> s \<union> d"
        proof (elim disjE)
           { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
             thus ?thesis using x m by auto}
           next
           { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
             thus ?thesis using x b by auto}
           next
           { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
             then obtain t' where "t\<parallel>t'" and "t'\<parallel>c" by auto
             with pc cz qz kt tq kp have "(p,q) \<in> ov" using ov by blast
             thus ?thesis using x by auto}
        qed
        }  
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where "k'\<parallel>t" and "t\<parallel>p" by auto
        with kpq pc cz qz have "(p,q) \<in> d" using d by blast
        thus ?thesis using x  by auto}
       qed
qed

lemma cdov:"d O ov \<subseteq>b \<union> m \<union> ov \<union> s \<union> d"
proof
   fix x::"'a\<times>'a" assume "x \<in> d O ov" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> d" and "(z,q) \<in> ov" by auto
   from \<open>(p,z) \<in> d\<close> obtain k l u v where kl:"k\<parallel>l" and lp:"l\<parallel>p" and kz:"k\<parallel>z" and pu:"p\<parallel>u" and uv:"u\<parallel>v" and zv:"z\<parallel>v" using d by blast
   from \<open>(z,q) \<in> ov\<close> obtain k' l' u' v' c where kplp:"k'\<parallel>l'" and kpz:"k'\<parallel>z" and lpq:"l'\<parallel>q" and zup:"z\<parallel>u'" and upvp:"u'\<parallel>v'" and qvp:"q\<parallel>v'" and "l'\<parallel>c" and "c\<parallel>u'" using ov by blast
   from zup zv uv have "u\<parallel>u'" using M1 by auto
   with pu upvp obtain uu where puu:"p\<parallel>uu" and uuvp:"uu\<parallel>v'" using M5exist_var by blast
   from lp lpq  have "l\<parallel>q \<oplus> ((\<exists>t. l\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. l'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
   then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
   thus "x \<in> b \<union> m \<union> ov \<union> s \<union> d"
   proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with lp puu uuvp qvp  have "(p,q) \<in> s" using s by blast
        thus ?thesis using x  by auto} 
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where lt:"l\<parallel>t" and tq:"t\<parallel>q" by auto
        from pu tq have "p\<parallel>q \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>q) \<oplus> (\<exists>t'. t\<parallel>t' \<and> t'\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus "x \<in> b \<union> m \<union> ov \<union> s \<union> d"
        proof (elim disjE)
           { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
             thus ?thesis using x m by auto}
           next
           { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
             thus ?thesis using x b by auto}
           next
           { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
             then obtain t' where ttp:"t\<parallel>t'" and "t'\<parallel>u" by auto
             with pu puu have "t'\<parallel>uu" using M1 by auto
             with lp puu qvp uuvp lt tq  ttp have "(p,q) \<in> ov" using ov by blast
             thus ?thesis using x by auto}
        qed
        }  
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where "l'\<parallel>t" and "t\<parallel>p" by auto
         with lpq puu uuvp qvp have "(p,q) \<in> d" using d by blast
        thus ?thesis using x  by auto}
       qed
qed

lemma cdfi:"d O f^-1 \<subseteq> b \<union> m \<union> ov \<union> s \<union> d"
proof
   fix x::"'a\<times>'a" assume "x \<in> d O f^-1" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> d" and "(z,q) \<in> f^-1" by auto
   from \<open>(p,z) \<in> d\<close> obtain k l u v where kl:"k\<parallel>l" and lp:"l\<parallel>p" and kz:"k\<parallel>z" and pu:"p\<parallel>u" and uv:"u\<parallel>v" and zv:"z\<parallel>v" using d by blast
   from \<open>(z,q) \<in> f^-1\<close> obtain k' l' u'  where kpz:"k'\<parallel>z" and kplp:"k'\<parallel>l'" and lpq:"l'\<parallel>q" and zup:"z\<parallel>u'" and  qup:"q\<parallel>u'" using f by blast
   from zup zv uv have uup:"u\<parallel>u'" using M1 by auto
   from lp lpq  have "l\<parallel>q \<oplus> ((\<exists>t. l\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. l'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
   then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
   thus "x \<in> b \<union> m \<union> ov \<union> s \<union> d"
   proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with lp pu uup qup  have "(p,q) \<in> s" using s by blast
        thus ?thesis using x  by auto} 
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where lt:"l\<parallel>t" and tq:"t\<parallel>q" by auto
        from pu tq have "p\<parallel>q \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>q) \<oplus> (\<exists>t'. t\<parallel>t' \<and> t'\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus "x \<in> b \<union> m \<union> ov \<union> s \<union> d"
        proof (elim disjE)
           { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
             thus ?thesis using x m by auto}
           next
           { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
             thus ?thesis using x b by auto}
           next
           { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
             then obtain t' where ttp:"t\<parallel>t'" and tpu:"t'\<parallel>u" by auto
             with lt tq lp pu uup qup  have "(p,q) \<in> ov" using ov by blast
             thus ?thesis using x by auto}
        qed
        }  
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where "l'\<parallel>t" and "t\<parallel>p" by auto
        with lpq pu uup qup  have "(p,q) \<in> d" using d by blast
        thus ?thesis using x  by auto}
       qed
qed

(* =========$\beta_2$ composition ==========*)
text \<open>We prove compositions of the form $r_1 \circ r_2 \subseteq b \cup m \cup ov \cup f^{-1} \cup d^{-1}$.\<close>

lemma covdi:"ov O d^-1 \<subseteq> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
proof
  fix x::"'a\<times>'a" assume "x \<in> ov O d^-1" then obtain p q z where "(p,z) : ov" and "(z,q) : d^-1" and x:"x = (p,q)" by auto
  from \<open>(p,z) : ov\<close> obtain k l u v c  where kp:"k\<parallel>p" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and pu:"p\<parallel>u" and uv:"u\<parallel>v"  and zv:"z\<parallel>v" and lc:"l\<parallel>c" and cu:"c\<parallel>u" using ov by blast
  from \<open>(z,q) : d^-1\<close> obtain l' k' u' v'  where lpq:"l'\<parallel>q" and kplp:"k'\<parallel>l'" and kpz:"k'\<parallel>z" and qup:"q\<parallel>u'" and upvp:"u'\<parallel>v'" and zvp:"z\<parallel>v'"  using d  by blast
  from lz kpz kplp have "l\<parallel>l'" using M1 by auto
  with kl lpq obtain ll where kll:"k\<parallel>ll" and llq:"ll\<parallel>q" using M5exist_var by blast
  from pu qup  have "p\<parallel>u' \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>u') \<oplus> (\<exists>t. q\<parallel>t \<and> t\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with qup kll llq kp  have "(p,q) \<in> f^-1" using f by blast
        thus ?thesis using x  by auto} 
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where pt:"p\<parallel>t" and tup:"t\<parallel>u'" by auto
        from pt lpq have "p\<parallel>q \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>q) \<oplus> (\<exists>t'. l'\<parallel>t' \<and> t'\<parallel>t))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus "x \<in> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
        proof (elim disjE)
           { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
             thus ?thesis using x m by auto}
           next
           { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
             thus ?thesis using x b by auto}
           next
           { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
             then obtain t' where lptp:"l'\<parallel>t'" and tpt:"t'\<parallel>t" by auto
             from lpq lptp llq have "ll\<parallel>t'" using M1 by auto
             with kp kll llq pt tup qup tpt  have "(p,q) \<in> ov" using ov by blast
             thus ?thesis using x by auto}
        qed
        }  
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where "q\<parallel>t" and "t\<parallel>u" by auto
        with pu kll llq kp   have "(p,q) \<in> d^-1" using d by blast
        thus ?thesis using x  by auto}
       qed
qed

lemma cdib:"d^-1 O b \<subseteq> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
proof
  fix x::"'a\<times>'a" assume "x \<in> d^-1 O b" then obtain p q z where "(p,z) : d^-1" and "(z,q) : b" and x:"x = (p,q)" by auto
  from \<open>(p,z) : d^-1\<close> obtain k l u v  where kp:"k\<parallel>p" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and pv:"p\<parallel>v" and uv:"u\<parallel>v"  and zu:"z\<parallel>u"  using d by blast
  from \<open>(z,q) : b\<close> obtain c  where  zc:"z\<parallel>c" and cq:"c\<parallel>q"  using b by blast
  with kl lz obtain lzc where klzc:"k\<parallel>lzc" and lzcq:"lzc\<parallel>q" using M5exist_var by blast
  obtain v' where qvp:"q\<parallel>v'" using M3 meets_wd cq by blast
  from pv qvp  have "p\<parallel>v' \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>v') \<oplus> (\<exists>t. q\<parallel>t \<and> t\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with qvp kp klzc lzcq  have "(p,q) \<in> f^-1" using f by blast
        thus ?thesis using x  by auto} 
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where pt:"p\<parallel>t" and tvp:"t\<parallel>v'" by auto
        from pt cq have "p\<parallel>q \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>q) \<oplus> (\<exists>t'. c\<parallel>t' \<and> t'\<parallel>t))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus "x \<in> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
        proof (elim disjE)
           { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
             thus ?thesis using x m by auto}
           next
           { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
             thus ?thesis using x b by auto}
           next
           { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
             then obtain t' where ctp:"c\<parallel>t'" and tpt:"t'\<parallel>t" by auto
             from lzcq cq ctp have "lzc\<parallel>t'" using M1 by auto
             with pt tvp qvp kp klzc lzcq tpt have "(p,q) \<in> ov" using ov by blast
             thus ?thesis using x by auto}
        qed
        }  
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where "q\<parallel>t" and "t\<parallel>v" by auto
        with pv kp klzc lzcq  have "(p,q) \<in> d^-1" using d by blast
        thus ?thesis using x  by auto}
       qed
qed

lemma csdi:"s O d^-1 \<subseteq> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
proof
  fix x::"'a\<times>'a" assume "x \<in> s O d^-1" then obtain p q z where "(p,z) : s" and "(z,q) : d^-1" and x:"x = (p,q)" by auto
  from \<open>(p,z) : s\<close> obtain k  u v  where kp:"k\<parallel>p" and kz:"k\<parallel>z" and pu:"p\<parallel>u" and uv:"u\<parallel>v"  and zv:"z\<parallel>v"  using s by blast
  from \<open>(z,q) : d^-1\<close> obtain l' k' u' v'  where lpq:"l'\<parallel>q" and kplp:"k'\<parallel>l'" and kpz:"k'\<parallel>z" and qup:"q\<parallel>u'" and upvp:"u'\<parallel>v'" and zvp:"z\<parallel>v'"  using d  by blast
  from kp kz kpz have kpp:"k'\<parallel>p" using M1 by auto
  from pu qup  have "p\<parallel>u' \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>u') \<oplus> (\<exists>t. q\<parallel>t \<and> t\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with qup kpp kplp lpq  have "(p,q) \<in> f^-1" using f by blast
        thus ?thesis using x  by auto} 
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where pt:"p\<parallel>t" and tup:"t\<parallel>u'" by auto
        from pt lpq have "p\<parallel>q \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>q) \<oplus> (\<exists>t'. l'\<parallel>t' \<and> t'\<parallel>t))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus "x \<in> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
        proof (elim disjE)
           { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
             thus ?thesis using x m by auto}
           next
           { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
             thus ?thesis using x b by auto}
           next
           { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
             then obtain t' where lptp:"l'\<parallel>t'" and tpt:"t'\<parallel>t" by auto
             with pt tup qup kpp kplp lpq  have "(p,q) \<in> ov" using ov by blast
             thus ?thesis using x by auto}
        qed
        }  
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where "q\<parallel>t" and "t\<parallel>u" by auto
        with pu kpp kplp lpq   have "(p,q) \<in> d^-1" using d by blast
        thus ?thesis using x  by auto}
       qed
qed

lemma csib:"s^-1 O b \<subseteq> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
proof
  fix x::"'a\<times>'a" assume "x \<in> s^-1 O b" then obtain p q z where "(p,z) : s^-1" and "(z,q) : b" and x:"x = (p,q)" by auto
  from \<open>(p,z) : s^-1\<close> obtain k  u v  where kp:"k\<parallel>p" and kz:"k\<parallel>z" and zu:"z\<parallel>u" and uv:"u\<parallel>v"  and pv:"p\<parallel>v"  using s by blast
  from \<open>(z,q) : b\<close> obtain c  where  zc:"z\<parallel>c" and cq:"c\<parallel>q"  using b by blast
  from kz zc cq obtain zc where kzc:"k\<parallel>zc" and zcq:"zc\<parallel>q" using M5exist_var by blast
  obtain v' where qvp:"q\<parallel>v'" using M3 meets_wd cq by blast
  from pv qvp  have "p\<parallel>v' \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>v') \<oplus> (\<exists>t. q\<parallel>t \<and> t\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with qvp kp kzc zcq  have "(p,q) \<in> f^-1" using f by blast
        thus ?thesis using x  by auto} 
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where pt:"p\<parallel>t" and tvp:"t\<parallel>v'" by auto
        from pt cq have "p\<parallel>q \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>q) \<oplus> (\<exists>t'. c\<parallel>t' \<and> t'\<parallel>t))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus "x \<in> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
        proof (elim disjE)
           { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
             thus ?thesis using x m by auto}
           next
           { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
             thus ?thesis using x b by auto}
           next
           { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
             then obtain t' where ctp:"c\<parallel>t'" and tpt:"t'\<parallel>t" by auto
             from zcq cq ctp have "zc\<parallel>t'" using M1 by auto
             with zcq  pt tvp qvp kzc kp ctp tpt have "(p,q) \<in> ov" using ov by blast
             thus ?thesis using x by auto}
        qed
        }  
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where "q\<parallel>t" and "t\<parallel>v" by auto
        with pv kp kzc zcq   have "(p,q) \<in> d^-1" using d by blast
        thus ?thesis using x  by auto}
       qed
qed

lemma covib:"ov^-1 O b \<subseteq> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
proof
  fix x::"'a\<times>'a" assume "x \<in> ov^-1 O b" then obtain p q z where "(p,z) : ov^-1" and "(z,q) : b" and x:"x = (p,q)" by auto
  from \<open>(p,z) : ov^-1\<close> obtain k l u v c  where kz:"k\<parallel>z" and kl:"k\<parallel>l" and lp:"l\<parallel>p" and zu:"z\<parallel>u" and uv:"u\<parallel>v"  and pv:"p\<parallel>v" and lc:"l\<parallel>c" and cu:"c\<parallel>u" using ov by blast
  from \<open>(z,q) : b\<close> obtain w  where  zw:"z\<parallel>w" and wq:"w\<parallel>q"  using b by blast
  from cu zu zw have cw:"c\<parallel>w" using M1 by auto
  with lc wq obtain cw where lcw:"l\<parallel>cw" and cwq:"cw\<parallel>q" using M5exist_var by blast
  obtain v' where qvp:"q\<parallel>v'" using M3 meets_wd wq by blast
  from pv qvp  have "p\<parallel>v' \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>v') \<oplus> (\<exists>t. q\<parallel>t \<and> t\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with qvp lp lcw cwq  have "(p,q) \<in> f^-1" using f by blast
        thus ?thesis using x  by auto} 
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where pt:"p\<parallel>t" and tvp:"t\<parallel>v'" by auto
        from pt wq have "p\<parallel>q \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>q) \<oplus> (\<exists>t'. w\<parallel>t' \<and> t'\<parallel>t))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus "x \<in> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
        proof (elim disjE)
           { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
             thus ?thesis using x m by auto}
           next
           { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
             thus ?thesis using x b by auto}
           next
           { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
             then obtain t' where wtp:"w\<parallel>t'" and tpt:"t'\<parallel>t" by auto
             moreover with wq cwq have "cw\<parallel>t'" using M1 by auto
             ultimately have "(p,q) \<in> ov" using ov cwq lp lcw pt tvp qvp by blast
             thus ?thesis using x by auto}
        qed
        }  
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where "q\<parallel>t" and "t\<parallel>v" by auto
        with pv lp lcw cwq  have "(p,q) \<in> d^-1" using d by blast
        thus ?thesis using x  by auto}
       qed
qed

lemma cmib:"m^-1 O b \<subseteq> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
proof
  fix x::"'a\<times>'a" assume "x \<in> m^-1 O b" then obtain p q z where "(p,z) : m^-1" and "(z,q) : b" and x:"x = (p,q)" by auto
  from \<open>(p,z) : m^-1\<close> have zp:"z\<parallel>p" using m by auto
  from \<open>(z,q) : b\<close> obtain w  where  zw:"z\<parallel>w" and wq:"w\<parallel>q"  using b by blast
  obtain v where pv:"p\<parallel>v" using M3 meets_wd zp  by blast
  obtain v' where qvp:"q\<parallel>v'" using M3 meets_wd wq by blast

  from pv qvp  have "p\<parallel>v' \<oplus> ((\<exists>t. p\<parallel>t \<and> t\<parallel>v') \<oplus> (\<exists>t. q\<parallel>t \<and> t\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
        with zp zw wq qvp  have "(p,q) \<in> f^-1" using f by blast
        thus ?thesis using x  by auto} 
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp 
        then obtain t where pt:"p\<parallel>t" and tvp:"t\<parallel>v'" by auto
        from pt wq have "p\<parallel>q \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>q) \<oplus> (\<exists>t'. w\<parallel>t' \<and> t'\<parallel>t))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus "x \<in> b \<union> m \<union> ov \<union> f^-1 \<union> d^-1"
        proof (elim disjE)
           { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
             thus ?thesis using x m by auto}
           next
           { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
             thus ?thesis using x b by auto}
           next
           { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
             then obtain t' where wtp:"w\<parallel>t'" and tpt:"t'\<parallel>t" by auto
             with zp zw wq pt tvp qvp have "(p,q) \<in> ov" using ov  by blast
             thus ?thesis using x by auto}
        qed
        }  
      next
      { assume "\<not>?A \<and> \<not>?B \<and> ?C" then have ?C by simp
        then obtain t where "q\<parallel>t" and "t\<parallel>v" by auto
        with zp zw wq pv   have "(p,q) \<in> d^-1" using d by blast
        thus ?thesis using x  by auto}
       qed
qed

(*==========$\gamma$ composition =======*)
subsection \<open>$\gamma$-composition\<close>
text \<open>We prove compositions of the form $r_1 \circ r_2 \subseteq ov \cup s \cup d \cup f \cup e \cup f^{-1} \cup d^{-1} \cup s^{-1} \cup ov^{-1}$.\<close>

lemma covovi:"ov O ov^-1 \<subseteq> e \<union> ov \<union> ov^-1 \<union> d \<union> d^-1 \<union> s \<union> s^-1 \<union> f \<union> f^-1 "
proof
  fix x::"'a\<times>'a" assume "x \<in> ov O ov^-1" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> ov" and "(z, q) \<in> ov^-1" by auto
  from \<open>(p,z) \<in> ov\<close> obtain k l c u  where kp:"k\<parallel>p" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and lc:"l\<parallel>c" and pu:"p\<parallel>u" and cu:"c\<parallel>u"  using ov by blast
  from \<open>(z,q) \<in> ov^-1\<close> obtain k' l' c' u'  where kpq:"k'\<parallel>q" and kplp:"k'\<parallel>l'" and lpz:"l'\<parallel>z" and lpcp:"l'\<parallel>c'" and qup:"q\<parallel>u'" and cpup:"c'\<parallel>u'"  using ov by blast

  from kp kpq  have "k\<parallel>q \<oplus> ((\<exists>t. k\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> e \<union> ov \<union> ov^-1 \<union> d \<union> d^-1 \<union> s \<union> s^-1 \<union> f \<union> f^-1"
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have kq:?A by simp
        from pu qup have "p\<parallel>u' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>u') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
            with kq kp qup have "p = q" using M4 by auto
            thus ?thesis using x e by auto}
          next
          { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
            with kq kp qup show ?thesis using x s by blast}
          next
          { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
            with kq kp pu show ?thesis using x s by blast}
        qed}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
        then obtain t where kt:"k\<parallel>t" and tq:"t\<parallel>q" by auto
        from pu qup have "p\<parallel>u' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>u') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
            with qup kp kt tq  show ?thesis using x f  by blast}
          next
          { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
            then obtain t' where ptp:"p\<parallel>t'" and tpup:"t'\<parallel>u'" by auto
            from tq kpq kplp have "t\<parallel>l'" using M1 by auto
            moreover with lpz lz lc have "l'\<parallel>c" using M1 by auto
            moreover with cu pu ptp have "c\<parallel>t'" using M1 by auto
            ultimately obtain lc where "t\<parallel>lc" and "lc\<parallel>t'" using M5exist_var by blast
            with ptp tpup kp kt tq qup  show ?thesis using x ov by blast}
          next
          { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
            with pu kp kt tq  show ?thesis using x d  by blast}

        qed}
      next
      {assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by auto
       then obtain t where kpt:"k'\<parallel>t" and tp:"t\<parallel>p" by auto
        from pu qup have "p\<parallel>u' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>u') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
            with kpq kpt tp qup show ?thesis using x f  by blast}
          next
          { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
            then obtain t' where "p\<parallel>t'" and "t'\<parallel>u'" by auto
            with  kpq kpt tp qup show ?thesis using x d by blast}
          next
          { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
            then obtain t' where qtp:"q\<parallel>t'" and tpu:"t'\<parallel>u" by auto
            from tp kp kl have "t\<parallel>l" using M1 by auto
            moreover with lpcp lpz lz have "l\<parallel>c'" using M1 by auto
            moreover with cpup qup qtp have "c'\<parallel>t'" using M1 by auto
            ultimately obtain lc where "t\<parallel>lc" and "lc\<parallel>t'" using M5exist_var by blast
            with kpt tp kpq qtp tpu pu show ?thesis using x ov by blast}
          qed}
      qed
qed


lemma cdid:"d^-1 O d \<subseteq> e \<union> ov \<union> ov^-1 \<union> d \<union> d^-1 \<union> s \<union> s^-1 \<union> f \<union> f^-1 "
proof
  fix x::"'a\<times>'a" assume "x \<in> d^-1 O d" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> d^-1" and "(z, q) \<in> d" by auto
  from \<open>(p,z) \<in> d^-1\<close> obtain k l u v where kp:"k\<parallel>p" and kl:"k\<parallel>l" and lz:"l\<parallel>z" and pv:"p\<parallel>v" and zu:"z\<parallel>u" and uv:"u\<parallel>v"  using d by blast
  from \<open>(z,q) \<in> d\<close> obtain k' l'  u' v'  where kpq:"k'\<parallel>q" and kplp:"k'\<parallel>l'" and lpz:"l'\<parallel>z"  and qvp:"q\<parallel>v'" and zup:"z\<parallel>u'" and upvp:"u'\<parallel>v'"  using d by blast

  from kp kpq  have "k\<parallel>q \<oplus> ((\<exists>t. k\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> e \<union> ov \<union> ov^-1 \<union> d \<union> d^-1 \<union> s \<union> s^-1 \<union> f \<union> f^-1"
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have kq:?A by simp
        from pv qvp have "p\<parallel>v' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>v') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
            with kq kp qvp have "p = q" using M4 by auto
            thus ?thesis using x e by auto}
          next
          { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
            with kq kp qvp show ?thesis using x s by blast}
          next
          { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
            with kq kp pv show ?thesis using x s by blast}
        qed}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
        then obtain t where kt:"k\<parallel>t" and tq:"t\<parallel>q" by auto
        from pv qvp have "p\<parallel>v' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>v') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
            with qvp kp kt tq  show ?thesis using x f  by blast}
          next
          { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
            then obtain t' where ptp:"p\<parallel>t'" and tpvp:"t'\<parallel>v'" by auto
            from tq kpq kplp have "t\<parallel>l'" using M1 by auto
            moreover with ptp pv uv have "u\<parallel>t'" using M1 by auto
            moreover with lpz zu \<open>t\<parallel>l'\<close> obtain lzu where "t\<parallel>lzu" and "lzu\<parallel>t'" using  M5exist_var   by blast
            ultimately  show ?thesis using x ov kt tq kp ptp tpvp qvp by blast}
          next
          { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
            with pv kp kt tq  show ?thesis using x d  by blast}

        qed}
      next
      {assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by auto
       then obtain t where kpt:"k'\<parallel>t" and tp:"t\<parallel>p" by auto
        from pv qvp have "p\<parallel>v' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>v') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
            with kpq kpt tp qvp show ?thesis using x f  by blast}
          next
          { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
            then obtain t' where "p\<parallel>t'" and "t'\<parallel>v'" by auto
            with  kpq kpt tp qvp show ?thesis using x d by blast}
          next
          { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
            then obtain t' where qtp:"q\<parallel>t'" and tpv:"t'\<parallel>v" by auto
            from tp kp kl have "t\<parallel>l" using M1 by auto
            moreover with qtp qvp upvp have "u'\<parallel>t'" using M1 by auto
            moreover with lz zup \<open>t\<parallel>l\<close> obtain lzu where "t\<parallel>lzu" and "lzu\<parallel>t'" using  M5exist_var by blast
            ultimately show ?thesis using x ov kpt tp kpq qtp tpv pv  by blast}
          qed}
      qed
qed

lemma coviov:"ov^-1 O ov \<subseteq> e \<union> ov \<union> ov^-1 \<union> d \<union> d^-1 \<union> s \<union> s^-1 \<union> f \<union> f^-1"
proof
  fix x::"'a\<times>'a" assume "x \<in> ov^-1 O ov" then obtain p q z where x:"x = (p,q)" and "(p,z) \<in> ov^-1" and "(z, q) \<in> ov" by auto
  from \<open>(p,z) \<in> ov^-1\<close> obtain k l c u v where kz:"k\<parallel>z" and kl:"k\<parallel>l" and lp:"l\<parallel>p" and lc:"l\<parallel>c" and zu:"z\<parallel>u" and pv:"p\<parallel>v" and cu:"c\<parallel>u" and uv:"u\<parallel>v"  using ov by blast
  from \<open>(z,q) \<in> ov\<close> obtain k' l' c' u' v' where kpz:"k'\<parallel>z" and kplp:"k'\<parallel>l'" and lpq:"l'\<parallel>q" and lpcp:"l'\<parallel>c'" and qvp:"q\<parallel>v'" and zup:"z\<parallel>u'" and cpup:"c'\<parallel>u'" and upvp:"u'\<parallel>v'" using ov by blast

  from lp lpq  have "l\<parallel>q \<oplus> ((\<exists>t. l\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. l'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in> e \<union> ov \<union> ov^-1 \<union> d \<union> d^-1 \<union> s \<union> s^-1 \<union> f \<union> f^-1"
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have lq:?A by simp
        from pv qvp have "p\<parallel>v' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>v') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
            with lq lp qvp have "p = q" using M4 by auto
            thus ?thesis using x e by auto}
          next
          { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
            with lq lp qvp show ?thesis using x s by blast}
          next
          { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
            with lq lp pv show ?thesis using x s by blast}
        qed}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
        then obtain t where lt:"l\<parallel>t" and tq:"t\<parallel>q" by auto
        from pv qvp have "p\<parallel>v' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>v') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
            with qvp lp lt tq  show ?thesis using x f  by blast}
          next
          { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
            then obtain t' where ptp:"p\<parallel>t'" and tpvp:"t'\<parallel>v'" by auto
            from tq lpq lpcp have "t\<parallel>c'" using M1 by auto
            moreover with cpup zup zu have "c'\<parallel>u" using M1 by auto
            moreover with ptp pv uv have "u\<parallel>t'" using M1 by auto
            ultimately obtain cu where "t\<parallel>cu" and "cu\<parallel>t'" using M5exist_var by blast
            with lt tq lp ptp tpvp qvp  show ?thesis using x ov by blast}
          next
          { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
            with pv lp lt tq  show ?thesis using x d  by blast}

        qed}
      next
      {assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by auto
       then obtain t where lpt:"l'\<parallel>t" and tp:"t\<parallel>p" by auto
        from pv qvp have "p\<parallel>v' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>v') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>v))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          { assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
            with qvp lpq lpt tp show ?thesis using x f  by blast}
          next
          { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
            then obtain t' where "p\<parallel>t'" and "t'\<parallel>v'" by auto
            with  qvp lpq lpt tp show ?thesis using x d by blast}
          next
          { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
            then obtain t' where qtp:"q\<parallel>t'" and tpv:"t'\<parallel>v" by auto
            from tp lp lc have "t\<parallel>c" using M1 by auto
            moreover with cu zu zup have "c\<parallel>u'" using M1 by auto
            moreover with qtp qvp upvp have "u'\<parallel>t'" using M1 by auto
            ultimately obtain cu where "t\<parallel>cu" and "cu\<parallel>t'" using M5exist_var by blast
            with lpt tp lpq pv qtp tpv show ?thesis using x ov by blast}
          qed}
      qed
qed

(* ===========$\delta$ composition =========*)
subsection \<open>$\gamma$-composition\<close>
text \<open>We prove compositions of the form $r_1 \circ r_2 \subseteq b \cup m \cup ov \cup s \cup d \cup f \cup e \cup f^{-1} \cup d^{-1} \cup s^{-1} \cup ov^{-1} \cup b^{-1} \cup m^{-1}$.\<close>


lemma cbbi:"b O b^-1 \<subseteq> b \<union> b^-1 \<union> m \<union> m^-1 \<union> e \<union> ov \<union> ov^-1 \<union> s \<union> s^-1 \<union> d \<union> d^-1 \<union> f \<union> f^-1" (is "b O b^-1 \<subseteq> ?R")
proof
  fix x::"'a\<times>'a" assume "x \<in> b O b^-1" then obtain p q z::'a where x:"x = (p,q)" and "(p,z) \<in> b" and "(z,q) \<in> b^-1" by auto
  from \<open>(p,z)\<in>b\<close> obtain c where pc:"p\<parallel>c" and "c\<parallel>z" using b  by blast
  from \<open>(z,q) \<in> b^-1\<close> obtain c' where qcp:"q\<parallel>c'" and "c'\<parallel>z" using b  by blast
  obtain k k' where kp:"k\<parallel>p" and kpq:"k'\<parallel>q" using M3 meets_wd pc qcp by fastforce
  then have "k\<parallel>q \<oplus> ((\<exists>t. k\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. k'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in>?R"
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have kq:?A by simp
        from pc qcp have "p\<parallel>c' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>c') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>c))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          {assume "(?A\<and>\<not>?B\<and>\<not>?C)" then have "?A" by simp
           with kp kq qcp have "p = q" using M4 by auto
           thus ?thesis using x e  by auto}
          next
          {assume "\<not>?A\<and>?B\<and>\<not>?C" then have "?B" by simp
           with kq kp qcp show ?thesis using x s by blast}
          next
          {assume "(\<not>?A\<and>\<not>?B\<and>?C)" then have "?C" by simp
           with kq kp pc show ?thesis using x s by blast}
        qed}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
        then obtain t where kt:"k\<parallel>t" and tq:"t\<parallel>q" by auto
        from pc qcp have "p\<parallel>c' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>c') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>c))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
           with kp qcp kt tq show ?thesis using f x by blast}
          next
          {assume "\<not>?A\<and>?B\<and>\<not>?C"  then have ?B by simp
           then obtain t' where ptp:"p\<parallel>t'" and tpcp:"t'\<parallel>c'" by auto
           from pc tq  have "p\<parallel>q \<oplus> ((\<exists>t''. p\<parallel>t'' \<and> t''\<parallel>q) \<oplus> (\<exists>t''. t\<parallel>t'' \<and> t''\<parallel>c))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
           then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
           thus ?thesis
           proof (elim disjE)
              {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
               thus ?thesis using x m by auto}
              next
              {assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
               thus ?thesis using x b by auto}
              next
              { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
                then obtain g where "t\<parallel>g" and "g\<parallel>c" by auto
                moreover with pc ptp have "g\<parallel>t'" using M1 by blast
                ultimately  show ?thesis using x ov kt tq kp ptp tpcp qcp   by blast}
           qed}
         next
          {assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
           then obtain t' where "q\<parallel>t'" and "t'\<parallel>c" by auto
           with kp  kt tq pc show ?thesis using d x by blast}
         qed}
      next
      { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
        then obtain t where kpt:"k'\<parallel>t" and tp:"t\<parallel>p" by auto
        from  pc qcp have "p\<parallel>c' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>c') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>c))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
           with qcp kpt tp kpq show ?thesis using x f by blast}
          next
          {assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
           with qcp kpt tp kpq show ?thesis using x d by blast}
          next
          {assume "\<not>?A\<and>\<not>?B\<and>?C" then obtain t' where qt':"q\<parallel>t'" and tpc:"t'\<parallel>c" by auto
           from qcp tp have "q\<parallel>p \<oplus> ((\<exists>t''. q\<parallel>t'' \<and> t''\<parallel>p) \<oplus> (\<exists>t''. t\<parallel>t'' \<and> t''\<parallel>c'))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
           then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
           thus ?thesis
           proof (elim disjE)
              {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
               thus ?thesis using x m by auto}
              next
              {assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
               thus ?thesis using x b by auto}
              next
              { assume "\<not>?A\<and>\<not>?B\<and>?C" then obtain g where tg:"t\<parallel>g" and "g\<parallel>c'" by auto
                with qcp qt' have "g\<parallel>t'" using M1 by blast
                with qt' tpc pc kpq kpt tp tg show ?thesis using x ov by blast}
          qed}
     qed}
 qed
qed
       


lemma cbib:"b^-1 O b \<subseteq> b \<union> b^-1 \<union> m \<union> m^-1 \<union> e \<union> ov \<union> ov^-1 \<union> s \<union> s^-1 \<union> d \<union> d^-1 \<union> f \<union> f^-1" (is "b^-1 O b \<subseteq> ?R")
proof
  fix x::"'a\<times>'a" assume "x \<in> b^-1 O b" then obtain p q z::'a where x:"x = (p,q)" and "(p,z) \<in> b^-1" and "(z,q) \<in> b" by auto
  from \<open>(p,z)\<in>b^-1\<close> obtain c where zc:"z\<parallel>c" and cp:"c\<parallel>p" using b  by blast
  from \<open>(z,q) \<in> b\<close> obtain c' where zcp:"z\<parallel>c'" and cpq:"c'\<parallel>q" using b  by blast
  obtain u u' where pu:"p\<parallel>u" and qup:"q\<parallel>u'" using M3 meets_wd cp cpq by fastforce
  from cp cpq have "c\<parallel>q \<oplus> ((\<exists>t. c\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. c'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in>?R"
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have cq:?A by simp
        from pu qup have "p\<parallel>u' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>u') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          {assume "(?A\<and>\<not>?B\<and>\<not>?C)" then have "?A" by simp
           with cq cp qup have "p = q" using M4 by auto
           thus ?thesis using x e  by auto}
          next
          {assume "\<not>?A\<and>?B\<and>\<not>?C" then have "?B" by simp
           with cq cp qup show ?thesis using x s by blast}
          next
          {assume "(\<not>?A\<and>\<not>?B\<and>?C)" then have "?C" by simp
           with pu cq cp show ?thesis using x s by blast}
        qed}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
        then obtain t where ct:"c\<parallel>t" and tq:"t\<parallel>q" by auto
        from pu qup have "p\<parallel>u' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>u') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
           with qup ct tq cp show ?thesis using f x by blast}
          next
          {assume "\<not>?A\<and>?B\<and>\<not>?C"  then have ?B by simp
           then obtain t' where ptp:"p\<parallel>t'" and tpup:"t'\<parallel>u'" by auto
           from pu tq  have "p\<parallel>q \<oplus> ((\<exists>t''. p\<parallel>t'' \<and> t''\<parallel>q) \<oplus> (\<exists>t''. t\<parallel>t'' \<and> t''\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
           then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
           thus ?thesis
           proof (elim disjE)
              {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
               thus ?thesis using x m by auto}
              next
              {assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
               thus ?thesis using x b by auto}
              next
              { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
                then obtain g where "t\<parallel>g" and "g\<parallel>u" by auto
                moreover with pu ptp have "g\<parallel>t'" using M1 by blast
                ultimately  show ?thesis using x ov ct tq cp ptp tpup qup   by blast}
           qed}
         next
          {assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
           then obtain t' where "q\<parallel>t'" and "t'\<parallel>u" by auto
           with cp  ct tq pu  show ?thesis using d x by blast}
         qed}
      next
      { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
        then obtain t where cpt:"c'\<parallel>t" and tp:"t\<parallel>p" by auto
        from  pu qup have "p\<parallel>u' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>u') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
           with qup cpt tp cpq show ?thesis using x f by blast}
          next
          {assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
           with qup cpt tp cpq show ?thesis using x d by blast}
          next
          {assume "\<not>?A\<and>\<not>?B\<and>?C" then obtain t' where qt':"q\<parallel>t'" and tpc:"t'\<parallel>u" by auto
           from qup tp have "q\<parallel>p \<oplus> ((\<exists>t''. q\<parallel>t'' \<and> t''\<parallel>p) \<oplus> (\<exists>t''. t\<parallel>t'' \<and> t''\<parallel>u'))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
           then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
           thus ?thesis
           proof (elim disjE)
              {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
               thus ?thesis using x m by auto}
              next
              {assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
               thus ?thesis using x b by auto}
              next
              { assume "\<not>?A\<and>\<not>?B\<and>?C" then obtain g where tg:"t\<parallel>g" and "g\<parallel>u'" by auto
                with qup qt' have "g\<parallel>t'" using M1 by blast
                with qt' tpc pu cpq cpt tp tg show ?thesis using x ov by blast}
          qed}
     qed}
 qed
qed

lemma cddi:"d O d^-1 \<subseteq> b \<union> b^-1 \<union> m \<union> m^-1 \<union> e \<union> ov \<union> ov^-1 \<union> s \<union> s^-1 \<union> d \<union> d^-1 \<union> f \<union> f^-1" (is "d O d^-1 \<subseteq> ?R")
proof
  fix x::"'a\<times>'a" assume "x \<in> d O d^-1" then obtain p q z::'a where x:"x = (p,q)" and "(p,z) \<in> d" and "(z,q) \<in> d^-1" by auto
  from \<open>(p,z) \<in> d\<close> obtain k l u v where lp:"l\<parallel>p" and kl:"k\<parallel>l" and kz:"k\<parallel>z" and pu:"p\<parallel>u" and uv:"u\<parallel>v" and zv:"z\<parallel>v"  using d  by blast
  from \<open>(z,q) \<in> d^-1\<close> obtain k' l' u' v' where lpq:"l'\<parallel>q" and kplp:"k'\<parallel>l'" and kpz:"k'\<parallel>z" and qup:"q\<parallel>u'" and upvp:"u'\<parallel>v'" and zv':"z\<parallel>v'"  using d  by blast
  from lp lpq have "l\<parallel>q \<oplus> ((\<exists>t. l\<parallel>t \<and> t\<parallel>q) \<oplus> (\<exists>t. l'\<parallel>t \<and> t\<parallel>p))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
  then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
  thus "x \<in>?R"
  proof (elim disjE)
      { assume "?A\<and>\<not>?B\<and>\<not>?C" then have lq:?A by simp
        from pu qup have "p\<parallel>u' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>u') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          {assume "(?A\<and>\<not>?B\<and>\<not>?C)" then have "?A" by simp
           with lq lp qup have "p = q" using M4 by auto
           thus ?thesis using x e  by auto}
          next
          {assume "\<not>?A\<and>?B\<and>\<not>?C" then have "?B" by simp
           with lq lp qup show ?thesis using x s by blast}
          next
          {assume "(\<not>?A\<and>\<not>?B\<and>?C)" then have "?C" by simp
           with pu lq lp show ?thesis using x s by blast}
        qed}
      next
      { assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
        then obtain t where lt:"l\<parallel>t" and tq:"t\<parallel>q" by auto
        from pu qup have "p\<parallel>u' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>u') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
           with qup lt tq lp show ?thesis using f x by blast}
          next
          {assume "\<not>?A\<and>?B\<and>\<not>?C"  then have ?B by simp
           then obtain t' where ptp:"p\<parallel>t'" and tpup:"t'\<parallel>u'" by auto
           from pu tq  have "p\<parallel>q \<oplus> ((\<exists>t''. p\<parallel>t'' \<and> t''\<parallel>q) \<oplus> (\<exists>t''. t\<parallel>t'' \<and> t''\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
           then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
           thus ?thesis
           proof (elim disjE)
              {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
               thus ?thesis using x m by auto}
              next
              {assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
               thus ?thesis using x b by auto}
              next
              { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
                then obtain g where "t\<parallel>g" and "g\<parallel>u" by auto
                moreover with pu ptp have "g\<parallel>t'" using M1 by blast
                ultimately  show ?thesis using x ov lt tq lp ptp tpup qup by blast}
           qed}
         next
          {assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
           then obtain t' where "q\<parallel>t'" and "t'\<parallel>u" by auto
           with lp  lt tq pu  show ?thesis using d x by blast}
         qed}
      next
      { assume "\<not>?A\<and>\<not>?B\<and>?C" then have ?C by simp
        then obtain t where lpt:"l'\<parallel>t" and tp:"t\<parallel>p" by auto
        from  pu qup have "p\<parallel>u' \<oplus> ((\<exists>t'. p\<parallel>t' \<and> t'\<parallel>u') \<oplus> (\<exists>t'. q\<parallel>t' \<and> t'\<parallel>u))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
        then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
        thus ?thesis
        proof (elim disjE)
          {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
           with qup lpt tp lpq show ?thesis using x f by blast}
          next
          {assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
           with qup lpt tp lpq show ?thesis using x d by blast}
          next
          {assume "\<not>?A\<and>\<not>?B\<and>?C" then obtain t' where qt':"q\<parallel>t'" and tpc:"t'\<parallel>u" by auto
           from qup tp have "q\<parallel>p \<oplus> ((\<exists>t''. q\<parallel>t'' \<and> t''\<parallel>p) \<oplus> (\<exists>t''. t\<parallel>t'' \<and> t''\<parallel>u'))" (is "?A \<oplus> (?B \<oplus> ?C)") using M2 by blast
           then have "(?A\<and>\<not>?B\<and>\<not>?C) \<or> ((\<not>?A\<and>?B\<and>\<not>?C) \<or> (\<not>?A\<and>\<not>?B\<and>?C))" by (insert xor_distr_L[of ?A ?B ?C], auto simp:elimmeets)
           thus ?thesis
           proof (elim disjE)
              {assume "?A\<and>\<not>?B\<and>\<not>?C" then have ?A by simp
               thus ?thesis using x m by auto}
              next
              {assume "\<not>?A\<and>?B\<and>\<not>?C" then have ?B by simp
               thus ?thesis using x b by auto}
              next
              { assume "\<not>?A\<and>\<not>?B\<and>?C" then obtain g where tg:"t\<parallel>g" and "g\<parallel>u'" by auto
                with qup qt' have "g\<parallel>t'" using M1 by blast
                with qt' tpc pu lpq lpt tp tg show ?thesis using x ov by blast}
          qed}
     qed}
 qed
qed


(* ========= inverse ========== *)
subsection \<open>The rest of the composition table\<close>
text \<open>Because of the symmetry $(r_1 \circ r_2)^{-1} = r_2^{-1} \circ r_1^{-1} $, the rest of the compositions is easily deduced.\<close>


lemma cmbi:"m O b^-1 \<subseteq> b^-1 \<union> m^-1 \<union> s^-1 \<union> ov^-1 \<union> d^-1"
  using cbmi by auto


lemma covmi:"ov O m^-1 \<subseteq> ov^-1 \<union> d^-1 \<union> s^-1"
  using  cmovi by auto

lemma covbi:"ov O b^-1 \<subseteq> b^-1 \<union> m^-1 \<union> s^-1 \<union> ov^-1 \<union> d^-1"
  using cbovi by auto

lemma cfiovi:"f^-1 O ov^-1 \<subseteq> ov^-1 \<union> s^-1 \<union> d^-1"
  using covf by auto

lemma cfimi:"(f^-1 O m^-1) \<subseteq> s^-1 \<union> ov^-1 \<union> d^-1"
  using cmf by auto

lemma cfibi:"f^-1 O b^-1 \<subseteq> b^-1 \<union> m^-1 \<union> ov^-1 \<union> s^-1 \<union> d^-1"
  using cbf by auto

lemma cdif:"d^-1 O f \<subseteq> ov^-1 \<union> s^-1 \<union> d^-1"
  using cfid by auto

lemma cdiovi:"d^-1 O ov ^-1 \<subseteq> ov^-1 \<union> s^-1 \<union> d^-1"
  using covd by auto

lemma cdimi:"d^-1 O m^-1 \<subseteq> s^-1 \<union> ov^-1 \<union> d^-1 "
  using cmd by auto

lemma cdibi:"d^-1 O b^-1 \<subseteq> b^-1 \<union> m^-1 \<union> ov^-1 \<union> s^-1 \<union> d^-1"
  using cbd by auto 

lemma csd:"s O d \<subseteq> d"
  using cdisi by auto

lemma csf:"s O f \<subseteq> d"
  using cfisi by auto

lemma csovi:"s O ov^-1 \<subseteq> ov^-1 \<union> f \<union> d"
  using covsi by auto

lemma csmi:"s O m^-1 \<subseteq> m^-1"
  using cmsi by auto

lemma csbi:"s O b^-1 \<subseteq> b^-1"
  using cbsi by auto

lemma csisi:"s^-1 O s^-1 \<subseteq> s^-1"
  using css by auto

lemma csid:"s^-1 O d \<subseteq> ov^-1 \<union> f \<union> d"
  using cdis by auto

lemma csif:"s^-1 O f \<subseteq> ov^-1"
  using cfis by auto

lemma csiovi:"s^-1 O ov^-1 \<subseteq> ov^-1"
  using covs by auto

lemma csimi:"s^-1 O m^-1 \<subseteq> m^-1"
  using cms by auto

lemma csibi:"s^-1 O b^-1 \<subseteq> b^-1"
  using cbs by auto

lemma cds:"d O s \<subseteq> d"
  using csidi by auto

lemma cdsi:"d O s^-1 \<subseteq> b^-1 \<union> m^-1 \<union> ov^-1 \<union> f \<union> d"
  using csdi by auto

lemma cdd:"d O d \<subseteq> d"
  using cdidi by auto

lemma cdf:"d O f \<subseteq> d" 
  using cfidi by auto

lemma cdovi:"d O ov^-1 \<subseteq> b^-1 \<union> m^-1 \<union> ov^-1 \<union> f \<union> d"
  using covdi by auto

lemma cdmi:"d O m^-1 \<subseteq> b^-1"
  using cmdi by auto

lemma cdbi:"d O b^-1 \<subseteq> b^-1"
  using cbdi by auto

lemma cfdi:"f O d^-1 \<subseteq>  b^-1 \<union> m^-1 \<union> ov^-1 \<union> s^-1 \<union> d^-1 "
  using cdfi by auto

lemma cfs:"f O s \<subseteq> d"
  using csifi by auto

lemma cfsi:"f O s^-1 \<subseteq> b ^-1 \<union> m^-1 \<union> ov ^-1"
  using csfi by auto

lemma cfd:"f O d \<subseteq> d"
  using cdifi by auto


lemma cff:"f O f \<subseteq> f"
  using cfifi by auto

lemma cfovi:"f O ov^-1 \<subseteq> b^-1 \<union> m^-1 \<union> ov^-1"
  using covfi by auto

lemma cfmi:"f O m^-1 \<subseteq> b^-1"
  using cmfi by auto

lemma cfbi:"f O b^-1 \<subseteq> b^-1"
  using cbfi by auto

lemma covifi:"ov^-1 O f^-1 \<subseteq> ov^-1 \<union> s^-1 \<union> d^-1"
  using cfov by auto

lemma covidi:"ov^-1 O d^-1 \<subseteq> b^-1 \<union> m^-1 \<union> s^-1 \<union> ov^-1 \<union> d^-1"
  using cdov by auto

lemma covis:"ov^-1 O s \<subseteq> ov^-1 \<union> f \<union> d"
  using csiov by auto

lemma covisi:"ov^-1 O s^-1 \<subseteq> b^-1 \<union> m^-1 \<union> ov^-1"
  using csov by auto

lemma covid:"ov^-1 O d \<subseteq> ov^-1 \<union> f \<union> d"
  using cdiov by auto

lemma covif:"ov^-1 O f \<subseteq> ov^-1"
  using cfiov by auto

lemma coviovi:"ov^-1 O ov^-1 \<subseteq> b^-1 \<union> m^-1 \<union> ov^-1"
  using covov by auto

lemma covimi:"ov^-1 O m^-1 \<subseteq> b^-1"
  using cmov by auto

lemma covibi:"ov^-1 O b^-1 \<subseteq> b^-1"
  using cbov by auto

lemma cmiov:"m^-1 O ov \<subseteq> ov^-1 \<union> d \<union> f"
  using covim by auto

lemma cmifi:"m^-1 O f^-1 \<subseteq> m^-1"
  using cfm by auto

lemma cmidi:"m^-1 O d^-1 \<subseteq> b^-1"
  using cdm by auto

lemma cmis:"m^-1 O s \<subseteq> ov^-1 \<union> d \<union> f"
  using csim by auto

lemma cmisi:"m^-1 O s^-1 \<subseteq> b^-1"
  using csm by auto

lemma cmid:"m^-1 O d \<subseteq> ov^-1 \<union> d \<union> f"
  using cdim by auto

lemma cmif:"m^-1 O f \<subseteq> m^-1"
  using cfim by auto

lemma cmiovi:"m^-1 O ov^-1 \<subseteq> b^-1"
  using covm by auto

lemma cmimi:"m^-1 O m^-1 \<subseteq> b^-1"
  using cmm by auto

lemma cmibi:"m^-1 O b^-1 \<subseteq> b^-1"
  using cbm by auto

lemma cbim:"b^-1 O m \<subseteq> b^-1 \<union> m^-1 \<union> ov^-1 \<union> f \<union> d"
  using cmib by auto

lemma cbiov:"b^-1 O ov \<subseteq> b^-1 \<union> m^-1 \<union> ov^-1 \<union> f \<union> d"
  using covib by auto

lemma cbifi:"b^-1 O f^-1 \<subseteq> b^-1"
  using cfb by auto

lemma cbidi:"b^-1 O d^-1 \<subseteq> b^-1"
  using cdb by auto

lemma cbis:"b^-1 O s \<subseteq> b^-1 \<union> m^-1 \<union> ov^-1 \<union> f \<union> d"
  using csib by auto

lemma cbisi:"b^-1 O s^-1 \<subseteq> b^-1"
  using csb by auto

lemma cbid:"b^-1 O d  \<subseteq> b^-1 \<union> m^-1 \<union> ov^-1 \<union> f \<union> d"
  using cdib by auto

lemma cbif:"b^-1 O f \<subseteq> b^-1"
  using cfib by auto

lemma cbiovi:"b^-1 O ov^-1 \<subseteq> b^-1"
  using covb by auto

lemma cbimi:"b^-1 O m^-1 \<subseteq> b^-1"
  using cmb by auto

lemma cbibi:"b^-1 O b^-1 \<subseteq> b^-1"
  using cbb by auto 

(****)

subsection \<open>Composition rules\<close> 
named_theorems ce_rules declare cem[ce_rules] and ceb[ce_rules] and ceov[ce_rules] and ces[ce_rules] and cef[ce_rules] and ced[ce_rules] and 
cemi[ce_rules] and cebi[ce_rules] and ceovi[ce_rules] and cesi[ce_rules] and cefi[ce_rules] and cedi[ce_rules]

named_theorems cm_rules declare cme[cm_rules] and cmb[cm_rules] and cmm[cm_rules] and cmov[cm_rules] and cms [cm_rules] and cmd[cm_rules] and cmf[cm_rules] and
cmbi[cm_rules] and cmmi[cm_rules] and cmovi[cm_rules] and cmsi[cm_rules] and cmdi[cm_rules] and cmfi[cm_rules]

named_theorems cb_rules declare cbe[cb_rules] and cbm[cb_rules] and cbb[cb_rules] and cbov[cb_rules] and cbs [cb_rules] and cbd[cb_rules] and cbf[cb_rules] and
cbbi[cb_rules] and cbbi[cb_rules] and cbovi[cb_rules] and cbsi[cb_rules] and cbdi[cb_rules] and cbfi[cb_rules]

named_theorems cov_rules declare cove[cov_rules] and covb[cov_rules] and covb[cov_rules] and covov[cov_rules] and covs [cov_rules] and covd[cov_rules] and covf[cov_rules] and
covbi[cov_rules] and covbi[cov_rules] and covovi[cov_rules] and covsi[cov_rules] and covdi[cov_rules] and covfi[cov_rules]

named_theorems cs_rules declare cse[cs_rules] and csb[cs_rules] and csb[cs_rules] and csov[cs_rules] and css [cs_rules] and csd[cs_rules] and csf[cs_rules] and
csbi[cs_rules] and csbi[cs_rules] and csovi[cs_rules] and cssi[cs_rules] and csdi[cs_rules] and csfi[cs_rules]

named_theorems cf_rules declare cfe[cf_rules] and cfb[cf_rules] and cfb[cf_rules] and cfov[cf_rules] and cfs [cf_rules] and cfd[cf_rules] and cff[cf_rules] and
cfbi[cf_rules] and cfbi[cf_rules] and cfovi[cf_rules] and cfsi[cf_rules] and cfdi[cf_rules] and cffi[cf_rules]

named_theorems cd_rules declare cde[cd_rules] and cdb[cd_rules] and cdb[cd_rules] and cdov[cd_rules] and cds [cd_rules] and cdd[cd_rules] and cdf[cd_rules] and
cdbi[cd_rules] and cdbi[cd_rules] and cdovi[cd_rules] and cdsi[cd_rules] and cddi[cd_rules] and cdfi[cd_rules]

named_theorems cmi_rules declare cmie[cmi_rules] and cmib[cmi_rules] and cmib[cmi_rules] and cmiov[cmi_rules] and cmis [cmi_rules] and cmid[cmi_rules] and cmif[cmi_rules] and
cmibi[cmi_rules] and cmibi[cmi_rules] and cmiovi[cmi_rules] and cmisi[cmi_rules] and cmidi[cmi_rules] and cmifi[cmi_rules]

named_theorems cbi_rules declare cbie[cbi_rules] and cbim[cbi_rules] and cbib[cbi_rules] and cbiov[cbi_rules] and cbis [cbi_rules] and cbid[cbi_rules] and cbif[cbi_rules] and
cbimi[cbi_rules] and cbibi[cbi_rules] and cbiovi[cbi_rules] and cbisi[cbi_rules] and cbidi[cbi_rules] and cbifi[cbi_rules]

named_theorems covi_rules declare covie[covi_rules] and covib[covi_rules] and covib[covi_rules] and coviov[covi_rules] and covis [covi_rules] and covid[covi_rules] and covif[covi_rules] and
covibi[covi_rules] and covibi[covi_rules] and coviovi[covi_rules] and covisi[covi_rules] and covidi[covi_rules] and covifi[covi_rules]

named_theorems csi_rules declare csie[csi_rules] and csib[csi_rules] and csib[csi_rules] and csiov[csi_rules] and csis [csi_rules] and csid[csi_rules] and csif[csi_rules] and
csibi[csi_rules] and csibi[csi_rules] and csiovi[csi_rules] and csisi[csi_rules] and csidi[csi_rules] and csifi[csi_rules]

named_theorems cfi_rules declare cfie[cfi_rules] and cfib[cfi_rules] and cfib[cfi_rules] and cfiov[cfi_rules] and cfis [cfi_rules] and cfid[cfi_rules] and cfif[cfi_rules] and
cfibi[cfi_rules] and cfibi[cfi_rules] and cfiovi[cfi_rules] and cfisi[cfi_rules] and cfidi[cfi_rules] and cfifi[cfi_rules]

named_theorems cdi_rules declare cdie[cdi_rules] and cdib[cdi_rules] and cdib[cdi_rules] and cdiov[cdi_rules] and cdis [cdi_rules] and cdid[cdi_rules] and cdif[cdi_rules] and
cdibi[cdi_rules] and cdibi[cdi_rules] and cdiovi[cdi_rules] and cdisi[cdi_rules] and cdidi[cdi_rules] and cdifi[cdi_rules]
(**)
named_theorems cre_rules declare cee[cre_rules] and cme[cre_rules] and cbe[cre_rules] and cove[cre_rules] and cse[cre_rules] and cfe[cre_rules] and cde[cre_rules] and 
cmie[cre_rules] and cbie[cre_rules] and covie[cre_rules] and csie[cre_rules] and cfie[cre_rules] and cdie[cre_rules]

named_theorems crm_rules declare cem[crm_rules] and cbm[crm_rules] and cmm[crm_rules]  and covm[crm_rules] and csm[crm_rules] and cfm[crm_rules] and cdm[crm_rules] and 
cmim[crm_rules] and cbim[crm_rules] and covim[crm_rules] and csim[crm_rules] and cfim[crm_rules] and cdim[crm_rules]

named_theorems crmi_rules declare cemi[crmi_rules] and cbmi[crmi_rules] and cmmi[crmi_rules]  and covmi[crmi_rules] and csmi[crmi_rules] and cfmi[crmi_rules] and cdmi[crmi_rules] and 
cmimi[crmi_rules] and cbimi[crmi_rules] and covimi[crmi_rules] and csimi[crmi_rules] and cfimi[crmi_rules] and cdimi[crmi_rules]

named_theorems crs_rules declare ces[crs_rules] and cbs[crs_rules] and cms[crs_rules]  and covs[crs_rules] and css[crs_rules] and cfs[crs_rules] and cds[crs_rules] and 
cmis[crs_rules] and cbis[crs_rules] and covis[crs_rules] and csis[crs_rules] and cfis[crs_rules] and cdis[crs_rules]

named_theorems crsi_rules declare cesi[crsi_rules] and cbsi[crsi_rules] and cmsi[crsi_rules]  and covsi[crsi_rules] and cssi[crsi_rules] and cfsi[crsi_rules] and cdsi[crsi_rules] and 
cmisi[crsi_rules] and cbisi[crsi_rules] and covisi[crsi_rules] and csisi[crsi_rules] and cfisi[crsi_rules] and cdisi[crsi_rules]

named_theorems crb_rules declare ceb[crb_rules] and cbb[crb_rules] and cmb[crb_rules]  and covb[crb_rules] and csb[crb_rules] and cfb[crb_rules] and cdb[crb_rules] and 
cmib[crb_rules] and cbib[crb_rules] and covib[crb_rules] and csib[crb_rules] and cfib[crb_rules] and cdib[crb_rules]

named_theorems crbi_rules declare cebi[crbi_rules] and cbbi[crbi_rules] and cmbi[crbi_rules]  and covbi[crbi_rules] and csbi[crbi_rules] and cfbi[crbi_rules] and cdbi[crbi_rules] and 
cmibi[crbi_rules] and cbibi[crbi_rules] and covibi[crbi_rules] and csibi[crbi_rules] and cfibi[crbi_rules] and cdibi[crbi_rules]

named_theorems crov_rules declare ceov[crov_rules] and cbov[crov_rules] and cmov[crov_rules]  and covov[crov_rules] and csov[crov_rules] and cfov[crov_rules] and cdov[crov_rules] and 
cmiov[crov_rules] and cbiov[crov_rules] and coviov[crov_rules] and csiov[crov_rules] and cfiov[crov_rules] and cdiov[crov_rules]

named_theorems crovi_rules declare ceovi[crovi_rules] and cbovi[crovi_rules] and cmovi[crovi_rules]  and covovi[crovi_rules] and csovi[crovi_rules] and cfovi[crovi_rules] and cdovi[crovi_rules] and 
cmiovi[crovi_rules] and cbiovi[crovi_rules] and coviovi[crovi_rules] and csiovi[crovi_rules] and cfiovi[crovi_rules] and cdiovi[crovi_rules]

named_theorems crf_rules declare cef[crf_rules] and cbf[crf_rules] and cmf[crf_rules]  and covf[crf_rules] and csf[crf_rules] and cff[crf_rules] and cdf[crf_rules] and 
cmif[crf_rules] and cbif[crf_rules] and covif[crf_rules] and csif[crf_rules] and cfif[crf_rules] and cdif[crf_rules]

named_theorems crfi_rules declare cefi[crfi_rules] and cbfi[crfi_rules] and cmfi[crfi_rules]  and covfi[crfi_rules] and csfi[crfi_rules] and cffi[crfi_rules] and cdfi[crfi_rules] and 
cmifi[crfi_rules] and cbifi[crfi_rules] and covifi[crfi_rules] and csifi[crfi_rules] and cfifi[crfi_rules] and cdifi[crfi_rules]

named_theorems crd_rules declare ced[crd_rules] and cbd[crd_rules] and cmd[crd_rules]  and covd[crd_rules] and csd[crd_rules] and cfd[crd_rules] and cdd[crd_rules] and 
cmid[crd_rules] and cbid[crd_rules] and covid[crd_rules] and csid[crd_rules] and cfid[crd_rules] and cdid[crd_rules]

named_theorems crdi_rules declare cedi[crdi_rules] and cbdi[crdi_rules] and cmdi[crdi_rules]  and covdi[crdi_rules] and csdi[crdi_rules] and cfdi[crdi_rules] and cddi[crdi_rules] and 
cmidi[crdi_rules] and cbidi[crdi_rules] and covidi[crdi_rules] and csidi[crdi_rules] and cfidi[crdi_rules] and cdidi[crdi_rules]



end
