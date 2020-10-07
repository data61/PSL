(*
   Author: Mike Stannett
   Date: 22 October 2012
   m.stannett@sheffield.ac.uk
   Updated 28 April 2016 to run under Isabelle2016.
*)
theory SpaceTime
imports Main
begin


(* A linordered_field is a field with a linear (total) order 
  INHERITED SYNTAX: 
    linorder: <, \<le>, \<ge>, >
    field: a * b, a / b, inverse a
           a + b, a - b, -a
           0, 1
*)


(*
  A vector has four components
*)
record 'a Vector =
  tdir :: "'a"
  xdir :: "'a"
  ydir :: "'a"
  zdir :: "'a"


(*
  A point has four coordinates.
*)
record 'a Point = 
  tval :: "'a"
  xval :: "'a"
  yval :: "'a"
  zval :: "'a"


(*
  To specify a line, give its local origin ("basepoint") together with its direction.
*)
record 'a Line  =
  basepoint :: "'a Point"
  direction :: "'a Vector"


(*
  To specify a plane, give its local origin ("pbasepoint") together with two basis vectors
*)
record 'a Plane =
  pbasepoint :: "'a Point"
  direction1 :: "'a Vector"
  direction2 :: "'a Vector"

(*
  To specify an upright cone, give its vertex and slope.
*)
record 'a Cone =
  vertex :: "'a Point"
  slope  :: "'a"


(*
  The set of quantities is assumed to be an ordered field. We shall
  sometimes need to assume that the field is also Euclidean, ie
  square roots exists, but this is not a general requirement so it
  will be added as a separate axiom class later.
*)
class Quantities = linordered_field


(*
  Vectors are defined over the field of quantities
*)
class Vectors = Quantities
begin

  abbreviation  vecZero :: "'a Vector" ("0") where
    "vecZero \<equiv> \<lparr> tdir = (0::'a), xdir = 0, ydir = 0, zdir = 0 \<rparr>"

  fun vecPlus :: "'a Vector \<Rightarrow> 'a Vector \<Rightarrow> 'a Vector" (infixr "\<oplus>" 100) where
    "vecPlus u v = \<lparr> tdir = tdir u + tdir v, xdir = xdir u + xdir v, 
                     ydir = ydir u + ydir v, zdir = zdir u + zdir v \<rparr>"

  fun vecMinus :: "'a Vector \<Rightarrow> 'a Vector \<Rightarrow> 'a Vector" (infixr "\<ominus>" 100) where
    "vecMinus u v = \<lparr> tdir = tdir u - tdir v, xdir = xdir u - xdir v, 
                      ydir = ydir u - ydir v, zdir = zdir u - zdir v \<rparr>"

  fun vecNegate :: "'a Vector \<Rightarrow> 'a Vector" ("~ _") where
    "vecNegate u = \<lparr> tdir = uminus (tdir u), xdir = uminus (xdir u), 
                     ydir = uminus (ydir u), zdir = uminus (zdir u) \<rparr>"

  fun innerProd :: "'a Vector \<Rightarrow> 'a Vector \<Rightarrow> 'a" (infix "dot" 50) where
    "innerProd u v = (tdir u * tdir v) + (xdir u * xdir v) + 
                     (ydir u * ydir v) + (zdir u * zdir v)"

  fun sqrlen :: "'a Vector \<Rightarrow> 'a"  where "sqrlen u = (u dot u)"

  fun minkowskiProd :: "'a Vector \<Rightarrow> 'a Vector \<Rightarrow> 'a" (infix "mdot" 50) where
    "minkowskiProd u v = (tdir u * tdir v) 
                       -  ((xdir u * xdir v) + (ydir u * ydir v) + (zdir u * zdir v))"

  fun mSqrLen :: "'a Vector \<Rightarrow>  'a"  where "mSqrLen u = (u mdot u)"

  fun vecScale  :: "'a \<Rightarrow> 'a Vector \<Rightarrow> 'a Vector" (infix "**" 200)  where
    "vecScale k u = \<lparr> tdir = k * tdir u, xdir = k * xdir u, ydir = k * ydir u, zdir = k * zdir u \<rparr>"

  fun orthogonal :: "'a Vector \<Rightarrow> 'a Vector \<Rightarrow> bool" (infix "\<bottom>" 150) where
    "orthogonal u v = (u dot v = 0)"

(*
  vector addition and subtraction do what's expected
*)

lemma lemVecZeroMinus:
  shows "0 \<ominus> u = ~ u"
  by simp

lemma lemVecSelfMinus:
  shows "u \<ominus> u = 0"
  by simp

lemma lemVecPlusCommute:
  shows "u \<oplus> v = v \<oplus> u"
  by (simp add: add.commute)

lemma lemVecPlusAssoc:
  shows "u \<oplus> (v \<oplus> w) = (u \<oplus> v) \<oplus> w"
  by (simp add: add.assoc)

lemma lemVecPlusMinus:
  shows "u \<oplus> (~ v)  = u \<ominus> v"
  by (simp add: local.add_uminus_conv_diff)


(*
  Dot product commutes.
*)
lemma lemDotCommute: 
  shows "(u dot v) = (v dot u)"
  by (simp add: mult.commute)


(*
  Minkowski product commutes.
*)
lemma lemMDotCommute: 
  shows "(u mdot v) = (v mdot u)"
  by (simp add:mult.commute)


(* Scaling can be done in stages *)
lemma lemScaleScale:
  shows "a**(b**u) = (a*b)**u"
  by (simp add: mult.assoc)



(* Scaling by 1 has no effect *)
lemma lemScale1:
  shows "1 ** u = u"
  by simp



(* Scaling by 0 gives the null vector *)
lemma lemScale0:
  shows "0 ** u = 0"
  by simp



(* Scaling by a negative value reverses *)
lemma lemScaleNeg:
  shows "(-k)**u = ~ (k**u)"
  by simp



(* The null vector is invariant under scaling *)
lemma lemScaleOrigin:
  shows "k**0 = 0" 
  by auto



(* Scaling distributes over addition *)
lemma lemScaleOverAdd:
  shows "k**(u \<oplus> v) = k**u \<oplus> k**v"
  by (simp add: semiring_normalization_rules(34))

lemma lemAddOverScale: 
  shows "a**u \<oplus> b**u = (a+b)**u"
  by (simp add: semiring_normalization_rules(1))


(* Scaling can be reversed *)
lemma lemScaleInverse:
  assumes "k \<noteq> (0::'a)"
    and   "v = k**u"
  shows   "u = (inverse k)**v"
proof -
  have "(inverse k)**v = (inverse k * k)**u"
    by (simp add: lemScaleScale assms(2) mult.assoc)
  thus ?thesis by (metis (lifting) field_inverse assms(1) lemScale1) 
qed
 


(* Being orthogonal is mutual *)
lemma lemOrthoSym:
  assumes "u \<bottom> v"
  shows "v \<bottom> u"
  by (metis assms(1) lemDotCommute orthogonal.simps)

end



(*
  Points have coordinates in the field of quantities.
*)
class Points = Quantities + Vectors
begin

  abbreviation origin :: "'a Point" where 
    "origin \<equiv> \<lparr> tval = 0, xval = 0, yval = 0, zval = 0 \<rparr>"

  fun vectorJoining :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> 'a Vector" ("from _ to _") where
    "vectorJoining p q
      = \<lparr> tdir = tval q - tval p, xdir = xval q - xval p, 
          ydir = yval q - yval p, zdir = zval q - zval p \<rparr>"

  fun moveBy :: "'a Point \<Rightarrow> 'a Vector \<Rightarrow> 'a Point" (infixl "\<leadsto>" 100) where
    "moveBy p u 
      = \<lparr> tval = tval p + tdir u, xval = xval p + xdir u, 
          yval = yval p + ydir u, zval = zval p + zdir u \<rparr>"

  fun positionVector :: "'a Point \<Rightarrow> 'a Vector" where
    "positionVector p = \<lparr> tdir = tval p, xdir = xval p, ydir = yval p, zdir = zval p \<rparr>"

  fun before :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> bool" (infixr "\<lesssim>" 100) where
    "before p q = (tval p < tval q)"

  fun after :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> bool" (infixr "\<greatersim>" 100) where
    "after p q = (tval p > tval q)"

  fun sametime :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> bool" (infixr "\<approx>" 100) where
    "sametime p q = (tval p = tval q)"

  lemma lemFromToTo: 
    shows "(from p to q) \<oplus> (from q to r) = (from p to r)"
  proof -
    have shared: "\<forall>valp valq valr.( valq - valp + (valr - valq) = valr - valp)" 
      by (metis add_uminus_conv_diff add_diff_cancel 
                semiring_normalization_rules(24) semiring_normalization_rules(25))
    thus ?thesis by auto
  qed

  lemma lemMoveByMove: 
    shows "p \<leadsto> u \<leadsto> v = p \<leadsto> (u \<oplus> v)"
    by (simp add: add.assoc)

  lemma lemScaleLinear: 
    shows "p \<leadsto> a**u \<leadsto> b**v = p \<leadsto> (a**u \<oplus> b**v)"
  by (simp add: add.assoc)

end


(*
  Lines are defined using a basepoint and a direction.
*)
class Lines = Quantities + Vectors + Points
begin

  fun onAxisT :: "'a Point \<Rightarrow> bool" where
     "onAxisT u = ((xval u = 0) \<and> (yval u = 0) \<and> (zval u = 0))"

  fun space2 :: "('a Point) \<Rightarrow> ('a Point) \<Rightarrow> 'a" where
    "space2 u v 
      = (xval u - xval v)*(xval u - xval v) 
      + (yval u - yval v)*(yval u - yval v) 
      + (zval u - zval v)*(zval u - zval v)"

  fun time2 :: "('a Point) \<Rightarrow> ('a Point) \<Rightarrow> 'a" where
    "time2 u v = (tval u - tval v)*(tval u - tval v)"

  fun speed :: "('a Point) \<Rightarrow> ('a Point) \<Rightarrow> 'a" where
    "speed u v = (space2 u v /  time2 u v)"

  fun mkLine :: "'a Point => 'a Vector \<Rightarrow> 'a Line" where
    "mkLine b d = \<lparr> basepoint = b, direction = d \<rparr>"

  fun lineJoining :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> 'a Line" ("line joining _ to _") where
    "lineJoining p q = \<lparr> basepoint = p, direction = from p to q \<rparr>"

  fun parallel :: "'a Line \<Rightarrow> 'a Line \<Rightarrow> bool" ("_ \<parallel> ") where
    "parallel lineA lineB = ((direction lineA = vecZero) \<or> (direction lineB = vecZero) 
                                   \<or> (\<exists>k.(k \<noteq> (0::'a) \<and> direction lineB = k**direction lineA)))"

  fun collinear :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> 'a Point \<Rightarrow> bool" where
    "collinear p q r = (\<exists>\<alpha> \<beta>. ( (\<alpha> + \<beta> = 1)  \<and>
            positionVector p = \<alpha>**(positionVector q) \<oplus> \<beta>**(positionVector r) ))"

  fun inLine :: "'a Point \<Rightarrow> 'a Line \<Rightarrow> bool" where
    "inLine p l = collinear p (basepoint l) (basepoint l \<leadsto> direction l)"

  fun meets :: "'a Line \<Rightarrow> 'a Line \<Rightarrow> bool" where
    "meets line1 line2 = (\<exists>p.(inLine p line1 \<and> inLine p line2))"


  lemma lemParallelReflexive: 
    shows "lineA \<parallel> lineA"
  proof -
    define dir where "dir = direction lineA"
    have "(1 \<noteq> 0) \<and> (dir = 1**dir)" by simp
    thus ?thesis by (metis dir_def parallel.simps)
  qed


  lemma lemParallelSym: 
    assumes "lineA \<parallel> lineB"
    shows   "lineB \<parallel> lineA"
  proof -
    have case1: "direction lineA = vecZero \<longrightarrow> ?thesis" by auto
    have case2: "direction lineB = vecZero \<longrightarrow> ?thesis" by auto
    {
      assume case3: "direction lineA \<noteq> vecZero \<and> direction lineB \<noteq> vecZero"
      have exists_kab: "\<exists>kab.(kab \<noteq> (0::'a) \<and> direction lineB = kab**direction lineA)" 
        by (metis parallel.simps assms(1) case3)
      define kab where "kab \<equiv> (SOME kab.(kab \<noteq> (0::'a) \<and> direction lineB = kab**direction lineA))"
      have kab_props: "kab \<noteq> 0 \<and> direction lineB = kab**direction lineA"
        using exists_kab kab_def 
        by (rule Hilbert_Choice.exE_some)

      define kba where "kba = inverse kab"
      have kba_nonzero: "kba \<noteq> 0" by (metis inverse_zero_imp_zero kab_props kba_def)
      have "direction lineA = kba**direction lineB" by (metis kba_def lemScaleInverse kab_props)
      hence ?thesis by (metis kba_nonzero parallel.simps)
    }
    from this have "(direction lineA \<noteq> vecZero \<and> direction lineB \<noteq> vecZero) \<longrightarrow> ?thesis" by blast

    thus ?thesis by (metis case1 case2)
  qed


  lemma lemParallelTrans: 
    assumes "lineA \<parallel> lineB"
      and   "lineB \<parallel> lineC"
      and   "direction lineB \<noteq> vecZero"
    shows   "lineA \<parallel> lineC"
  proof -
    have case1: "direction lineA = vecZero \<longrightarrow> ?thesis" by auto
    have case2: "direction lineC = vecZero \<longrightarrow> ?thesis" by auto
    
    {
      assume case3: "direction lineA \<noteq> vecZero \<and> direction lineC \<noteq> vecZero"

      have exists_kab: "\<exists>kab.(kab \<noteq> (0::'a) \<and> direction lineB = kab**direction lineA)" 
        by (metis parallel.simps assms(1) case3 assms(3))
      then obtain kab where kab_props: "kab \<noteq> 0 \<and> direction lineB = kab**direction lineA" by auto

      have exists_kbc: "\<exists>kbc.(kbc \<noteq> (0::'a) \<and> direction lineC = kbc**direction lineB)" 
        by (metis parallel.simps assms(2) case3 assms(3))
      then obtain kbc where kbc_props: "kbc \<noteq> 0 \<and> direction lineC = kbc**direction lineB" by auto

      define kac where "kac = kbc * kab"
      have kac_nonzero: "kac \<noteq> 0" by (metis kab_props kac_def kbc_props no_zero_divisors)
      have "direction lineC = kac**direction lineA" 
        by (metis kab_props kbc_props kac_def lemScaleScale)
      hence ?thesis by (metis kac_nonzero parallel.simps)
    }
    from this have "(direction lineA \<noteq> vecZero \<and> direction lineC \<noteq> vecZero) \<longrightarrow> ?thesis" by blast

    thus ?thesis by (metis case1 case2)
  qed


  lemma (in -) lemLineIdentity: 
    assumes "lineA = \<lparr> basepoint = basepoint lineB, direction = direction lineB \<rparr>"
    shows "lineA = lineB"
  proof -
  have "basepoint lineA = basepoint lineB \<and> direction lineA = direction lineB" 
    by (simp add: assms(1))
  thus ?thesis by simp
  qed


  lemma lemDirectionJoining: 
    shows "vectorJoining p (p \<leadsto> v) = v"
  proof -
    have "\<forall>a b.(a + b - a = b)"
      by (metis add_uminus_conv_diff diff_add_cancel semiring_normalization_rules(24))
    thus ?thesis by auto
  qed

  lemma lemDirectionFromTo: 
    shows "direction (line joining p to (p \<leadsto> dir)) = dir"
  proof -
    have "direction (line joining p to (p \<leadsto> dir)) = from p to (p \<leadsto> dir)" by simp
    thus ?thesis by (metis lemDirectionJoining)
  qed



  lemma lemLineEndpoint: 
    shows "q = p \<leadsto> (from p to q)"
  proof -
    have "\<forall>a b. (b = a + (b - a))" 
      by (metis diff_add_cancel semiring_normalization_rules(24))
    thus ?thesis by auto
  qed


  lemma lemNullLine:
    assumes "direction lineA = vecZero" 
      and   "inLine x lineA"
    shows   "x = basepoint lineA"
  proof -
    define bp where "bp = basepoint lineA"
    have "collinear x (basepoint lineA) (basepoint lineA \<leadsto> direction lineA)" 
      by (metis inLine.simps assms(2))
    hence "collinear x bp (bp \<leadsto> vecZero)" by (metis bp_def  assms(1))
    hence "collinear x bp bp" by simp
    hence "\<exists>a b.( (a + b = 1) \<and>  
                  (positionVector x = a**(positionVector bp) \<oplus> b**(positionVector bp)) )"
      by (metis collinear.simps)
    hence "positionVector x = positionVector bp" by (metis lemScale1 lemAddOverScale)
    thus ?thesis by (simp add: bp_def)
  qed


  lemma lemLineContainsBasepoint: 
    shows "inLine p (line joining p to q)"
  proof -
    define linePQ where "linePQ = line joining p to q"
    have bp: "basepoint linePQ = p" by (simp add: linePQ_def)
    have dir: "direction linePQ = from p to q" by (simp add: linePQ_def)
    have endq: "basepoint linePQ \<leadsto> direction linePQ = q" by (metis bp dir lemLineEndpoint)
    
    have "(1 + 0 = 1)  \<and> (positionVector p = 1**(positionVector p) \<oplus> 0**(positionVector q))"
      by auto
    hence "collinear p p q" by (metis collinear.simps)
    hence "collinear p (basepoint linePQ) (basepoint linePQ \<leadsto> direction linePQ)"
      by (metis bp endq)
    thus ?thesis by (simp add: linePQ_def)
  qed


  lemma lemLineContainsEndpoint: 
    shows "inLine q (line joining p to q)"
  proof -
    define linePQ where "linePQ = line joining p to q"
    have bp: "basepoint linePQ = p" by (simp add: linePQ_def)
    have dir: "direction linePQ = from p to q" by (simp add: linePQ_def)
    have endq: "basepoint linePQ \<leadsto> direction linePQ = q" by (metis bp dir lemLineEndpoint)
    
    have "(0 + 1 = 1)  \<and> (positionVector q = 0**(positionVector p) \<oplus> 1**(positionVector q))"
      by auto
    hence "collinear q p q" by (metis collinear.simps)
    hence "collinear q (basepoint linePQ) (basepoint linePQ \<leadsto> direction linePQ)"
      by (metis bp endq)
    thus ?thesis by (simp add: linePQ_def)
  qed



  lemma lemDirectionReverse: 
    shows "from q to p = vecNegate (from p to q)"
    by simp


  lemma lemParallelJoin: 
    assumes "line joining p to q \<parallel> line joining q to r"
    shows  "line joining p to q \<parallel> line joining p to r"
  proof -
    define linePQ where "linePQ = line joining p to q"
    define lineQR where "lineQR = line joining q to r"
    define linePR where "linePR = line joining p to r"

    have case1: "(direction linePQ = vecZero) \<longrightarrow> ?thesis" by (simp add: linePQ_def)
    have case2: "(direction linePR = vecZero) \<longrightarrow> ?thesis" by (simp add: linePR_def)

    {
      assume case3: "direction linePQ \<noteq> vecZero \<and> direction linePR \<noteq> vecZero"
      {
        assume case3a: "direction lineQR = vecZero"
        have "inLine r lineQR" by (metis lemLineContainsEndpoint lineQR_def)
        hence "r = basepoint lineQR" by (metis lemNullLine case3a)
        hence "r = q" by (simp add: lineQR_def)
        hence "linePQ = linePR" by (simp add: linePQ_def linePR_def)
        hence ?thesis by (metis lemParallelReflexive linePQ_def linePR_def)
      }
      from this have rtp3a: "direction lineQR = vecZero \<longrightarrow> ?thesis" by blast

      {
        assume case3b: "direction lineQR \<noteq> vecZero"

        define dirPQ where "dirPQ = from p to q"
        have dir_pq: "direction linePQ = dirPQ" by (simp add: linePQ_def dirPQ_def)

        define dirQR where "dirQR = from q to r"
        have dir_qr: "direction lineQR = dirQR" by (simp add: lineQR_def dirQR_def)
  
        have exists_k: "\<exists>k.(k \<noteq> 0 \<and> direction lineQR = k**direction linePQ)" 
          by (metis linePQ_def lineQR_def assms(1) parallel.simps case3b case3)
        then obtain k where k_props: "k \<noteq> 0 \<and> dirQR= k**dirPQ" by (metis dir_pq dir_qr)

        define scalar where "scalar = 1+k"

        have "q = p \<leadsto> dirPQ \<and> r = q \<leadsto> dirQR" by (metis lemLineEndpoint dirPQ_def dirQR_def)
        hence "r = p \<leadsto> dirPQ \<leadsto> (k**dirPQ)" by (metis k_props)
        hence scalarPR: "r = p \<leadsto> scalar**dirPQ"
          by (metis lemScaleLinear lemScale1 lemAddOverScale scalar_def)

        {
          assume scalar0: "scalar = 0"
          have "r = p" by (simp add: lemScale0 scalarPR scalar0)
          hence "direction linePR = vecZero" by (simp add: linePR_def)
          hence "False" by (metis case3)
        }
        from this have scalar_nonzero: "scalar \<noteq> 0" by blast

        have "linePR = line joining p to (p \<leadsto> scalar**dirPQ)" 
          by (simp add: linePR_def scalarPR)
        hence "direction linePR = scalar**dirPQ" by (metis lemDirectionFromTo)
    
        hence scalar_props: "scalar \<noteq> 0 \<and> direction linePR = scalar**direction linePQ" 
         by (metis scalar_nonzero dir_pq)
        hence ?thesis by (metis parallel.simps linePR_def linePQ_def) 
      }
      from this have "direction lineQR \<noteq> vecZero \<longrightarrow> ?thesis" by blast
    
      hence ?thesis by (metis rtp3a)
    }
    from this have "(direction linePQ \<noteq> vecZero \<and> direction linePR \<noteq> vecZero) \<longrightarrow> ?thesis" by blast

    thus ?thesis by (metis case1 case2)
  qed


  lemma lemDirectionCollinear: 
    shows "collinear u v (v \<leadsto> d) \<longleftrightarrow> (\<exists>\<beta>.(from u to v = (-\<beta>)**d))"
  proof -
    have basic1: "\<forall>u v.(positionVector (u \<leadsto> v)) = (positionVector u) \<oplus> v" by simp
    have basic2: "\<forall>u v w.(u = v \<oplus> w \<longrightarrow> v \<ominus> u = vecNegate w )"
      apply auto 
      by    (metis add_uminus_conv_diff diff_add_cancel minus_add 
              semiring_normalization_rules(24)) +
    have basic3: "\<forall>u v.(from u to v = positionVector v \<ominus> positionVector u)" by simp
    have basic4: "\<forall>u v w.(v \<ominus> u = vecNegate w \<longrightarrow> u = v \<oplus> w)"
      apply auto
      by (metis add_uminus_conv_diff diff_add_cancel lemScale1 mult.left_neutral 
          semiring_normalization_rules(24) vecScale.simps)

    {
      assume assm: "collinear u v (v \<leadsto> d)"
      have "\<exists>\<alpha> \<beta>. ( (\<alpha> + \<beta> = 1)  \<and>
         positionVector u = \<alpha>**(positionVector v) \<oplus> \<beta>**(positionVector (v \<leadsto> d)) )"
        by (metis assm collinear.simps)
      then obtain \<alpha> \<beta> where props: "(\<alpha> + \<beta> = 1)  \<and>
              positionVector u = \<alpha>**(positionVector v) \<oplus> \<beta>**(positionVector (v \<leadsto> d))" by auto
      hence "positionVector u = 1**(positionVector v) \<oplus> \<beta>**d"
        by (metis basic1 lemScaleOverAdd lemVecPlusAssoc lemAddOverScale props)
      hence "positionVector u = positionVector v \<oplus> \<beta>**d" by (metis lemScale1)
      hence "positionVector v \<ominus> positionVector u = (-\<beta>)**d" by (metis basic2 lemScaleNeg)
      hence "\<exists>\<beta>.(from u to v = (-\<beta>)**d)" by (metis basic3)
    }
    from this have fwd: "collinear u v (v \<leadsto> d) \<longrightarrow> (\<exists>\<beta>.(from u to v = (-\<beta>)**d))" by blast

    {
      assume "\<exists>\<beta>.(from u to v = (-\<beta>)**d)"
      then obtain \<beta> where assm: "from u to v = (-\<beta>)**d" by auto
      define \<alpha> where "\<alpha> = 1 - \<beta>"
      have \<alpha>\<beta>_sum: "\<alpha> + \<beta> = 1" by (simp add: \<alpha>_def) 
      have "from u to v = vecNegate (\<beta>**d)" by (metis assm lemScaleNeg)
      hence "positionVector v \<ominus> positionVector u = vecNegate (\<beta>**d)" by auto
      hence "positionVector u = positionVector v \<oplus> \<beta>**d" by (metis basic4)
      hence "positionVector u = 1**(positionVector v) \<oplus> \<beta>**d"
        by (metis lemScale1)
      hence "(\<alpha> + \<beta> = 1)  \<and>
            positionVector u = \<alpha>**(positionVector v) \<oplus> \<beta>**(positionVector (v \<leadsto> d))"
        by (metis \<alpha>\<beta>_sum basic1 lemScaleOverAdd lemVecPlusAssoc lemAddOverScale)
      hence "collinear u v (v \<leadsto> d)" by auto
    }
    from this have "(\<exists>\<beta>.(from u to v = (-\<beta>)**d)) \<longrightarrow> collinear u v (v \<leadsto> d)" by blast

    thus ?thesis by (metis fwd)
  qed


  lemma lemParallelNotMeet: 
    assumes "lineA \<parallel> lineB"
      and   "direction lineA \<noteq> vecZero"
      and   "direction lineB \<noteq> vecZero"
      and   "inLine x lineA"
      and   "\<not>(inLine x lineB)"
    shows   "\<not>(meets lineA lineB)"
  proof -

    have basic: "\<forall>p q v a.(from p to q = a**v \<longrightarrow> from q to p = (-a)**v)"
      apply (simp add: lemScaleNeg) by (metis minus_diff_eq)

    define bpA where "bpA = basepoint lineA"
    define dirA where "dirA = direction lineA"
    define bpB where "bpB = basepoint lineB"
    define dirB where "dirB = direction lineB"

    (* lineA is parallel to lineB *)
    have "lineB \<parallel> lineA" by (metis lemParallelSym assms(1))
    hence exists_kab: "\<exists>kab.(kab \<noteq> (0::'a) \<and> direction lineA = kab**direction lineB)" 
      by (metis parallel.simps assms(2) assms(3))
    then obtain kab where kab_props: "kab \<noteq> 0 \<and> dirA = kab**dirB" by (metis dirA_def dirB_def)

    (* x is in lineA *)
    have "collinear x bpA (bpA \<leadsto> dirA)" by (metis assms(4) inLine.simps bpA_def dirA_def)
    then obtain \<beta> where "from x to bpA = (-\<beta>)**dirA" by (metis lemDirectionCollinear)
    hence x_to_bpA: "from x to bpA = ((-\<beta>)*kab)**dirB" by (metis lemScaleScale kab_props)

    (* Assume the claim is false, and show that x is in lineB, contrary to assumption *)
    {
      assume converse: "meets lineA lineB"
      have "\<exists>p.(inLine p lineA \<and> inLine p lineB)" by (metis converse meets.simps)
      then obtain p where  p_in_AB: "inLine p lineA \<and> inLine p lineB" by auto

      have "collinear p bpA (bpA \<leadsto> dirA)" by (metis p_in_AB inLine.simps bpA_def dirA_def)
      then obtain \<beta>A where "from p to bpA = (-\<beta>A)**dirA" by (metis lemDirectionCollinear)
      hence "from bpA to p = (\<beta>A)**dirA" by (metis basic minus_minus)
      hence bpA_to_p: "from bpA to p = (\<beta>A*kab)**dirB" by (metis lemScaleScale kab_props)

      have "collinear p bpB (bpB \<leadsto> dirB)" by (metis p_in_AB inLine.simps bpB_def dirB_def)
      then obtain \<beta>B where p_to_bpB: "from p to bpB = (-\<beta>B)**dirB" by (metis lemDirectionCollinear)

      (* Express from x to bpB directly in terms of dirB *)

      define \<gamma> where "\<gamma> = -((-\<beta>)*kab + (\<beta>A*kab) + (-\<beta>B))"
      have x_to_bpB: "(from x to bpA) \<oplus> (from bpA to p) \<oplus> (from p to bpB) = (from x to bpB)"
        by (metis lemFromToTo)      
      hence "from x to bpB = ((-\<beta>)*kab)**dirB \<oplus> (\<beta>A*kab)**dirB \<oplus> (-\<beta>B)**dirB"
        by (metis x_to_bpA bpA_to_p p_to_bpB)
      hence "from x to bpB = (-\<gamma>)**dirB"
        by (metis lemAddOverScale add.assoc \<gamma>_def minus_minus)
      hence "collinear x bpB (bpB \<leadsto> dirB)" by (metis lemDirectionCollinear)
      hence "inLine x lineB" by (metis inLine.simps bpB_def dirB_def)
    }
    from this have "meets lineA lineB \<longrightarrow> inLine x lineB" by blast
    thus ?thesis by (metis assms(5))
  qed


  lemma lemAxisIsLine:
    assumes "onAxisT x"
      and   "onAxisT y"
      and   "onAxisT z"
      and   "x \<noteq> y"
      and   "y \<noteq> z"
      and   "z \<noteq> x"
    shows   "collinear x y z"
  proof -
    define ratio where "ratio = -(tval y - tval x) / (tval z - tval y)"

    have x_onAxis: "xval x = 0 \<and> yval x = 0 \<and> zval x = 0" by (metis assms(1) onAxisT.simps)
    have y_onAxis: "xval y = 0 \<and> yval y = 0 \<and> zval y = 0" by (metis assms(2) onAxisT.simps)
    have z_onAxis: "xval z = 0 \<and> yval z = 0 \<and> zval z = 0" by (metis assms(3) onAxisT.simps)

    have  "tval z - tval y = 0 \<longrightarrow> z = y" by (simp add: z_onAxis y_onAxis)
    hence "tval z \<noteq> tval y" by (metis assms(5) eq_iff_diff_eq_0)
    hence tvalyz_nonzero: "tval z - tval y \<noteq> 0" by (metis eq_iff_diff_eq_0)

    have x_to_y: "from x to y = \<lparr> tdir = tval y - tval x, xdir = 0, ydir = 0, zdir = 0 \<rparr>"
      by (simp add: x_onAxis y_onAxis)
    have y_to_z: "from y to z = \<lparr> tdir = tval z - tval y, xdir = 0, ydir = 0, zdir = 0 \<rparr>"
      by (simp add:y_onAxis z_onAxis)

    have "from x to y = (-ratio)**(from y to z)" 
      apply (simp add: x_to_y y_to_z ratio_def)
      by (metis diff_self eq_divide_imp minus_diff_eq mult_eq_0_iff 
                tvalyz_nonzero x_onAxis y_onAxis z_onAxis)
     hence "collinear x y (y \<leadsto> (from y to z))" by (metis lemDirectionCollinear)
    thus ?thesis by (metis lemLineEndpoint)
  qed

  lemma lemSpace2Sym: 
    shows "space2 x y = space2 y x"
  proof -
    define xsep where "xsep = xval x - xval y"
    define ysep where "ysep = yval x - yval y"
    define zsep where "zsep = zval x - zval y"

    have spacexy: "space2 x y = (xsep*xsep) + (ysep*ysep) + (zsep*zsep)"
      by (simp add: xsep_def ysep_def zsep_def)
    have spaceyx: "space2 y x = (-xsep)*(-xsep) + (-ysep)*(-ysep) + (-zsep)*(-zsep)"
      by (simp add: xsep_def ysep_def zsep_def)
    thus ?thesis by (metis spacexy diff_0_right minus_diff_eq minus_mult_left minus_mult_right)
  qed

  lemma lemTime2Sym: 
    shows "time2 x y = time2 y x"
  proof -
    define tsep where "tsep = tval x - tval y"

    have timexy: "time2 x y = tsep*tsep"
      by (simp add: tsep_def)
    have timeyx: "time2 y x = (-tsep)*(-tsep)"
      by (simp add: tsep_def)
    thus ?thesis by (metis timexy diff_0_right minus_diff_eq minus_mult_left minus_mult_right)
  qed

end

(*
  A plane is determined by a basepoint with two directions.
*)
class Planes = Quantities + Lines
begin
  fun mkPlane :: "'a Point \<Rightarrow> 'a Vector \<Rightarrow> 'a Vector \<Rightarrow> 'a Plane" where
    "mkPlane b d1 d2 = \<lparr> pbasepoint = b, direction1 = d1, direction2 = d2 \<rparr>"

  fun coplanar :: "'a Point \<Rightarrow> 'a Point \<Rightarrow> 'a Point \<Rightarrow> 'a Point \<Rightarrow> bool" where
    "coplanar e x y z 
      = (\<exists>\<alpha> \<beta> \<gamma>. ( (\<alpha> +  \<beta> +  \<gamma> = 1)  \<and>
            positionVector e 
              = (\<alpha>**(positionVector x) \<oplus> \<beta>**(positionVector y) \<oplus> \<gamma>**(positionVector z) )))"

  fun inPlane :: "'a Point \<Rightarrow> 'a Plane \<Rightarrow> bool" where
    "inPlane e pl = coplanar e (pbasepoint pl) (pbasepoint pl \<leadsto> direction1 pl)
                                               (pbasepoint pl \<leadsto> direction2 pl)"

  fun samePlane :: "'a Plane \<Rightarrow> 'a Plane \<Rightarrow> bool" where
    "samePlane pl pl' = (inPlane (pbasepoint pl) pl' \<and>
                         inPlane (pbasepoint pl \<leadsto> direction1 pl) pl' \<and>
                         inPlane (pbasepoint pl \<leadsto> direction2 pl) pl')"

lemma lemPlaneContainsBasePoint: 
  shows "inPlane (pbasepoint pl) pl"
  proof -
    define \<alpha> where "\<alpha> = (1::'a)"
    define \<beta> where "\<beta> = (0::'a)"
    define \<gamma> where "\<gamma> = (0::'a)"
    have rtp1: "\<alpha> + \<beta> + \<gamma> = 1" by (simp add: \<alpha>_def \<beta>_def \<gamma>_def)

    define e where "e = pbasepoint pl"
    define x where "x = pbasepoint pl"
    define y where "y = pbasepoint pl \<leadsto> direction1 pl"
    define z where "z = pbasepoint pl \<leadsto> direction2 pl"
    have rtp2: "positionVector e = \<alpha>**(positionVector x) 
                                 \<oplus> \<beta>**(positionVector y) \<oplus> \<gamma>**(positionVector z)"
      by (simp add: e_def x_def \<alpha>_def \<beta>_def \<gamma>_def)

    have sameplane: "coplanar e x y z" by (metis coplanar.simps rtp1 rtp2)
    hence "coplanar e (pbasepoint pl) (pbasepoint pl \<leadsto> direction1 pl) 
                                      (pbasepoint pl \<leadsto> direction2 pl)" 
      by (simp add: x_def y_def z_def)
    hence "inPlane e pl" by simp
    thus ?thesis by (simp add: e_def)
qed

end


(*
  An upright cone is determined by its vertex + slope (ie, speed).
*)

class Cones = Quantities + Lines + Planes +
fixes 
  (* the tangent plane at a point on a cone *)
  tangentPlane :: "'a Point \<Rightarrow> 'a Cone \<Rightarrow> 'a Plane"
assumes 
  (* The pbasepoint of the plane-at-e is e *)
  AxTangentBase: "pbasepoint (tangentPlane e cone) = e"
and
  (* The tangent plane contains the vertex *)
  AxTangentVertex: "inPlane (vertex cone) (tangentPlane e cone)"
and
  (* The tangent plane meets the cone in a line *)
  AxConeTangent: "(onCone e cone) \<longrightarrow>
                  ((inPlane pt (tangentPlane e cone) \<and> onCone pt cone) 
                                                           \<longleftrightarrow> collinear (vertex cone) e pt)"
and
  (* The tangent plane is tangential to all cones with vertex in that plane, and
     the intersection lines are parallel. *)
  AxParallelCones: "(onCone e econe \<and> e \<noteq> vertex econe \<and> onCone f fcone \<and> f \<noteq> vertex fcone
                      \<and> inPlane f (tangentPlane e econe))
                    \<longrightarrow>  (samePlane (tangentPlane e econe) (tangentPlane f fcone)
                          \<and> ((lineJoining (vertex econe) e) \<parallel> (lineJoining (vertex fcone) f)))"
and
  (* 
     if f is outside a cone, there is a tangent plane to that cone which contains f. The 
     tangent plane is determined by some e lying on the intersection line with the cone.
  *)
  AxParallelConesE: "outsideCone f cone
    \<longrightarrow> (\<exists>e.(onCone e cone \<and> e \<noteq> vertex cone \<and> inPlane f (tangentPlane e cone)))"
and
(* 
  Given distinct e f on the t-axis, and g off the axis, we can 
  find a point p on the line e-g such that the line f-p has 
  slope s. This can be proven using AxEuclidean, by taking the 
  intersection of a line with a cone.
*)
  AxSlopedLineInVerticalPlane: "\<lbrakk>onAxisT e; onAxisT f; e \<noteq> f; \<not>(onAxisT g)\<rbrakk>
     \<Longrightarrow> (\<forall>s.( \<exists>p . (collinear e g p \<and> (space2 p f = (s*s)*time2 p f))))"

begin

  fun onCone :: "'a Point \<Rightarrow> 'a Cone \<Rightarrow> bool" where
    "onCone p cone  
      = (space2 (vertex cone) p  = (slope cone * slope cone) * time2 (vertex cone) p )"

  fun insideCone :: "'a Point \<Rightarrow> 'a Cone \<Rightarrow> bool" where
    "insideCone p cone  
      = (space2 (vertex cone) p < (slope cone * slope cone) * time2 (vertex cone) p)"

  fun outsideCone :: "'a Point \<Rightarrow> 'a Cone \<Rightarrow> bool" where
    "outsideCone p cone  
      = (space2 (vertex cone) p > (slope cone * slope cone) * time2 (vertex cone) p)"

  fun mkCone :: "'a Point \<Rightarrow> 'a \<Rightarrow> 'a Cone" where
    "mkCone v s = \<lparr> vertex = v, slope = s \<rparr>"

  lemma lemVertexOnCone: 
    shows "onCone (vertex cone) cone"
  by simp

  lemma lemOutsideNotOnCone: 
    assumes "outsideCone f cone"
    shows   "\<not> (onCone f cone)"
  by (metis assms less_irrefl onCone.simps outsideCone.simps)

  

end

class SpaceTime = Quantities + Vectors + Points + Lines + Planes + Cones

end
