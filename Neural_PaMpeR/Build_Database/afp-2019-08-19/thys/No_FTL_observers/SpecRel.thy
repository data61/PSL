(*
   Author: Mike Stannett
   Date: 22 October 2012
   m.stannett@sheffield.ac.uk
   Updated 28 April 2016 to run under Isabelle2016.
*)
theory SpecRel
imports Axioms
begin

class SpecRel = WorldView + AxPh + AxEv + AxSelf + AxSym
(*
  The following proof  assumes that the quantity field is Euclidean. It
  may be possible to produce a proof without this constraint.
*)

  + AxEuclidean

(*
  We also assume for now that lines, planes and lightcones are
  preserved by the worldview transformation.
*)

  + AxLines + AxPlanes + AxCones

begin


(* *******************************************************************
*                                                                    *
*     THEOREM:                                                       *
*     No inertial observer can move faster than light.               *
*                                                                    *
** **************************************************************** *)

  lemma lemZEG:
    shows "z - e = g - e + (z - g)"
  proof -
    have  "g - e + (z - g) = (g - e + z) - g" by (rule add_diff_eq)
    also have "(g - e + z) - g = (-e + z)"
      by (metis local.diff_add_cancel 
                local.ring_normalization_rules(2) 
                local.semiring_normalization_rules(24) 
                local.semiring_normalization_rules(25))
    thus ?thesis
      by (simp add: calculation)
  qed


lemma noFTLObserver:
  assumes iobm:  "IOb m"
  and     iobk:  "IOb k"
  and     mke:   "m sees k at e"
  and     mkf:   "m sees k at f"
  and     enotf: "e \<noteq> f"
shows     "space2 e f \<le> (c m * c m) * time2 e f"
proof -  (* by reductio *)

(* Step 1: Suppose k is going FTL from m's viewpoint. *)
{
  assume converse: "space2 e f > (c m * c m) * time2 e f" 


(* Step 2: Consider the m-lightcone at e *)
  define eCone where "eCone = mkCone e (c m)"  
  have e_on_econe: "onCone e eCone" by (simp add: eCone_def)



(* Step 3: There is a tangent plane for eCone containing both e and f,
   defined using some point g on the tangent line  *)

  have e_is_vertex: "e = vertex eCone" by (simp add: eCone_def)
  have cm_is_slope: "c m = slope eCone" by (simp add: eCone_def)
  hence outside: "outsideCone f eCone"
    by (metis (lifting) e_is_vertex cm_is_slope converse outsideCone.simps)

  have "outsideCone f eCone 
    \<longrightarrow> (\<exists>x.(onCone x eCone \<and> x \<noteq> vertex eCone \<and> inPlane f (tangentPlane x eCone)))"
    by (rule AxParallelConesE)

  hence tplane_exists: "\<exists>x.(onCone x eCone \<and> x \<noteq> vertex eCone \<and> inPlane f (tangentPlane x eCone))" 
    by (metis outside)
  then obtain g where g_props: "(onCone g eCone \<and> g \<noteq> vertex eCone \<and> inPlane f (tangentPlane g eCone))" 
    by auto
  have g_on_eCone: "onCone g eCone" by (metis g_props)
  have g_not_vertex: "g \<noteq> vertex eCone" by (metis g_props)

  define tplane where "tplane = tangentPlane g eCone"
  have e_in_tplane: "inPlane e tplane" by (metis AxTangentVertex e_is_vertex tplane_def)
  have f_in_tplane: "inPlane f tplane" by (metis g_props tplane_def)
  have g_in_tplane: "inPlane g tplane" by (metis lemPlaneContainsBasePoint tplane_def AxTangentBase)

  (* We'll need to show that e-f-g aren't collinear *)
  have "(onCone g eCone) \<longrightarrow>
                  ((inPlane f (tangentPlane g eCone) \<and> onCone f eCone) 
                                                           \<longleftrightarrow> collinear (vertex eCone) g f)"
    by (metis AxConeTangent)
  hence axconetangent: "collinear e g f \<longrightarrow> onCone f eCone"
    by (metis g_on_eCone e_is_vertex)
  have "\<not>(onCone f eCone)" by (metis outside lemOutsideNotOnCone)
  hence g_not_collinear: "\<not> (collinear e g f)"
    by (metis axconetangent)



(* Step 4: k considers wvte and wvtf to be distinct points on the t-axis, and wvtg is off 
           k's t-axis. *)

  define wvte where "wvte = wvt k m e"
  define wvtf where "wvtf = wvt k m f"
  define wvtg where "wvtg = wvt k m g"

  have "W k k wvte" by (metis wvte_def AxWVT mke iobm iobk)
  hence wvte_onAxis: "onAxisT wvte" by (metis AxSelf iobk)

  have "W k k wvtf" by (metis wvtf_def AxWVT mkf iobm iobk)
  hence wvtf_onAxis: "onAxisT wvtf" by (metis AxSelf iobk)

  have wvte_inv: "e = wvt m k wvte" by (metis AxWVTSym iobk iobm wvte_def)
  have wvtf_inv: "f = wvt m k wvtf" by (metis AxWVTSym iobk iobm wvtf_def)
  have wvtg_inv: "g = wvt m k wvtg" by (metis AxWVTSym iobk iobm wvtg_def)

  have e_not_g: "e \<noteq> g" by (metis e_is_vertex g_not_vertex)
  have f_not_g: "f \<noteq> g" by (metis outside lemOutsideNotOnCone g_on_eCone)

  have wvt_e_not_f: "wvte \<noteq> wvtf" by (metis wvte_inv wvtf_inv enotf)
  have wvt_f_not_g: "wvtf \<noteq> wvtg" by (metis wvtf_inv wvtg_inv f_not_g)
  have wvt_g_not_e: "wvtg \<noteq> wvte" by (metis wvtg_inv wvte_inv e_not_g)

  have if_g_onAxis:  "onAxisT wvtg \<longrightarrow> collinear wvte wvtg wvtf" 
    by (metis lemAxisIsLine wvte_onAxis wvtf_onAxis wvt_e_not_f wvt_f_not_g wvt_g_not_e)

  have "collinear wvte wvtg wvtf \<longrightarrow> collinear e g f"
    by (metis AxLines iobm iobk wvte_inv wvtf_inv wvtg_inv)
  hence "onAxisT wvtg \<longrightarrow> collinear e g f" by (metis if_g_onAxis)

  hence wvtg_offAxis: "\<not> (onAxisT wvtg)" by (metis g_not_collinear)
 



(* Step 5: There is a point z with various contradictory properties. *)

  have "\<forall>s.(\<exists>p.( collinear wvte wvtg p \<and> (space2 p wvtf = (s*s)*time2 p wvtf)))"
    by (metis AxSlopedLineInVerticalPlane wvte_onAxis wvtf_onAxis wvtg_offAxis wvt_e_not_f)
  hence exists_wvtz: "\<exists>p.( collinear wvte wvtg p \<and> (space2 p wvtf = (c k * c k)*time2 p wvtf))"
    by metis
  then obtain wvtz where 
    wvtz_props: "collinear wvte wvtg wvtz \<and> (space2 wvtz wvtf = (c k * c k)*time2 wvtz wvtf)" by auto
  hence wvtf_speed: "space2 wvtz wvtf = (c k * c k)*time2 wvtz wvtf" by metis

  define z where "z = wvt m k wvtz"  
  define wvtzCone where "wvtzCone = lightcone k wvtz"

  have wvtz_is_vertex: "wvtz = vertex wvtzCone" by (simp add: wvtzCone_def)
  have ck_is_slope: "c k = slope wvtzCone" by (simp add: wvtzCone_def)
  hence "space2 (vertex wvtzCone) wvtf = ((slope wvtzCone) *(slope wvtzCone))*time2 (vertex wvtzCone) wvtf" 
    by (metis wvtf_speed wvtz_is_vertex ck_is_slope)
  hence "onCone wvtf wvtzCone" by (metis onCone.simps)

  hence wvtf_on_wvtzCone: "onCone (wvt m k wvtf) (lightcone m z)" 
    by (metis iobm iobk AxCones wvtzCone_def z_def)



  (* f is on the lightcone at z *)
  define zCone where "zCone = lightcone m z"
  have z_is_vertex: "z = vertex zCone" by (simp add: zCone_def)
  have cm_is_zSlope: "c m = slope zCone" by (simp add: zCone_def)

  have f_on_zCone: "onCone f zCone" by (metis wvtf_inv wvtf_on_wvtzCone zCone_def)



  (* whence z is on the lightcone at f *)
  hence "space2 (vertex zCone) f = (slope zCone * slope zCone)*time2 (vertex zCone) f"
    by (simp add: zCone_def)
  hence "space2 z f = (c m * c m)*time2 z f" by (metis z_is_vertex cm_is_zSlope)
  hence fz_speed: "space2 f z = (c m * c m)*time2 f z" by (metis lemSpace2Sym lemTime2Sym)

  define fCone where "fCone = lightcone m f"

  have f_is_fVertex: "f = vertex fCone" by (simp add: fCone_def)
  have cm_is_fSlope: "c m = slope fCone" by (simp add: fCone_def)
  hence "space2 (vertex fCone) z = ((slope fCone) *(slope fCone))*time2 (vertex fCone) z" 
    by (metis fz_speed f_is_fVertex cm_is_fSlope)
  hence z_on_fCone: "onCone z fCone" by (metis onCone.simps)



  (* z is also on the lightcone at e, as well as in the tangent plane at g *)
  have "collinear wvte wvtg wvtz" by (metis wvtz_props)
  hence egz_collinear: "collinear e g z" by (metis wvte_inv wvtg_inv z_def AxLines iobm iobk)
  hence z_geometry: "(inPlane z (tangentPlane g eCone) \<and> onCone z eCone)"
    by (metis AxConeTangent e_is_vertex g_on_eCone)

  have z_on_eCone: "onCone z eCone" by (metis z_geometry)
  have z_in_tplane: "inPlane z tplane" by (metis z_geometry tplane_def)

  hence z_not_f: "z \<noteq> f" by (metis z_on_eCone outside lemOutsideNotOnCone)
  hence z_not_fVertex: "z \<noteq> vertex fCone" by (simp add: fCone_def z_not_f)

  {
    assume assm: "z = e"
    have "space2 f e = (c m * c m)*time2 f e \<and> space2 f e = space2 e f \<and> time2 f e = time2 e f" 
     by (metis lemSpace2Sym lemTime2Sym fz_speed assm)
    hence "space2 e f = (c m * c m)*time2 e f" by metis
    hence "False" by (metis less_irrefl converse)
  }
  from this have z_not_e: "z \<noteq> e" by blast


  (* but the lines e-z and f-z must be parallel *)

  define lineA where "lineA = lineJoining e z"
  define lineB where "lineB = lineJoining f z"

  {
    assume assm: "direction lineA = vecZero"
    have lemnullline: "(direction lineA = vecZero \<and> inLine z lineA) \<longrightarrow> z = basepoint lineA"
      by (metis lemNullLine)
    have "inLine z lineA" by (metis lineA_def lemLineContainsEndpoint)
    hence z_is_bp: "z = basepoint lineA" by (metis lemnullline assm)
    have "basepoint lineA = e" by (simp add: lineA_def)
    hence "False" by (metis z_is_bp z_not_e)
  }
  from this have ez_not_null: "direction lineA \<noteq> vecZero" by blast

  {
    assume assm: "direction lineB = vecZero"
    have lemnullline: "(direction lineB = vecZero \<and> inLine z lineB) \<longrightarrow> z = basepoint lineB"
      by (metis lemNullLine)
    have "inLine z lineB" by (metis lineB_def lemLineContainsEndpoint)
    hence z_is_bp: "z = basepoint lineB" by (metis lemnullline assm)
    have "basepoint lineB = f" by (simp add: lineB_def)
    hence "False" by (metis z_is_bp z_not_f)
  }
  from this have fz_not_null: "direction lineB \<noteq> vecZero" by blast

  {
    have "samePlane tplane (tangentPlane z fCone)
           \<and> ((lineJoining e g) \<parallel> (lineJoining f z))"
    by (metis AxParallelCones tplane_def
              g_on_eCone g_not_vertex z_on_fCone z_not_fVertex z_in_tplane
              e_is_vertex f_is_fVertex)

    hence eg_par_fz: "(lineJoining e g) \<parallel> (lineJoining f z)" by metis
    {
      assume case1: "direction (lineJoining e g) = vecZero"
      have "direction (lineJoining e g) = from e to g" by simp
      hence "from e to g = vecZero" by (metis case1)
      hence "e = g" by (simp)
      hence "False" by (metis e_not_g)
    }
    from this have eg_not_null: "\<not>(direction (lineJoining e g) = vecZero)" by blast
    then obtain a where a_props: "a \<noteq> 0 \<and> direction (lineJoining f z) = a**direction (lineJoining e g)"
      by (metis fz_not_null eg_not_null eg_par_fz parallel.simps lineB_def)
    hence f_to_z: "from f to z = a**(from e to g)" by simp
    have a_nonzero: "a \<noteq> 0" by (metis a_props)

    have eg_dir: "from e to g = direction (lineJoining e g)" by simp
    have gz_dir: "from g to z = direction (lineJoining g z)" by simp
    have egz: "z = g \<leadsto> (from g to z)" by (metis lemLineEndpoint)
    hence "collinear e g (g \<leadsto> (from g to z))" by (metis egz_collinear)
    then obtain b where e_to_g: "from e to g = (-b)**(from g to z)"
      by (metis lemDirectionCollinear)

    {
      assume assm: "-b = 0"
      have "from e to g = (-b)**(from g to z)" by (metis e_to_g)
      hence "from e to g = vecZero" by (simp add: assm)
      hence "direction (lineJoining e g) = vecZero" by (simp)
      hence "False" by (metis eg_not_null lineA_def)
    }
    from this have b_nonzero: "-b \<noteq> 0" by blast

    define binv where "binv = inverse (-b)"
    define factor where "factor = 1+binv"
    have binv_nonzero: "binv \<noteq> 0" by (metis b_nonzero add.comm_neutral binv_def nonzero_imp_inverse_nonzero right_minus)
    
    have "from e to g = (-b)**(from g to z)" by (metis e_to_g)
    hence g_to_z: "(from g to z) = binv**(from e to g)" 
      by (metis b_nonzero lemScaleInverse binv_def)

    
    
    have "from e to z = from e to g \<oplus> from g to z"      
      by (simp add: lemZEG)


    hence "from e to z = (from e to g) \<oplus> binv**(from e to g)" by (metis g_to_z)
    hence e_to_z: "from e to z = factor**(from e to g)" by (metis lemAddOverScale lemScale1 factor_def)
    have ez_dir: "direction (lineJoining e z) = from e to z" by simp
    have eg_dir: "direction (lineJoining e g) = from e to g" by simp 

    {
      assume assm: "factor = 0"
      have "from e to z = factor**(from e to g)" by (metis e_to_z)
      hence "from e to z = vecZero" by (simp add: assm)
      hence "direction (lineJoining e z) = vecZero" by (simp)
      hence "False" by (metis ez_not_null lineA_def)
    }
    from this have factor_nonzero: "factor \<noteq> 0" by blast

    have "direction (lineJoining e z) = factor**(direction (lineJoining e g))" 
      by (metis e_to_z ez_dir eg_dir)
    hence "(lineJoining e g) \<parallel> (lineJoining e z)" by (metis parallel.simps factor_nonzero)
    hence "(lineJoining e z) \<parallel> (lineJoining e g)" by (metis lemParallelSym)

    hence "(lineJoining e z) \<parallel> (lineJoining f z)" by (metis lemParallelTrans eg_par_fz eg_not_null)
  }
  from this have A_par_B: "lineA \<parallel> lineB" by (metis lineA_def lineB_def)


  (* which is impossible because this means they are distinct parallel lines that meet *)

  have e_in_lineA: "inLine e lineA" by (metis lineA_def lemLineContainsBasepoint)

  {
    have basic: "\<forall>a b.(((-a)*b)*((-a)*b) = (a*a)*(b*b))" 
      by (metis equation_minus_iff minus_mult_commute minus_mult_right 
                semiring_normalization_rules(17) semiring_normalization_rules(19))

    assume assm: "inLine e lineB"
    hence coll: "collinear e f (f \<leadsto> direction lineB)" by (simp add: lineB_def)
    then obtain \<beta> where props: "from e to f = (-\<beta>)**(direction lineB)"
      by (metis lemDirectionCollinear)
    
    hence "tval f - tval e = (-\<beta>)*(tval z - tval f) \<and> xval f - xval e = (-\<beta>)*(xval z - xval f)
        \<and> yval f - yval e = (-\<beta>)*(yval z - yval f) \<and> zval f - zval e = (-\<beta>)*(zval z - zval f)" 
      by (simp add: lineB_def)
    hence speeds: "time2 f e = (\<beta>*\<beta>)*time2 z f \<and> space2 f e = (\<beta>*\<beta>)*space2 z f" 
      apply (simp add: basic) apply auto
      apply (metis semiring_normalization_rules(18) semiring_normalization_rules(19))
      by (metis semiring_normalization_rules(18) semiring_normalization_rules(19) 
                semiring_normalization_rules(34))
      
    have "space2 f z = (c m * c m)*time2 f z" by (metis fz_speed)
    hence "space2 z f = (c m * c m)*time2 z f" by (metis lemSpace2Sym lemTime2Sym)
    hence "space2 f e = ((\<beta>*\<beta>)*(c m * c m))*time2 z f" by (metis speeds mult.assoc)
    hence "space2 f e = (c m * c m)*(\<beta>*\<beta>)*time2 z f" by (metis mult.assoc mult.commute)
    hence "space2 f e = (c m * c m)*time2 f e" by (metis mult.assoc speeds)
    hence "space2 e f = (c m * c m)*time2 e f" by (metis lemSpace2Sym lemTime2Sym)
    hence "False" by (metis less_irrefl converse)
  }
  from this have e_not_in_lineB: "\<not>(inLine e lineB)" by blast

  have "inLine z lineA \<and> inLine z lineB" by (metis lemLineContainsEndpoint lineA_def lineB_def)  
  hence A_meets_B: "meets lineA lineB" by auto

  hence "False" by (metis A_par_B ez_not_null fz_not_null e_in_lineA e_not_in_lineB lemParallelNotMeet)
  }
  from this have "\<not> (space2 e f > (c m * c m) * time2 e f)" by blast

  thus ?thesis by simp
qed

end


end
