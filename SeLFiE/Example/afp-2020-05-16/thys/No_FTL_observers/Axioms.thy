(*
   Author: Mike Stannett
   Date: 22 October 2012
   m.stannett@sheffield.ac.uk
   Updated 28 April 2016 to run under Isabelle2016.
*)
theory Axioms
imports SpaceTime SomeFunc
begin

record Body =
  Ph :: "bool"
  IOb :: "bool"


class WorldView = SpaceTime +
fixes
  (* Worldview relation *)
  W :: "Body \<Rightarrow> Body \<Rightarrow> 'a Point \<Rightarrow> bool" ("_ sees _ at _")
and
  (* Worldview transformation *)
  wvt :: "Body \<Rightarrow> Body \<Rightarrow> 'a Point \<Rightarrow> 'a Point"
assumes
  AxWVT: "\<lbrakk> IOb m; IOb k \<rbrakk> \<Longrightarrow> (W k b x \<longleftrightarrow> W m b (wvt m k x))"
and
  AxWVTSym: "\<lbrakk> IOb m; IOb k \<rbrakk> \<Longrightarrow> (y = wvt k m x  \<longleftrightarrow>  x = wvt m k y)"
begin
end


(* THE BASIC AXIOMS *)
(* ================ *)


class AxiomPreds = WorldView 
begin
  fun sqrtTest :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
     "sqrtTest x r = ((r \<ge> 0) \<and> (r*r = x))"

  fun cTest :: "Body \<Rightarrow> 'a \<Rightarrow> bool" where
    "cTest m v = ( (v > 0) \<and> ( \<forall>x y . ( 
               (\<exists>p. (Ph p \<and> W m p x \<and> W m p y)) \<longleftrightarrow> (space2 x y = (v * v)*(time2 x y)) 
             )))"
end

(*
  AxEuclidean
  Quantities form a Euclidean field, ie positive quantities have
  square roots. We introduce a function, sqrt, that determines them.
*)
class AxEuclidean = AxiomPreds + Quantities +
assumes
  AxEuclidean: "(x \<ge> Groups.zero_class.zero) \<Longrightarrow> (\<exists>r. sqrtTest x r)"
begin

  abbreviation sqrt :: "'a \<Rightarrow> 'a" where
     "sqrt \<equiv> someFunc sqrtTest"

  lemma lemSqrt: 
    assumes "x \<ge> 0"
      and   "r = sqrt x"
    shows   "r \<ge> 0  \<and>  r*r = x"
  proof -
    have rootExists: "(\<exists>r. sqrtTest x r)" by (metis AxEuclidean assms(1))
    hence "sqrtTest x (sqrt x)" by (metis lemSomeFunc)
    thus ?thesis using assms(2) by simp
  qed

end


(* 
   AxLight
   There is an inertial observer, according to whom, any light
   signal moves with the same velocity in any direction 
*)
class AxLight = WorldView +
assumes
  AxLight: "\<exists>m v.( IOb m \<and> (v > (0::'a)) \<and> ( \<forall>x y.( 
              (\<exists>p.(Ph p \<and> W m p x \<and> W m p y)) \<longleftrightarrow> (space2 x y = (v * v)*time2 x y) 
            )))"
begin
end



(*
  AxPh
  For any inertial observer, the speed of light is the same in every
  direction everywhere, and it is finite. Furthermore, it is possible
  to send out a light signal in any direction.
*)
class AxPh = WorldView + AxiomPreds +
assumes
  AxPh: "IOb m \<Longrightarrow> (\<exists>v. cTest m v)"
begin

  abbreviation c :: "Body \<Rightarrow> 'a" where
    "c \<equiv> someFunc cTest"

  fun lightcone :: "Body \<Rightarrow> 'a Point \<Rightarrow> 'a Cone" where
    "lightcone m v = mkCone v (c m)"


lemma lemCProps:
  assumes "IOb m"
     and  "v = c m"
  shows "(v > 0) \<and> (\<forall>x y.((\<exists>p. (Ph p \<and> W m p x \<and> W m p y)) 
                      \<longleftrightarrow> ( space2 x y = (c m * c m)*time2 x y )))"
proof -
  have vExists: "(\<exists>v. cTest m v)" by (metis AxPh assms(1))
  hence "cTest m (c m)" by (metis lemSomeFunc)
  thus ?thesis using assms(2) by simp
qed


lemma lemCCone: 
  assumes "IOb m"
    and   "onCone y (lightcone m x)"
  shows   "\<exists>p. (Ph p \<and> W m p x \<and> W m p y)"
proof -
  have "(\<exists>p.(Ph p \<and> W m p x \<and> W m p y)) 
                      \<longleftrightarrow> ( space2 x y = (c m * c m)*time2 x y )"
    by (smt assms(1) lemCProps)
  hence ph_exists: "(space2 x y = (c m * c m)*time2 x y) \<longrightarrow> (\<exists>p.(Ph p \<and> W m p x \<and> W m p y))"
    by metis
  define lcmx where "lcmx = lightcone m x"
  have lcmx_vertex: "vertex lcmx = x" by (simp add: lcmx_def)
  have lcmx_slope: "slope lcmx = c m" by (simp add: lcmx_def)
  have "onCone y lcmx \<longrightarrow> (space2 x y = (c m * c m)*time2 x y)" 
    by (metis lcmx_vertex lcmx_slope onCone.simps)
  hence "space2 x y = (c m * c m)*time2 x y" by (metis lcmx_def assms(2))
  thus ?thesis by (metis ph_exists)
qed


lemma lemCPos: 
  assumes "IOb m"
  shows   "c m > 0"
  by (metis assms(1) lemCProps)


lemma lemCPhoton:
  assumes "IOb m"
  shows "\<forall>x y. (\<exists>p. (Ph p \<and> W m p x \<and> W m p y)) \<longleftrightarrow> (space2 x y = (c m * c m)*(time2 x y))"
  by (metis assms(1) lemCProps)

end



(*
  AxEv
  Inertial observers see the same events (meetings of bodies).
  This also enables us to discuss the worldview transformation.
*)
class AxEv = WorldView +
assumes
  AxEv: "\<lbrakk> IOb m; IOb k\<rbrakk> \<Longrightarrow>  (\<exists>y. (\<forall>b. (W m b x  \<longleftrightarrow> W k b y)))"
begin
end



(*
  Inertial observers can move with any speed slower than that of light
*)
class AxThExp = WorldView + AxPh +
assumes
    AxThExp: "IOb m \<Longrightarrow> (\<forall>x y .( 
       (\<exists>k.(IOb k \<and> W m k x \<and> W m k y)) \<longleftrightarrow> (space2 x y < (c m * c m) * time2 x y) 
       ))"

begin
end



(*
  Every inertial observer is stationary according to himself
*)
class AxSelf = WorldView +
assumes
  AxSelf: "IOb m  \<Longrightarrow>  (W m m x) \<longrightarrow> (onAxisT x)"
begin
end



(* 
  All inertial observers agree that the speed of light is 1
*)
class AxC = WorldView + AxPh +
assumes
  AxC: "IOb m \<Longrightarrow> c m = 1"
begin
end


(*
  Inertial observers agree as to the spatial distance between two
  events if these two events are simultaneous for both of them.
*)
class AxSym = WorldView +
assumes
  AxSym: "\<lbrakk> IOb m; IOb k \<rbrakk> \<Longrightarrow>
            (W m e x \<and> W m f y \<and> W k e x'\<and> W k f y' \<and>
            tval x = tval y \<and> tval x' = tval y' )
          \<longrightarrow> (space2 x y = space2 x' y')"
begin
end



(*
  AxLines
  All observers agree about lines
*)
class AxLines = WorldView + 
assumes
  AxLines: "\<lbrakk> IOb m; IOb k; collinear x p q \<rbrakk> \<Longrightarrow> 
     collinear (wvt k m x) (wvt k m p) (wvt k m q)"
begin
end



(*
  AxPlanes
  All observers agree about planes
*)
class AxPlanes = WorldView +
assumes
  AxPlanes: "\<lbrakk> IOb m; IOb k \<rbrakk> \<Longrightarrow> 
     (coplanar e x y z  \<longrightarrow> coplanar (wvt k m e) (wvt k m x) (wvt k m y) (wvt k m z))"
begin
end



(*
  AxCones
  All observers agree about lightcones
*)
class AxCones = WorldView + AxPh +
assumes
  AxCones: "\<lbrakk> IOb m; IOb k \<rbrakk> \<Longrightarrow> 
     ( onCone x (lightCone m v) \<longrightarrow> onCone (wvt k m x) (lightcone k (wvt k m v)))"
begin
end



(*
  All inertial observers see time travelling in the same direction. That
  is, if m thinks that k reached y after he reached x, then
  k should also think that he reached y after he reached x.
*)
class AxTime = WorldView +
assumes 
  AxTime: "\<lbrakk> IOb m; IOb k \<rbrakk> 
              \<Longrightarrow>( x \<lesssim> y \<longrightarrow> wvt k m x \<lesssim> wvt k m y )"
begin
end


end
