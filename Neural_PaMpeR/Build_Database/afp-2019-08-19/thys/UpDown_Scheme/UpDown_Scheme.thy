section \<open> UpDown Scheme \<close>

theory UpDown_Scheme
  imports Grid
begin

fun down' :: "nat \<Rightarrow> nat \<Rightarrow> grid_point \<Rightarrow> real \<Rightarrow> real \<Rightarrow> vector \<Rightarrow> vector"
where
  "down' d 0       p f\<^sub>l f\<^sub>r \<alpha> = \<alpha>"
| "down' d (Suc l) p f\<^sub>l f\<^sub>r \<alpha> = (let
      f\<^sub>m = (f\<^sub>l + f\<^sub>r) / 2 + (\<alpha> p);
      \<alpha> = \<alpha>(p := ((f\<^sub>l + f\<^sub>r) / 4 + (1 / 3) * (\<alpha> p)) / 2 ^ (lv p d));
      \<alpha> = down' d l (child p left d) f\<^sub>l f\<^sub>m \<alpha>;
      \<alpha> = down' d l (child p right d) f\<^sub>m f\<^sub>r \<alpha>
    in \<alpha>)"

definition down :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> vector \<Rightarrow> vector" where
  "down = lift (\<lambda> d l p. down' d l p 0 0)"

fun up' :: "nat \<Rightarrow> nat \<Rightarrow> grid_point \<Rightarrow> vector \<Rightarrow> (real * real) * vector" where
  "up' d       0 p \<alpha> = ((0, 0), \<alpha>)"
| "up' d (Suc l) p \<alpha> = (let
      ((f\<^sub>l, f\<^sub>m\<^sub>l), \<alpha>) = up' d l (child p left d) \<alpha>;
      ((f\<^sub>m\<^sub>r, f\<^sub>r), \<alpha>) = up' d l (child p right d) \<alpha>;
      result = (f\<^sub>m\<^sub>l + f\<^sub>m\<^sub>r + (\<alpha> p) / 2 ^ (lv p d) / 2) / 2
    in ((f\<^sub>l + result, f\<^sub>r + result), \<alpha>(p := f\<^sub>m\<^sub>l + f\<^sub>m\<^sub>r)))"


definition up :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> vector \<Rightarrow> vector" where
  "up = lift (\<lambda> d lm p \<alpha>. snd (up' d lm p \<alpha>))"

fun updown' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> vector \<Rightarrow> vector" where
  "updown' dm lm 0 \<alpha> = \<alpha>"
| "updown' dm lm (Suc d) \<alpha> =
    (sum_vector (updown' dm lm d (up dm lm d \<alpha>)) (down dm lm d (updown' dm lm d \<alpha>)))"

definition updown :: "nat \<Rightarrow> nat \<Rightarrow> vector \<Rightarrow> vector" where
  "updown dm lm \<alpha> = updown' dm lm dm \<alpha>"

end
