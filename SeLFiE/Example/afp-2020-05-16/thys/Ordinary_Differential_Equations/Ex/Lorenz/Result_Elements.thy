theory Result_Elements
  imports
    "HOL-Analysis.Analysis"
    "HOL-ODE-Numerics.ODE_Numerics"
    "HOL-Library.Float"
begin

datatype result = Result
  (invoke_nf : bool)
  (min_deg : real)
  (max_deg : real)
  (expansion : real)
  (preexpansion : real)
  (gridx0 : int)
  (gridx1 : int)
  (gridy0 : int)
  (gridy1 : int)
  (inf_retx : int)
  (inf_rety : int)
  (sup_retx : int)
  (sup_rety : int)
derive "show" result

definition "get_results LX LY UX UY fgs =
  [fg \<leftarrow> fgs. LX \<le> gridx1 fg \<and> gridx0 fg \<le> UX \<and> LY \<le> gridy1 fg \<and> gridy0 fg \<le> UY]"

primrec mirror_result where
  "mirror_result (Result nf u v e ep x0 x1 y0 y1 rx0 ry0 rx1 ry1) =
    Result nf u v e ep (-x1) (-x0) (-y1) (-y0) (-rx1) (-ry1) (-rx0) (-ry0)"
definition "upper_result fg \<longleftrightarrow> 5 * gridy1 fg \<ge> 2 * gridx0 fg"
definition "symmetrize upper_list = upper_list @ map mirror_result upper_list"
definition "mirror_upper fg = (if upper_result fg then fg else mirror_result fg)"

definition "tangent_of_deg deg = (cos (rad_of (deg)), sin (rad_of (deg)), 0::real)"

definition "tangent_seg_of_res_spec res = SPEC (\<lambda>r.
  closed_segment (tangent_of_deg (min_deg res)) (tangent_of_deg (max_deg res)) \<subseteq> r)"

definition "conefield_of_res res =
  conefield (tangent_of_deg (min_deg res)) (tangent_of_deg (max_deg res))"

definition "ivl_of_resultrect x0 x1 y0 y1 =
  (let scale = FloatR 1 (-8) in ([scale * real_of_int (x0 - 1), scale * real_of_int (y0 - 1), 27],
                         [scale * real_of_int (x1 + 1), scale * real_of_int (y1 + 1), 27]))"

definition "ivl_of_res res = ivl_of_resultrect (gridx0 res) (gridx1 res) (gridy0 res) (gridy1 res)"

definition
  "source_of_res res =
    (set_of_ivl (pairself eucl_of_list (ivl_of_res res))::(real*real*real) set)"

definition "c1_of_res res = source_of_res res \<times> conefield_of_res res"

definition "return_of_res results res =
  set (get_results (inf_retx res) (inf_rety res) (sup_retx res) (sup_rety res) results)"


subsection \<open>Validate (in a non-verified way) the expansion estimates (following expansion.cc)\<close>

subsubsection \<open>\<open>Generate_F_0_List\<close>\<close>

definition "assert_option s x = (if x then Some () else (let _ = print (String.implode s) in None))"

definition "get_return_grids tlist uppr fg =
  (let ret = get_results (inf_retx fg) (inf_rety fg) (sup_retx fg) (sup_rety fg) tlist
  in if uppr then map mirror_upper ret else ret)"

definition "generate_f0_list total_list upper_list u_min u_max =
  (do {
    let f0_list = [fg\<leftarrow>upper_list. u_min \<le> gridx0 fg \<and> gridx1 fg \<le> u_max];
    let mme = Min (expansion ` set f0_list);
    assert_option ''ERROR: mme > 1\<newline>'' (mme > 1);
    let rgs = get_return_grids total_list True (last f0_list);
    let fd = set rgs \<subseteq> set f0_list;
    assert_option ''ERROR: fundamental domain\<newline>'' fd;
    Some (f0_list, mme)
  })"

subsubsection \<open>\<open>Find_F_0_Inv_Sets\<close>\<close>

definition "find_f0_inv_sets f0_list =
  (let
    space_list = symmetrize f0_list;
    factors = map (\<lambda>it.
      if it \<in> set (get_return_grids space_list True it) then ereal (max (expansion it) (preexpansion it))
      else \<infinity>) f0_list
  in real_of_ereal (Min (set factors)))"

subsubsection \<open>\<open>Generate_F_1_List\<close>\<close>

abbreviation "println s \<equiv> print (String.implode (s @ ''\<newline>''))"

definition "compute_image total_list source_list =
  (let
    r = (fold (\<lambda>it res. (get_return_grids total_list False it @ res)) source_list []);
    rd = remdups r
  in rd)"

definition "generate_f1_list total_list f0_list =
  (let
    f1_list = remdups (map mirror_upper (compute_image total_list f0_list))
  in
    fold (\<lambda>f0 f1_list. List.remove1 f0 f1_list) f0_list f1_list)"

subsection \<open>\<open>Flow_Along\<close>\<close>

definition "flow_along i f1_it f0_list total_list =
  (let
  (_, _, all_good, its, min_acc_exp) = while (\<lambda>(iterate_list, acc_exp, all_good, its, min_min_exp).
      iterate_list \<noteq> [] \<and> all_good)
    (\<lambda>(iterate_list, acc_exp, _, its, min_acc_exp).
      let
        min_exp = Min (expansion ` set iterate_list);
        acc_exp = truncate_down 30 (acc_exp * min_exp);
        image_list = compute_image total_list iterate_list;
        _ = println (''flow_along: '' @ show i @ '' -- '' @ show (gridx0 f1_it, gridx1 f1_it));
        _ = println (''|image_list|: '' @ show (length image_list));
        (mem_f0_list, iterate_list) = List.partition (\<lambda>it. it \<in> set f0_list) image_list;
        _ = println (''|mem_f0_list|: '' @ show (length mem_f0_list));
        _ = println (''acc_exp = '' @ show (acc_exp));
        min_acc_exp = (if mem_f0_list \<noteq> [] then min min_acc_exp (ereal acc_exp) else min_acc_exp);
        res = (iterate_list, acc_exp, mem_f0_list \<noteq> [] \<longrightarrow> acc_exp \<ge> 2,
           Suc its, min_acc_exp)
      in
      res)
    ([f1_it], preexpansion f1_it, True, 0, \<infinity>)
  in (all_good, its, min_acc_exp))"

subsubsection \<open>\<open>Iteration\<close>\<close>

definition "expansion_main upper_list =
  do {
    let total_list = symmetrize upper_list;
    (f0_list, exp_f0) \<leftarrow> generate_f0_list total_list upper_list (-128) (512);
    let exp_f0_inv = find_f0_inv_sets f0_list;
    assert_option ''ERROR: find_f0_inv_sets: '' (exp_f0_inv > ub_sqrt 30 2);
    let f1_list = generate_f1_list total_list f0_list;
    let f0_list = symmetrize f0_list;
    (_, max_its, min_acc_exp) \<leftarrow> fold (\<lambda>f1_it i. do {
        (i, max_its, min_min_acc_exp) \<leftarrow> i;
        let _ = println ((shows ''Grid # '' o shows i o shows ''/'' o shows (length f1_list)) '''');
        let (all_good, its, min_acc_exp) = flow_along i f1_it f0_list total_list;
        assert_option ''flow_along failed'' all_good;
        Some (Suc i, max max_its its, min min_min_acc_exp min_acc_exp)
      }) f1_list (Some (0, 0, \<infinity>));
    let _ = println (show ''EXPANSION_MAIN finished'');
    let _ = println ((shows ''smallest accumulated expansion for orbits returning to F: '' o shows (real_of_ereal min_acc_exp)) '''');
    let _ = println ((shows ''the smallest expansion factor for orbits confined to F: '' o shows exp_f0_inv) '''');
    let _ = println ((shows ''minimal expansion in F: '' o shows exp_f0) '''');
    let _ = println ((shows ''longest number of iterates: '' o shows max_its) '''');
    Some True
  }"

end
