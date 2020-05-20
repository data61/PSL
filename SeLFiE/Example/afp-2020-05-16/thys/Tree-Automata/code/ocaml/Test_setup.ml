module Test_setup =
struct
  open List;;
  open Ta;;
  
  (* Build tree automaton *)
  let cnv_rule r = match r with 
    ((q,f,qs)) -> Ta.Rule (Ta.nat_of_integer (Z.of_int q), Ta.nat_of_integer (Z.of_int f), map (fun i -> Ta.nat_of_integer (Z.of_int i)) qs)
  ;;
  
  let createFta initial rules =
    let f1 = fold_left (fun a q -> Ta.htai_add_qi (Ta.nat_of_integer (Z.of_int q)) a) (Ta.htai_empty ()) initial in
      fold_left (fun a r -> Ta.htai_add_rule (cnv_rule r) a) f1 rules
  ;;
  
  (* Return info about tree automaton *)
  let info h =
    Z.to_string (Ta.integer_of_nat (Ta.ls_size (Ta.hta_delta h))) ^ " Rules"
  ;;
  
  (* Tree pretty printer *)
  
  let rec concpad pad l = 
    match l with
      [] -> "" |
      [s] -> s |
      s::ss -> s ^ pad ^ concpad pad ss
  ;;
  
  let rec pretty_tree  n = match n with 
    (Ta.Node(f, [])) -> Z.to_string (Ta.integer_of_nat f) |
    (Ta.Node(f,ts)) -> Z.to_string (Ta.integer_of_nat f) ^ "(" ^ concpad ", " (map pretty_tree ts) ^ ")"
  ;;
  
  let pretty_witness w = match w with
    None -> "none" |
    Some t -> pretty_tree t
  ;;

end;;
