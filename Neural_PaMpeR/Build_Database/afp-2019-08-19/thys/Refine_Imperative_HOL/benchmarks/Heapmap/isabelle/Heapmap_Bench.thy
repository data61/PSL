theory Heapmap_Bench
imports 
  "../../../IICF/Impl/Heaps/IICF_Impl_Heapmap"
  "../../../Sepref_ICF_Bindings"
begin

definition rrand :: "uint32 \<Rightarrow> uint32" 
  where "rrand s \<equiv> (s * 1103515245 + 12345) AND 0x7FFFFFFF"

definition rand :: "uint32 \<Rightarrow> nat \<Rightarrow> (uint32 * nat)" where
  "rand s m \<equiv> let
    s = rrand s;
    r = nat_of_uint32 s;
    r = (r * m) div 0x80000000
  in (s,r)"

partial_function (heap) rep where "rep i N f s = (
  if i<N then do {
    s \<leftarrow> f s i;
    rep (i+1) N f s
  } else return s
)"

declare rep.simps[code]

term hm_insert_op_impl

definition "testsuite N \<equiv> do {
  let s=0;
  let N2=efficient_nat_div2 N;
  hm \<leftarrow> hm_empty_op_impl N;

  (hm,s) \<leftarrow> rep 0 N (\<lambda>(hm,s) i. do {
    let (s,v) = rand s N2;
    hm \<leftarrow> hm_insert_op_impl N id i v hm;
    return (hm,s)
  }) (hm,s);


  (hm,s) \<leftarrow> rep 0 N (\<lambda>(hm,s) i. do {
    let (s,v) = rand s N2;
    hm \<leftarrow> hm_change_key_op_impl id i v hm;
    return (hm,s)
  }) (hm,s);


  hm \<leftarrow> rep 0 N (\<lambda>hm i. do {
    (_,hm) \<leftarrow> hm_pop_min_op_impl id hm;
    return hm
  }) hm;


  return ()
}"

export_code rep in SML_imp

partial_function (tailrec) drep where "drep i N f s = (
  if i<N then drep (i+1) N f (f s i)
  else s
)"

declare drep.simps[code]


term aluprioi.insert
term aluprioi.empty
term aluprioi.pop

definition "ftestsuite N \<equiv> do {
  let s=0;
  let N2=efficient_nat_div2 N;
  let hm= aluprioi.empty ();

  let (hm,s) = drep 0 N (\<lambda>(hm,s) i. do {
    let (s,v) = rand s N2;
    let hm = aluprioi.insert hm i v;
    (hm,s)
  }) (hm,s);

  let (hm,s) = drep 0 N (\<lambda>(hm,s) i. do {
    let (s,v) = rand s N2;
    let hm = aluprioi.insert hm i v;
    (hm,s)
  }) (hm,s);

  let hm = drep 0 N (\<lambda>hm i. do {
    let (_,_,hm) = aluprioi.pop hm;
    hm
  }) hm;

  ()
}"


export_code 
  testsuite ftestsuite
  nat_of_integer integer_of_nat
  in SML_imp module_name Heapmap
  file \<open>heapmap_export.sml\<close>

end
