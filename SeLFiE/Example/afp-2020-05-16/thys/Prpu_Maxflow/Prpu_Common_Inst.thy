theory Prpu_Common_Inst
imports 
  Flow_Networks.Refine_Add_Fofu
  Generic_Push_Relabel
begin

context Network 
begin
  definition "relabel f l u \<equiv> do {
    assert (Height_Bounded_Labeling c s t f l);
    assert (relabel_precond f l u);
    assert (u\<in>V-{s,t});
    return (relabel_effect f l u)
  }"
  
  definition "gap_relabel f l u \<equiv> do {
    assert (u\<in>V-{s,t});
    assert (Height_Bounded_Labeling c s t f l);
    assert (relabel_precond f l u);
    assert (l u < 2*card V \<and> relabel_effect f l u u < 2*card V);
    return (gap_relabel_effect f l u)
  }"  

  definition "push f l \<equiv> \<lambda>(u,v). do {
    assert (push_precond f l (u,v));
    assert (Labeling c s t f l);
    return (push_effect f (u,v))
  }"  

end

end
