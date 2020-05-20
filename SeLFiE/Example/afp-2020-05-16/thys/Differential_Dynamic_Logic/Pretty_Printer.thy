theory "Pretty_Printer" 
imports
  Ordinary_Differential_Equations.ODE_Analysis
  "Ids"
  "Lib"
  "Syntax"
begin
context ids begin

section\<open>Syntax Pretty-Printer\<close>
text \<open>
  The deeply-embedded syntax is difficult to read for large formulas.
  This pretty-printer produces a more human-friendly syntax, 
  which can be helpful if you want to produce a proof term by hand for
  the proof checker (not recommended for most users).
\<close>
  
fun join :: "string \<Rightarrow> char list list \<Rightarrow> char list"
where "join S [] = []"
  | "join S [S'] = S'"
  | "join S (S' # SS) = S' @ S @ (join S SS)"

 
fun vid_to_string::"'sz \<Rightarrow> char list"
where "vid_to_string vid = (if vid = vid1 then ''x'' else if vid = vid2 then ''y'' else if vid = vid3 then ''z'' else ''w'')" 

fun oid_to_string::"'sz \<Rightarrow> char list"
where "oid_to_string vid = (if vid = vid1 then ''c'' else if vid = vid2 then ''c2'' else if vid = vid3 then ''c3'' else ''c4'')" 

fun cid_to_string::"'sc \<Rightarrow> char list"
where "cid_to_string vid = (if vid = pid1 then ''C'' else if vid = pid2 then ''C2'' else if vid = pid3 then ''C3'' else ''C4'')" 

fun ppid_to_string::"'sc \<Rightarrow> char list"
where "ppid_to_string vid = (if vid = pid1 then ''P'' else if vid = pid2 then ''Q'' else if vid = pid3 then ''R'' else ''H'')" 

fun hpid_to_string::"'sz \<Rightarrow> char list"
where "hpid_to_string vid = (if vid = vid1 then ''a'' else if vid = vid2 then ''b'' else if vid = vid3 then ''a1'' else ''b1'')" 

fun fid_to_string::"'sf \<Rightarrow> char list"
where "fid_to_string vid = (if vid = fid1 then ''f'' else if vid = fid2 then ''g'' else if vid = fid3 then ''h'' else ''j'')" 

primrec trm_to_string::"('sf,'sz) trm \<Rightarrow> char list"
where  
  "trm_to_string (Var x) = vid_to_string x"
| "trm_to_string (Const r) = ''r''"
| "trm_to_string (Function f args) = fid_to_string f"
| "trm_to_string (Plus t1 t2) = trm_to_string t1 @ ''+'' @ trm_to_string t2"
| "trm_to_string (Times t1 t2) = trm_to_string t1 @ ''*'' @ trm_to_string t2"
| "trm_to_string (DiffVar x) = ''Dv{'' @ vid_to_string x @ ''}''"
| "trm_to_string (Differential t) = ''D{'' @ trm_to_string t @ ''}''"
  
primrec ode_to_string::"('sf,'sz) ODE \<Rightarrow> char list"
where  
  "ode_to_string (OVar x) = oid_to_string x"
| "ode_to_string (OSing x t) = ''d'' @ vid_to_string x @ ''='' @ trm_to_string t"
| "ode_to_string (OProd ODE1 ODE2) = ode_to_string ODE1 @ '', '' @ ode_to_string ODE2 "
     
fun fml_to_string ::"('sf, 'sc, 'sz) formula \<Rightarrow> char list"
and hp_to_string ::"('sf, 'sc, 'sz) hp \<Rightarrow> char list"
where 
    "fml_to_string (Geq t1 t2) =  trm_to_string t1 @ ''>='' @ trm_to_string t2"
  | "fml_to_string (Prop p args) = []"
  | "fml_to_string (Not p) = 
     (case p of (And (Not q) (Not (Not p))) \<Rightarrow> fml_to_string p @ ''->'' @ fml_to_string q
               | (Exists x (Not p)) \<Rightarrow> ''A''@ vid_to_string x @ ''.'' @ fml_to_string p
               | (Diamond a (Not p)) \<Rightarrow> ''[''@ hp_to_string a @ '']'' @ fml_to_string p
               | (And (Not (And p q)) (Not (And (Not p') (Not q')))) \<Rightarrow> 
                (if (p = p' \<and> q = q') then fml_to_string p @ ''<->'' @ fml_to_string q else ''!'' @ fml_to_string (And (Not (And p q)) (Not (And (Not p') (Not q')))))
               | _ \<Rightarrow> ''!'' @ fml_to_string p)"
  | "fml_to_string (And p q) = fml_to_string p @ ''&'' @ fml_to_string q"
  | "fml_to_string (Exists x p) = ''E'' @ vid_to_string x @ '' . '' @ fml_to_string p"
  | "fml_to_string (Diamond a p) = ''<'' @ hp_to_string a @ ''>'' @ fml_to_string p"
  | "fml_to_string (InContext C p) = 
      (case p of
        (Geq  _ _) \<Rightarrow> ppid_to_string C
      | _ \<Rightarrow> cid_to_string C @ ''('' @ fml_to_string p @ '')'')"
  
  | "hp_to_string (Pvar a) = hpid_to_string a"
  | "hp_to_string (Assign x e) = vid_to_string x @ '':='' @ trm_to_string e"
  | "hp_to_string (DiffAssign x e) = ''D{'' @ vid_to_string x @ ''}:='' @ trm_to_string e"
  | "hp_to_string (Test p) = ''?'' @ fml_to_string p"
  | "hp_to_string (EvolveODE ODE p) = ''{'' @ ode_to_string ODE @ ''&'' @ fml_to_string p @ ''}''"
  | "hp_to_string (Choice a b) = hp_to_string a @ ''U'' @ hp_to_string b"
  | "hp_to_string (Sequence a b) = hp_to_string a @ '';'' @ hp_to_string b"
  | "hp_to_string (Loop a) = hp_to_string a @ ''*''"
    
end end
