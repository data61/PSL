theory "Ids"
imports Complex_Main
  "Syntax"
begin
text \<open>Some specific identifiers used in Axioms\<close>
abbreviation hgid1::ident where "hgid1 \<equiv> CHR ''a''"
abbreviation hgid2::ident where "hgid2 \<equiv> CHR ''b''"
abbreviation hgidc::ident where "hgidc \<equiv> CHR ''c''"
abbreviation hgidd::ident where "hgidd \<equiv> CHR ''d''"
abbreviation pid1::ident  where "pid1  \<equiv> CHR ''p''"
abbreviation pid2::ident  where "pid2  \<equiv> CHR ''q''"
abbreviation fid1::ident  where "fid1  \<equiv> CHR ''f''"
abbreviation xid1::variable where "xid1  \<equiv> RVar (CHR ''x'')"
end
