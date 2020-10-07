theory "CValue-Nominal"
imports CValue "Nominal-Utils" "Nominal-HOLCF"
begin

instantiation C :: pure
begin
  definition "p \<bullet> (c::C) = c"
instance by standard (auto simp add: permute_C_def)
end
instance C :: pcpo_pt
  by standard (simp add: pure_permute_id)


instantiation CValue :: pure
begin
  definition "p \<bullet> (v::CValue) = v"
instance
  apply standard
  apply (auto simp add: permute_CValue_def)
  done
end

instance CValue :: pcpo_pt
  by standard (simp add: pure_permute_id)

end
