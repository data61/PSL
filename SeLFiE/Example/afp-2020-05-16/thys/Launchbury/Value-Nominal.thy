theory "Value-Nominal"
imports Value "Nominal-Utils" "Nominal-HOLCF"
begin

text \<open>Values are pure, i.e. contain no variables.\<close>

instantiation Value :: pure
begin
  definition "p \<bullet> (v::Value) = v"
instance
  apply standard
  apply (auto simp add: permute_Value_def)
  done
end

instance Value :: pcpo_pt
  by standard (simp add: pure_permute_id)

end
