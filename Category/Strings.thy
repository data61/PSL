(* The type "string list" as monoid. *)
theory Strings
imports Category
begin

ML{* structure Strings_Min : MONOID_MIN =
struct
  type monoid_min = string list;
  val mempty = [];
  fun mappend src1 src2 = src1 @ src2;
end
*}

ML{* structure Strings = mk_Monoid (Strings_Min) : MONOID; *}

end