(*  Title:      RSAPSS/SHA1Padding.thy
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt
*)


section "Message Padding for SHA1"

theory SHA1Padding
imports WordOperations
begin

definition zerocount :: "nat \<Rightarrow> nat" where
  zerocount: "zerocount n = ((((n + 64) div 512) + 1) * 512) - n - (65::nat)"

definition helppadd :: "bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> bv" where
  "helppadd x y n = x @ [One] @ zerolist (zerocount n) @ zerolist (64 - length y) @y"

definition sha1padd :: "bv \<Rightarrow> bv" where
  sha1padd: "sha1padd x = helppadd x (nat_to_bv (length x)) (length x)"

end
