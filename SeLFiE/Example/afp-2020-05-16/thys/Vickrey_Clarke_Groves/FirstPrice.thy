(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati http://caminati.co.nr
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

section \<open>First-price auction: adapted from VCG auction\<close>

theory FirstPrice

imports
CombinatorialAuction


begin

(* In a first price auction we use the same allocation algorithm as in a VCG auction. 
   The price a winning bidder has to pay is given by evaluating b with respect to the bidder
   and the set he/she gets. *)
abbreviation "firstPriceP N \<Omega> b r n ==
  b (n, winningAllocationAlg N \<Omega> r b,, n)"

(* The non-negativity of prices follows immediately from the assumptions that all bids are
   non-negative. *)
theorem NonnegFirstPrices:
   assumes "\<forall> X. b (n, X) \<ge> 0" 
   shows "firstPriceP N \<Omega> b r n \<ge> 0" 
   using assms by blast
end

