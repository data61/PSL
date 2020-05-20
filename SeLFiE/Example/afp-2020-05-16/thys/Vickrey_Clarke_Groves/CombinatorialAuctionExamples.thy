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

section \<open>VCG auction: three simple examples evaluating the VCG allocation algorithm
          vcgaAlg and the price determination algorithm vcgpAlg in Isabelle\<close>

theory CombinatorialAuctionExamples

imports
CombinatorialAuction

begin

(* The following counterexample is built by deleting the additional assumption that n1 \<noteq> n2. *)
(* Since this a "false" theorem, the following needs to be commented out, since otherwise
   the subsequent lines will fail. *)
(* theorem counterexample_allocationDisjoint: 
  assumes "a \<in> allocationsUniverse" "n1\<in> Domain a" "n2 \<in> Domain a"
  shows "a,,,n1 \<inter> a,,,n2 = {}" nitpick
*)


(* Test example 1 for evaluation of vcga and vcgp in Isabelle *)
definition "r1 = 0" (* r1 in {0, 1, 2, ... 23 *)
definition "N1 = {1,2,3::integer}"
definition "\<Omega>1 = [11, 12]"
definition "b1 = {((1::integer, {11::integer, 12}), 2::nat),
                  ((2,          {11}),          2),
                  ((2,          {12}),          2),
                  ((3,          {11}),          2),
                  ((3,          {12}),          2)}"
definition "vcga1 = vcgaAlg N1 \<Omega>1 (b1 Elsee 0) r1"

value "vcga1"
value [nbe] "vcgpAlg N1 \<Omega>1 (b1 Elsee 0) r1 1 vcga1"
value [nbe] "vcgpAlg N1 \<Omega>1 (b1 Elsee 0) r1 2 vcga1"
value [nbe] "vcgpAlg N1 \<Omega>1 (b1 Elsee 0) r1 3 vcga1"

(* Test example 2 for evaluation of vcga and vcgp in Isabelle *)
definition "r2 = 1" (* r1 in {0, 1, 2, ... 23 *)
definition "N2 = {1,2,3::integer}"
definition "\<Omega>2 = [11, 12]"
definition "b2 = {((1::integer, {11::integer, 12}), 5::nat),
                  ((2,          {11}),              3),
                  ((2,          {12}),              3),
                  ((3,          {11}),              2),
                  ((3,          {12}),              4)}"
definition "vcga2 = vcgaAlg N2 \<Omega>2 (b2 Elsee 0) r2"

value "vcga2"
value [nbe] "vcgpAlg N2 \<Omega>2 (b2 Elsee 0) r2 1 vcga2"
value [nbe] "vcgpAlg N2 \<Omega>2 (b2 Elsee 0) r2 2 vcga2"
value [nbe] "vcgpAlg N2 \<Omega>2 (b2 Elsee 0) r2 3 vcga2"


(* Test example 3 for evaluation of vcga and vcgp in Isabelle *)
definition "r3 = 0" (* r1 in {0, 1, 2, ... 47 *)
definition "N3 = {1,2,3::integer}"
definition "\<Omega>3 = [11, 12, 13]"
definition "b3 = {((1::integer, {11::integer, 12, 13}), 20::nat),
                  ((1,          {11,12}),               18),
                  ((2,          {11}),                  10),
                  ((2,          {12}),                  15),
                  ((2,          {13}),                  15),
                  ((2,          {12,13}),               18),
                  ((3,          {11}),                   2),
                  ((3,          {11,12}),               12),
                  ((3,          {11,13}),               17),
                  ((3,          {12,13}),               18),
                  ((3,          {11,12,13}),            19)}"
definition "vcga3 = vcgaAlg N3 \<Omega>3 (b3 Elsee 0) r3"

value "vcga3"
value [nbe] "vcgpAlg N3 \<Omega>3 (b3 Elsee 0) r3 1 vcga3"
value [nbe] "vcgpAlg N3 \<Omega>3 (b3 Elsee 0) r3 2 vcga3"
value [nbe] "vcgpAlg N3 \<Omega>3 (b3 Elsee 0) r3 3 vcga3"

end
