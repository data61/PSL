theory "Ids"
imports Complex_Main
begin
section \<open>Identifier locale\<close>
text \<open>The differential dynamic logic formalization is parameterized by the type of identifiers.
  The identifier type(s) must be finite and have at least 3-4 distinct elements.
  Distinctness is required for soundness of some axioms. \<close>
locale ids =
  fixes vid1 :: "('sz::{finite,linorder})"
  fixes vid2 :: 'sz
  fixes vid3 :: 'sz
  fixes fid1 :: "('sf::finite)"
  fixes fid2 :: 'sf
  fixes fid3 :: 'sf
  fixes pid1 :: "('sc::finite)"
  fixes pid2 :: 'sc
  fixes pid3 :: 'sc
  fixes pid4 :: 'sc
  assumes vne12:"vid1 \<noteq> vid2"
  assumes vne23:"vid2 \<noteq> vid3"
  assumes vne13:"vid1 \<noteq> vid3"
  assumes fne12:"fid1 \<noteq> fid2"
  assumes fne23:"fid2 \<noteq> fid3"
  assumes fne13:"fid1 \<noteq> fid3"
  assumes pne12:"pid1 \<noteq> pid2"
  assumes pne23:"pid2 \<noteq> pid3"
  assumes pne13:"pid1 \<noteq> pid3"
  assumes pne14:"pid1 \<noteq> pid4"
  assumes pne24:"pid2 \<noteq> pid4"
  assumes pne34:"pid3 \<noteq> pid4"
context ids begin
lemma id_simps:
  "(vid1 = vid2) = False" "(vid2 = vid3) = False" "(vid1 = vid3) = False"
  "(fid1 = fid2) = False" "(fid2 = fid3) = False" "(fid1 = fid3) = False"
  "(pid1 = pid2) = False" "(pid2 = pid3) = False" "(pid1 = pid3) = False" 
  "(pid1 = pid4) = False" "(pid2 = pid4) = False" "(pid3 = pid4) = False"
  "(vid2 = vid1) = False" "(vid3 = vid2) = False" "(vid3 = vid1) = False"
  "(fid2 = fid1) = False" "(fid3 = fid2) = False" "(fid3 = fid1) = False"
  "(pid2 = pid1) = False" "(pid3 = pid2) = False" "(pid3 = pid1) = False" 
  "(pid4 = pid1) = False" "(pid4 = pid2) = False" "(pid4 = pid3) = False"
  using vne12 vne23 vne13 fne12 fne23 fne13 pne12 pne23 pne13 pne14 pne24 pne34 by auto
end
end
