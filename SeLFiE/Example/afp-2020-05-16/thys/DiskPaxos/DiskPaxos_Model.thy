(*  Title:       Proving the Correctness of Disk Paxos

    Author:      Mauro J. Jaskelioff, Stephan Merz, 2005
    Maintainer:  Mauro J. Jaskelioff <mauro at fceia.unr.edu.ar>
*)

section "Disk Paxos Algorithm Specification"

theory DiskPaxos_Model imports Main begin

text\<open>This is the specification of the Disk Synod algorithm.\<close>

typedecl InputsOrNi
typedecl Disk
typedecl Proc

axiomatization
  Inputs :: "InputsOrNi set" and
  NotAnInput :: "InputsOrNi" and
  Ballot :: "Proc \<Rightarrow> nat set" and
  IsMajority :: "Disk set \<Rightarrow> bool"
where
  NotAnInput: "NotAnInput \<notin> Inputs" and
  InputsOrNi: "(UNIV :: InputsOrNi set) = Inputs \<union> {NotAnInput}" and
  Ballot_nzero: "\<forall>p. 0 \<notin> Ballot p" and
  Ballot_disj: "\<forall>p q. p \<noteq> q \<longrightarrow> (Ballot p) \<inter> (Ballot q) = {}" and
  Disk_isMajority: "IsMajority(UNIV)" and
  majorities_intersect: 
    "\<forall>S T. IsMajority(S) \<and> IsMajority(T) \<longrightarrow> S \<inter> T \<noteq> {}"

lemma ballots_not_zero [simp]:
  "b \<in> Ballot p \<Longrightarrow> 0 < b"
proof (rule ccontr)
  assume b: "b \<in> Ballot p"
  and contr: "\<not> (0 < b)"
  from Ballot_nzero
  have "0 \<notin> Ballot p" ..
  with b contr 
  show "False"
    by auto
qed

lemma majority_nonempty [simp]: "IsMajority(S) \<Longrightarrow> S \<noteq> {}"
proof(auto)
  from majorities_intersect
  have "IsMajority({}) \<and> IsMajority({}) \<longrightarrow> {} \<inter> {} \<noteq> {}"
    by auto
  thus "IsMajority {} \<Longrightarrow> False"
    by auto
qed

definition AllBallots :: "nat set"
  where "AllBallots = (UN p. Ballot p)"

record
  DiskBlock = 
    mbal:: nat
    bal :: nat
    inp :: InputsOrNi

definition InitDB :: DiskBlock
  where "InitDB = \<lparr> mbal = 0, bal = 0, inp = NotAnInput \<rparr>"

record
  BlockProc =
    block :: DiskBlock
    proc  :: Proc
 
record 
  state =
    inpt :: "Proc \<Rightarrow> InputsOrNi"
    outpt :: "Proc \<Rightarrow> InputsOrNi"
    disk :: "Disk \<Rightarrow> Proc \<Rightarrow> DiskBlock"
    dblock :: "Proc \<Rightarrow> DiskBlock"
    phase :: "Proc \<Rightarrow> nat"
    disksWritten :: "Proc \<Rightarrow> Disk set"
    blocksRead :: "Proc \<Rightarrow> Disk \<Rightarrow> BlockProc set"
  (* History Variables *) 
    allInput  :: "InputsOrNi set"
    chosen    :: "InputsOrNi"


definition hasRead :: "state \<Rightarrow> Proc \<Rightarrow> Disk \<Rightarrow> Proc \<Rightarrow> bool"
  where "hasRead s p d q = (\<exists> br \<in> blocksRead s p d. proc br = q)"

definition allRdBlks :: "state \<Rightarrow> Proc \<Rightarrow> BlockProc set"
  where "allRdBlks s p = (UN d. blocksRead s p d)"

definition allBlocksRead :: "state \<Rightarrow> Proc \<Rightarrow> DiskBlock set"
  where "allBlocksRead s p = block ` (allRdBlks s p)"

definition Init :: "state \<Rightarrow> bool"
  where
    "Init s =
      (range (inpt s) \<subseteq> Inputs
     & outpt s = (\<lambda>p. NotAnInput)
     & disk s = (\<lambda>d p. InitDB)
     & phase s = (\<lambda>p. 0)
     & dblock s = (\<lambda>p. InitDB)
     & disksWritten s = (\<lambda>p. {})
     & blocksRead s = (\<lambda>p d. {}))"

definition InitializePhase :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> bool"
  where
  "InitializePhase s s' p =
    (disksWritten s' = (disksWritten s)(p := {})
   & blocksRead s' = (blocksRead s)(p := (\<lambda>d. {})))"

definition StartBallot :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> bool"
where
  "StartBallot s s' p =
    (phase s p \<in> {1,2}
   & phase s' = (phase s)(p := 1)
   & (\<exists>b \<in> Ballot p. 
         mbal (dblock s p) < b
       & dblock s' = (dblock s)(p := (dblock s p)\<lparr> mbal := b \<rparr>))
   & InitializePhase s s' p
   & inpt s' = inpt s & outpt s' = outpt s & disk s' = disk s)"

definition Phase1or2Write :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> Disk \<Rightarrow> bool"
where
  "Phase1or2Write s s' p d =
    (phase s p \<in> {1, 2}
   \<and> disk s' = (disk s) (d := (disk s d) (p := dblock s p)) 
   \<and> disksWritten s' = (disksWritten s) (p:= (disksWritten s p) \<union> {d})
   \<and> inpt s' = inpt s \<and> outpt s'= outpt s
   \<and> phase s' = phase s \<and> dblock s' = dblock s
   \<and> blocksRead s'= blocksRead s)"

definition Phase1or2ReadThen :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> Disk \<Rightarrow> Proc \<Rightarrow> bool"
where
  "Phase1or2ReadThen s s' p d q =
    (d \<in> disksWritten s p
   & mbal(disk s d q) < mbal(dblock s p)
   & blocksRead s' = (blocksRead s)(p := (blocksRead s p)(d :=
                       (blocksRead s p d) \<union> {\<lparr> block = disk s d q,
                                               proc = q \<rparr>}))
   & inpt s' = inpt s & outpt s' = outpt s
   & disk s' = disk s & phase s' = phase s
   & dblock s' = dblock s & disksWritten s' = disksWritten s)"

definition Phase1or2ReadElse :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> Disk \<Rightarrow> Proc \<Rightarrow> bool"
where
  "Phase1or2ReadElse s s' p d q =
    (d \<in> disksWritten s p
   \<and> StartBallot s s' p)"

definition Phase1or2Read :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> Disk \<Rightarrow> Proc \<Rightarrow> bool"
where
  "Phase1or2Read s s' p d q =
     (Phase1or2ReadThen s s' p d q
    \<or> Phase1or2ReadElse s s' p d q)"

definition blocksSeen :: "state \<Rightarrow> Proc \<Rightarrow> DiskBlock set"
  where "blocksSeen s p = allBlocksRead s p \<union> {dblock s p}"

definition nonInitBlks :: "state \<Rightarrow> Proc \<Rightarrow> DiskBlock set"
  where"nonInitBlks s p = {bs . bs \<in> blocksSeen s p \<and> inp bs \<in> Inputs}"

definition maxBlk :: "state \<Rightarrow> Proc \<Rightarrow> DiskBlock"
where
  "maxBlk s p =
     (SOME b. b \<in> nonInitBlks s p \<and> (\<forall>c \<in> nonInitBlks s p. bal c \<le> bal b))"

definition EndPhase1 :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> bool"
where
  "EndPhase1 s s' p =
    (IsMajority {d . d \<in> disksWritten s p
                     \<and> (\<forall>q \<in> UNIV - {p}. hasRead s p d q)}
   \<and> phase s p = 1
   \<and> dblock s' = (dblock s) (p := dblock s p 
           \<lparr> bal := mbal(dblock s p),
             inp := 
              (if nonInitBlks s p = {}
               then inpt s p
               else inp (maxBlk s p))
           \<rparr> )
   \<and> outpt s' = outpt s
   \<and> phase s' = (phase s) (p := phase s p + 1)
   \<and> InitializePhase s s' p
   \<and> inpt s' = inpt s \<and> disk s' = disk s)"

definition EndPhase2 :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> bool"
where
  "EndPhase2 s s' p =
    (IsMajority {d . d \<in> disksWritten s p
                     \<and> (\<forall>q \<in> UNIV - {p}. hasRead s p d q)}
   \<and> phase s p = 2
   \<and> outpt s' = (outpt s) (p:= inp (dblock s p))
   \<and> dblock s' = dblock s
   \<and> phase s' = (phase s) (p := phase s p + 1)
   \<and> InitializePhase s s' p
   \<and> inpt s' = inpt s \<and> disk s' = disk s)"

definition EndPhase1or2 :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> bool"
  where "EndPhase1or2 s s' p = (EndPhase1 s s' p \<or> EndPhase2 s s' p)"

definition Fail :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> bool"
where
  "Fail s s' p =
    (\<exists>ip \<in> Inputs. inpt s' = (inpt s) (p := ip)
   \<and> phase s' = (phase s) (p := 0)
   \<and> dblock s'= (dblock s) (p := InitDB)
   \<and> outpt s' = (outpt s) (p := NotAnInput)
   \<and> InitializePhase s s' p
   \<and> disk s'= disk s)"

definition Phase0Read :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> Disk \<Rightarrow> bool"
where
  "Phase0Read s s' p d =
    (phase s p = 0
   \<and> blocksRead s' = (blocksRead s) (p := (blocksRead s p) (d := blocksRead s p d \<union> {\<lparr> block = disk s d p, proc = p \<rparr>}))
   \<and> inpt s' = inpt s & outpt s' = outpt s
   \<and> disk s' = disk s & phase s' = phase s
   \<and> dblock s' = dblock s & disksWritten s' = disksWritten s)"

definition EndPhase0 :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> bool"
where
  "EndPhase0 s s' p =
    (phase s p = 0
   \<and> IsMajority ({d. hasRead s p d p})
   \<and> (\<exists>b \<in> Ballot p.   
       (\<forall>r \<in> allBlocksRead s p. mbal r < b)
     \<and> dblock s' = (dblock s) ( p:= 
                    (SOME r.   r \<in> allBlocksRead s p 
                            \<and> (\<forall>s \<in> allBlocksRead s p. bal s \<le>  bal r)) \<lparr> mbal := b \<rparr> ))
   \<and> InitializePhase s s' p
   \<and> phase s' = (phase s) (p:= 1)
   \<and> inpt s' = inpt s \<and> outpt s' = outpt s \<and> disk s' = disk s)"

definition Next :: "state \<Rightarrow> state \<Rightarrow> bool"
where
  "Next s s' = (\<exists>p.
                  StartBallot s s' p
                \<or> (\<exists>d.   Phase0Read s s' p d
                       \<or> Phase1or2Write s s' p d
                       \<or> (\<exists>q. q \<noteq> p \<and> Phase1or2Read s s' p d q))
                \<or> EndPhase1or2 s s' p
                \<or> Fail s s' p
                \<or> EndPhase0 s s' p)"

text \<open>
  In the following, for each action or state {\em name} we name
  {\em Hname} the corresponding action that includes 
  the history part of the HNext action or state predicate that includes 
  history variables.
\<close>

definition HInit :: "state \<Rightarrow> bool"
where
  "HInit s =
    (Init s
   & chosen s = NotAnInput
   & allInput s = range (inpt s))"

text \<open>HNextPart is the part of the Next action 
        that is concerned with history variables.
\<close>

definition HNextPart :: "state \<Rightarrow> state => bool"
where
  "HNextPart s s' =
    (chosen s' = 
       (if chosen s \<noteq> NotAnInput \<or> (\<forall>p. outpt s' p = NotAnInput )
            then chosen s
            else outpt s' (SOME p. outpt s' p \<noteq> NotAnInput))
   \<and> allInput s' = allInput s \<union> (range (inpt s')))"

definition HNext :: "state \<Rightarrow> state \<Rightarrow> bool"
where
  "HNext s s' =
     (Next s s'
   \<and> HNextPart s s')"

text \<open>
  We add HNextPart to every action (rather than proving that Next 
  maintains the HInv invariant) to make proofs easier. 
\<close>

definition
  HPhase1or2ReadThen :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> Disk \<Rightarrow> Proc \<Rightarrow> bool" where
  "HPhase1or2ReadThen s s' p d q = (Phase1or2ReadThen s s' p d q \<and> HNextPart s s')" 

definition
  HEndPhase1 :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> bool" where
  "HEndPhase1 s s' p = (EndPhase1 s s' p \<and> HNextPart s s')" 

definition
  HStartBallot :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> bool" where
  "HStartBallot s s' p = (StartBallot s s' p \<and> HNextPart s s')"

definition
  HPhase1or2Write :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> Disk \<Rightarrow> bool" where
  "HPhase1or2Write s s' p d = (Phase1or2Write s s' p d \<and> HNextPart s s')" 

definition
  HPhase1or2ReadElse :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> Disk \<Rightarrow> Proc \<Rightarrow> bool" where
  "HPhase1or2ReadElse s s' p d q = (Phase1or2ReadElse s s' p d q \<and> HNextPart s s')" 

definition
  HEndPhase2 :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> bool" where
  "HEndPhase2 s s' p = (EndPhase2 s s' p \<and> HNextPart s s')"

definition
  HFail :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> bool" where
  "HFail s s' p = (Fail s s' p  \<and> HNextPart s s')"

definition
  HPhase0Read :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> Disk \<Rightarrow> bool" where
  "HPhase0Read s s' p d = (Phase0Read s s' p d \<and> HNextPart s s')"

definition
  HEndPhase0 :: "state \<Rightarrow> state \<Rightarrow> Proc \<Rightarrow> bool" where
  "HEndPhase0 s s' p = (EndPhase0 s s' p \<and> HNextPart s s')"  

text \<open>
  Since these definitions are the conjunction of two other definitions 
  declaring them as simplification rules should be harmless.
\<close>

declare HPhase1or2ReadThen_def [simp]
declare HPhase1or2ReadElse_def [simp]
declare HEndPhase1_def  [simp]
declare HStartBallot_def  [simp]
declare HPhase1or2Write_def [simp]
declare HEndPhase2_def [simp]
declare HFail_def [simp]
declare HPhase0Read_def [simp]
declare HEndPhase0_def [simp]

end
