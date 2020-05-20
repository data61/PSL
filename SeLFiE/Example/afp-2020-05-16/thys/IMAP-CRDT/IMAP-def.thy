section \<open>IMAP-CRDT Definitions\<close>

text\<open>We begin by defining the operations on a mailbox state. In addition to the interpretation of 
the operations, we define valid behaviours for the operations as assumptions for the network.
We use the \texttt{network\_with\_constrained\_ops} locale from the framework.\<close>

theory
  "IMAP-def"
  imports
    "CRDT.Network"
begin

datatype ('id, 'a) operation = 
  Create "'id" "'a" | 
  Delete "'id set" "'a" | 
  Append "'id" "'a" | 
  Expunge "'a" "'id" "'id" | 
  Store "'a" "'id" "'id"

type_synonym ('id, 'a) state = "'a \<Rightarrow> ('id set \<times> 'id set)"

definition op_elem :: "('id, 'a) operation \<Rightarrow> 'a" where
  "op_elem oper \<equiv> case oper of 
    Create i e \<Rightarrow> e | 
    Delete is e \<Rightarrow> e | 
    Append i e \<Rightarrow> e | 
    Expunge e mo i \<Rightarrow> e | 
    Store e mo i \<Rightarrow> e"

definition interpret_op :: "('id, 'a) operation \<Rightarrow> ('id, 'a) state \<rightharpoonup> ('id, 'a) state" 
  ("\<langle>_\<rangle>" [0] 1000) where
  "interpret_op oper state \<equiv>
    let metadata = fst (state (op_elem oper));
        files = snd (state (op_elem oper));
        after  = case oper of 
          Create i e \<Rightarrow> (metadata \<union> {i}, files) |
          Delete is e \<Rightarrow> (metadata - is, files - is) |
          Append i e \<Rightarrow> (metadata, files \<union> {i}) |
          Expunge e mo i \<Rightarrow> (metadata \<union> {i}, files - {mo}) |
          Store e mo i \<Rightarrow> (metadata, insert i (files - {mo}))
    in  Some (state ((op_elem oper) := after))"

text\<open>In the definition of the valid behaviours of the operations, we define additional assumption 
the state where the operation is executed. In essence, a the tag of a \create, \append, \expunge,  
and \store\ operation is identical to the message number and therefore unique. A \delete\ operation 
deletes all metadata and the content of a folder. The \store\ and \expunge\ operations must refer 
to an existing message.\<close>

definition valid_behaviours :: "('id, 'a) state \<Rightarrow> 'id \<times> ('id, 'a) operation \<Rightarrow> bool" where
  "valid_behaviours state msg \<equiv>
    case msg of
      (i, Create j e) \<Rightarrow> i = j |
      (i, Delete is e) \<Rightarrow> is = fst (state e) \<union> snd (state e) |
      (i, Append j e) \<Rightarrow> i = j |
      (i, Expunge e mo j) \<Rightarrow> i = j \<and> mo \<in> snd (state e) |
      (i, Store e mo j) \<Rightarrow> i = j \<and> mo \<in> snd (state e)"

locale imap = network_with_constrained_ops _ interpret_op "\<lambda>x. ({},{})" valid_behaviours

end
