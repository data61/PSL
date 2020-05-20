(*  Title:       variants/c_gtobcast/C_Gtobcast.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
    Author:      Peter Höfner, NICTA
*)

theory %invisible C_Gtobcast
imports "../../Aodv_Basic"
begin

chapter "Variant C: From Groupcast to Broadcast"

text \<open>
  Explanation~\cite[\textsection 10.4]{FehnkerEtAl:AWN:2013}:
  A node maintains a set of `precursor nodes' for each of its valid routes.
  If the link to a route's next hop is lost, an error message is groupcast 
  to the associated precursor nodes. The idea is to reduce the number of
  messages received and handled. However, precursor lists are incomplete. 
  They are updated only when a RREP message is sent. This can lead to packet 
  loss. A possible solution is to abandon precursors and to replace every 
  groupcast by a broadcast. At first glance this strategy seems to need more 
  bandwidth, but this is not the case. Sending error messages to a set of 
  precursors is implemented at the link layer by broadcasting the message 
  anyway; a node receiving such a message then checks the header to 
  determine whether it is one of the intended recipients. Instead of 
  analysing the header only, a node can just as well read the message and 
  decide whether the information contained in the message is of use. To be 
  more precise: an error message is useful for a node if the node has 
  established a route to one of the nodes listed in the message, and the 
  next hop to a listed node is the sender of the error message. In case a 
  node finds useful information inside the message, it should update its 
  routing table and distribute another error message.
\<close>

end %invisible

