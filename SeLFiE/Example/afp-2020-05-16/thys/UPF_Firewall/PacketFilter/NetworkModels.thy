(*****************************************************************************
 * Copyright (c) 2005-2010 ETH Zurich, Switzerland
 *               2008-2015 Achim D. Brucker, Germany
 *               2009-2016 Université Paris-Sud, France
 *               2015-2016 The University of Sheffield, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *****************************************************************************)

section\<open>Network Models\<close>
theory            
  NetworkModels
  imports
    DatatypeAddress
    DatatypePort

    IntegerAddress
    IntegerPort
    IntegerPort_TCPUDP

    IPv4
    IPv4_TCPUDP
begin

text\<open>
  One can think of many different possible address representations. In this distribution, we include 
  seven different variants:
  \begin{itemize} 
    \item DatatypeAddress: Three explicitly named addresses, which build up a network consisting of 
          three disjunct  subnetworks. I.e. there are no overlaps and there is no way to distinguish 
          between individual hosts within a network.
    \item DatatypePort: An address is a pair, with the first element being the same as above, and 
          the second being a port number modelled as an Integer\footnote{For technical reasons,
          we always use Integers instead of Naturals. As a consequence, the (test) specifications 
          have to be adjusted to eliminate negative numbers.}.
    \item adr\_i: An address in an Integer.
    \item adr\_ip: An address is a pair of an Integer and a port (which is again an Integer).
    \item adr\_ipp: An address is a triple consisting of two Integers modelling the IP address and 
          the port number, and the specification of the network protocol
    \item IPv4: An address is a pair. The first element is a four-tuple of Integers, modelling an 
          IPv4 address, the second element is an Integer denoting the port number.
    \item IPv4\_TCPUDP: The same as above, but including additionally the specification of the 
          network protocol.
  \end{itemize}

  The theories of each pf the networks are relatively small. It suffices to provide the required 
  types, a couple of lemmas, and - if required - a definition for the source and destination ports 
  of a packet.
\<close>

end
