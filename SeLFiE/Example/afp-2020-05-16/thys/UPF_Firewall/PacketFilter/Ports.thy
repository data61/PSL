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

subsection \<open>Ports\<close>
theory Ports
  imports 
    Main
begin

text\<open>
  This theory can be used if we want to specify the port numbers by names denoting their default 
  Integer values. If you want to use them, please add \<open>Ports\<close> to the simplifier.
\<close>

definition http::int where "http = 80"

lemma http1: "x \<noteq> 80 \<Longrightarrow> x \<noteq> http"
  by (simp add: http_def)

lemma http2: "x \<noteq> 80 \<Longrightarrow> http \<noteq> x"
  by (simp add: http_def)

definition smtp::int where "smtp = 25"

lemma smtp1: "x \<noteq> 25 \<Longrightarrow> x \<noteq> smtp"
  by (simp add: smtp_def)

lemma smtp2: "x \<noteq> 25 \<Longrightarrow> smtp \<noteq> x"
  by (simp add: smtp_def)

definition ftp::int where "ftp = 21"

lemma ftp1: "x \<noteq> 21 \<Longrightarrow> x \<noteq> ftp"
  by (simp add: ftp_def)

lemma ftp2: "x \<noteq> 21 \<Longrightarrow> ftp \<noteq> x"
  by (simp add: ftp_def)

text\<open>And so on for all desired port numbers.\<close>

lemmas Ports = http1 http2 ftp1 ftp2 smtp1 smtp2

end
