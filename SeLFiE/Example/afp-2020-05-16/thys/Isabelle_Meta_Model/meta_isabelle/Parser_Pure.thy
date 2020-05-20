(******************************************************************************
 * A Meta-Model for the Isabelle API
 *
 * Copyright (c) 2011-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2017 IRT SystemX, France
 *               2011-2015 Achim D. Brucker, Germany
 *               2016-2018 The University of Sheffield, UK
 *               2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
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
 ******************************************************************************)

section\<open>Instantiating the Parser of (Pure) Term\<close>

theory  Parser_Pure
imports Meta_Pure
        Parser_init
begin

subsection\<open>Main\<close>

context Parse
begin

definition "of_pure_indexname a b = of_pair a b (of_string a b) (of_nat a b)"

definition "of_pure_class = of_string"

definition "of_pure_sort a b = of_list a b (of_pure_class a b)"

definition "of_pure_typ a b = rec_typ
  (ap2 a (b \<open>Type\<close>) (of_string a b) (of_list a b snd))
  (ap2 a (b \<open>TFree\<close>) (of_string a b) (of_pure_sort a b))
  (ap2 a (b \<open>TVar\<close>) (of_pure_indexname a b) (of_pure_sort a b))"

definition "of_pure_term a b = (\<lambda>f0 f1 f2 f3 f4 f5. rec_term f0 f1 f2 f3 (co2 K f4) (\<lambda>_ _. f5))
  (ap2 a (b \<open>Const\<close>) (of_string a b) (of_pure_typ a b))
  (ap2 a (b \<open>Free\<close>) (of_string a b) (of_pure_typ a b))
  (ap2 a (b \<open>Var\<close>) (of_pure_indexname a b) (of_pure_typ a b))
  (ap1 a (b \<open>Bound\<close>) (of_nat a b))
  (ar3 a (b \<open>Abs\<close>) (of_string a b) (of_pure_typ a b))
  (ar2 a (b \<open>App\<close>) id)"

end

lemmas [code] =
  Parse.of_pure_indexname_def
  Parse.of_pure_class_def
  Parse.of_pure_sort_def
  Parse.of_pure_typ_def
  Parse.of_pure_term_def

end
