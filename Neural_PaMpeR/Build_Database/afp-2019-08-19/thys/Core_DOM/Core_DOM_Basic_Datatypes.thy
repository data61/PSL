(***********************************************************************************
 * Copyright (c) 2016-2018 The University of Sheffield, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * SPDX-License-Identifier: BSD-2-Clause
 *******************************************************************************\***)

section\<open>Basic Data Types\<close>
text\<open>
  \label{sec:Core_DOM_Basic_Datatypes}
  This theory formalizes the primitive data types used by the DOM standard~\cite{dom-specification}.
\<close> 
theory Core_DOM_Basic_Datatypes
  imports
    Main
begin

type_synonym USVString = string
text\<open>
  In the official standard, the type @{type "USVString"} corresponds to the set of all possible   
  sequences of Unicode scalar values. As we are not interested in analyzing the specifics of Unicode
  strings, we just model @{type "USVString"} using the standard type @{type "string"} of Isabelle/HOL.
\<close> 

type_synonym DOMString = string
text\<open>
  In the official standard, the type @{type "DOMString"} corresponds to the set of all possible 
  sequences of code units, commonly interpreted as UTF-16 encoded strings. Again, as we are not 
  interested in analyzing the specifics of Unicode strings, we just model @{type "DOMString"} using 
  the standard type @{type "string"} of Isabelle/HOL.
\<close>

type_synonym doctype = DOMString

paragraph\<open>Examples\<close>
definition html :: doctype
  where "html = ''<!DOCTYPE html>''"

hide_const id

text \<open>This dummy locale is used to create scoped definitions by using global interpretations
  and defines.\<close>
locale l_dummy
end
