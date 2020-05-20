(******************************************************************************
 * Citadelle
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

section\<open>Initializing the Printer\<close>

theory  Printer_init
imports "../Init"
        "../isabelle_home/src/HOL/Isabelle_Main1"
begin

text\<open>At the time of writing, the following target languages supported
     by Isabelle are also supported by the meta-compiler:
     Haskell, OCaml, Scala, SML.\<close>

subsection\<open>Kernel Code for Target Languages\<close>

  (* We put in 'CodeConst' functions using characters
     not allowed in a Isabelle 'code_const' expr
     (e.g. '_', '"', ...) *)

lazy_code_printing code_module "CodeType" \<rightharpoonup> (Haskell) \<open>
module CodeType where {
  type MlInt = Integer
; type MlMonad a = IO a
}\<close> | code_module "CodeConst" \<rightharpoonup> (Haskell) \<open>
module CodeConst where {
  import System.Directory
; import System.IO
; import qualified CodeConst.Printf

; outFile1 f file = (do
  fileExists <- doesFileExist file
  if fileExists then error ("File exists " ++ file ++ "\n") else do
    h <- openFile file WriteMode
    f (\pat -> hPutStr h . CodeConst.Printf.sprintf1 pat)
    hClose h)

; outStand1 :: ((String -> String -> IO ()) -> IO ()) -> IO ()
; outStand1 f = f (\pat -> putStr . CodeConst.Printf.sprintf1 pat)
}\<close> | code_module "CodeConst.Monad" \<rightharpoonup> (Haskell) \<open>
module CodeConst.Monad where {
  bind a = (>>=) a
; return :: a -> IO a
; return = Prelude.return
}\<close> | code_module "CodeConst.Printf" \<rightharpoonup> (Haskell) \<open>
module CodeConst.Printf where {
  import Text.Printf
; sprintf0 = id

; sprintf1 :: PrintfArg a => String -> a -> String
; sprintf1 = printf

; sprintf2 :: PrintfArg a => PrintfArg b => String -> a -> b -> String
; sprintf2 = printf

; sprintf3 :: PrintfArg a => PrintfArg b => PrintfArg c => String -> a -> b -> c -> String
; sprintf3 = printf

; sprintf4 :: PrintfArg a => PrintfArg b => PrintfArg c => PrintfArg d => String -> a -> b -> c -> d -> String
; sprintf4 = printf

; sprintf5 :: PrintfArg a => PrintfArg b => PrintfArg c => PrintfArg d => PrintfArg e => String -> a -> b -> c -> d -> e -> String
; sprintf5 = printf
}\<close> | code_module "CodeConst.String" \<rightharpoonup> (Haskell) \<open>
module CodeConst.String where {
  concat s [] = []
; concat s (x : xs) = x ++ concatMap ((++) s) xs
}\<close> | code_module "CodeConst.Sys" \<rightharpoonup> (Haskell) \<open>
module CodeConst.Sys where {
  import System.Directory
; isDirectory2 = doesDirectoryExist
}\<close> | code_module "CodeConst.To" \<rightharpoonup> (Haskell) \<open>
module CodeConst.To where {
  nat = id
}\<close> | code_module "" \<rightharpoonup> (OCaml) \<open>
module CodeType = struct
  type mlInt = int

  type 'a mlMonad = 'a option
end

module CodeConst = struct
  let outFile1 f file =
    try
      let () = if Sys.file_exists file then Printf.eprintf "File exists \"%S\"\n" file else () in
      let oc = open_out file in
      let b = f (fun s a -> try Some (Printf.fprintf oc s a) with _ -> None) in
      let () = close_out oc in
      b
    with _ -> None

  let outStand1 f =
    f (fun s a -> try Some (Printf.fprintf stdout s a) with _ -> None)

  module Monad = struct
    let bind = function
        None -> fun _ -> None
      | Some a -> fun f -> f a
    let return a = Some a
  end

  module Printf = struct
    include Printf
    let sprintf0 = sprintf
    let sprintf1 = sprintf
    let sprintf2 = sprintf
    let sprintf3 = sprintf
    let sprintf4 = sprintf
    let sprintf5 = sprintf
  end

  module String = String

  module Sys = struct open Sys
    let isDirectory2 s = try Some (is_directory s) with _ -> None
  end

  module To = struct
    let nat big_int x = Big_int.int_of_big_int (big_int x)
  end
end

\<close> | code_module "" \<rightharpoonup> (Scala) \<open>
object CodeType {
  type mlMonad [A] = Option [A]
  type mlInt = Int
}

object CodeConst {
  def outFile1 [A] (f : (String => A => Option [Unit]) => Option [Unit], file0 : String) : Option [Unit] = {
    val file = new java.io.File (file0)
    if (file .isFile) {
      None
    } else {
      val writer = new java.io.PrintWriter (file)
      f ((fmt : String) => (s : A) => Some (writer .write (fmt .format (s))))
      Some (writer .close ())
    }
  }

  def outStand1 [A] (f : (String => A => Option [Unit]) => Option [Unit]) : Option[Unit] = {
    f ((fmt : String) => (s : A) => Some (print (fmt .format (s))))
  }

  object Monad {
    def bind [A, B] (x : Option [A], f : A => Option [B]) : Option [B] = x match {
      case None => None
      case Some (a) => f (a)
    }
    def Return [A] (a : A) = Some (a)
  }
  object Printf {
    def sprintf0 (x0 : String) = x0
    def sprintf1 [A1] (fmt : String, x1 : A1) = fmt .format (x1)
    def sprintf2 [A1, A2] (fmt : String, x1 : A1, x2 : A2) = fmt .format (x1, x2)
    def sprintf3 [A1, A2, A3] (fmt : String, x1 : A1, x2 : A2, x3 : A3) = fmt .format (x1, x2, x3)
    def sprintf4 [A1, A2, A3, A4] (fmt : String, x1 : A1, x2 : A2, x3 : A3, x4 : A4) = fmt .format (x1, x2, x3, x4)
    def sprintf5 [A1, A2, A3, A4, A5] (fmt : String, x1 : A1, x2 : A2, x3 : A3, x4 : A4, x5 : A5) = fmt .format (x1, x2, x3, x4, x5)
  }
  object String {
    def concat (s : String, l : List [String]) = l filter (_ .nonEmpty) mkString s
  }
  object Sys {
    def isDirectory2 (s : String) = Some (new java.io.File (s) .isDirectory)
  }
  object To {
    def nat [A] (f : A => BigInt, x : A) = f (x) .intValue ()
  }
}

\<close> | code_module "" \<rightharpoonup> (SML) \<open>
structure CodeType = struct
  type mlInt = string
  type 'a mlMonad = 'a option
end

structure CodeConst = struct
  structure Monad = struct
    val bind = fn
        NONE => (fn _ => NONE)
      | SOME a => fn f => f a
    val return = SOME
  end

  structure Printf = struct
    local
      fun sprintf s l =
        case String.fields (fn #"%" => true | _ => false) s of
          [] => ""
        | [x] => x
        | x :: xs =>
            let fun aux acc l_pat l_s =
              case l_pat of
                [] => rev acc
              | x :: xs => aux (String.extract (x, 1, NONE) :: hd l_s :: acc) xs (tl l_s) in
            String.concat (x :: aux [] xs l)
      end
    in
      fun sprintf0 s_pat = s_pat
      fun sprintf1 s_pat s1 = sprintf s_pat [s1]
      fun sprintf2 s_pat s1 s2 = sprintf s_pat [s1, s2]
      fun sprintf3 s_pat s1 s2 s3 = sprintf s_pat [s1, s2, s3]
      fun sprintf4 s_pat s1 s2 s3 s4 = sprintf s_pat [s1, s2, s3, s4]
      fun sprintf5 s_pat s1 s2 s3 s4 s5 = sprintf s_pat [s1, s2, s3, s4, s5]
    end
  end

  structure String = struct
    val concat = String.concatWith
  end

  structure Sys = struct
    val isDirectory2 = SOME o File.is_dir o Path.explode handle ERROR _ => K NONE
  end

  structure To = struct
    fun nat f = Int.toString o f
  end

  fun outFile1 f file =
    let
      val pfile = Path.explode file
      val () = if File.exists pfile then error ("File exists \"" ^ file ^ "\"\n") else ()
      val oc = Unsynchronized.ref []
      val _ = f (fn a => fn b => SOME (oc := Printf.sprintf1 a b :: (Unsynchronized.! oc))) in
      SOME (File.write_list pfile (rev (Unsynchronized.! oc))) handle _ => NONE
    end

  fun outStand1 f = outFile1 f (Unsynchronized.! stdout_file)
end

\<close>

subsection\<open>Interface with Types\<close>

datatype ml_int = ML_int
code_printing type_constructor ml_int \<rightharpoonup> (Haskell) "CodeType.MlInt" \<comment> \<open>syntax!\<close>
            | type_constructor ml_int \<rightharpoonup> (OCaml) "CodeType.mlInt"
            | type_constructor ml_int \<rightharpoonup> (Scala) "CodeType.mlInt"
            | type_constructor ml_int \<rightharpoonup> (SML) "CodeType.mlInt"

datatype 'a ml_monad = ML_monad 'a
code_printing type_constructor ml_monad \<rightharpoonup> (Haskell) "CodeType.MlMonad _" \<comment> \<open>syntax!\<close>
            | type_constructor ml_monad \<rightharpoonup> (OCaml) "_ CodeType.mlMonad"
            | type_constructor ml_monad \<rightharpoonup> (Scala) "CodeType.mlMonad [_]"
            | type_constructor ml_monad \<rightharpoonup> (SML) "_ CodeType.mlMonad"

type_synonym ml_string = String.literal

subsection\<open>Interface with Constants\<close>

text\<open>module CodeConst\<close>

consts out_file1 :: "((ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> unit ml_monad) \<comment> \<open>fprintf\<close> \<Rightarrow> unit ml_monad) \<Rightarrow> ml_string \<Rightarrow> unit ml_monad"
code_printing constant out_file1 \<rightharpoonup> (Haskell) "CodeConst.outFile1"
            | constant out_file1 \<rightharpoonup> (OCaml) "CodeConst.outFile1"
            | constant out_file1 \<rightharpoonup> (Scala) "CodeConst.outFile1"
            | constant out_file1 \<rightharpoonup> (SML) "CodeConst.outFile1"

consts out_stand1 :: "((ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> unit ml_monad) \<comment> \<open>fprintf\<close> \<Rightarrow> unit ml_monad) \<Rightarrow> unit ml_monad"
code_printing constant out_stand1 \<rightharpoonup> (Haskell) "CodeConst.outStand1"
            | constant out_stand1 \<rightharpoonup> (OCaml) "CodeConst.outStand1"
            | constant out_stand1 \<rightharpoonup> (Scala) "CodeConst.outStand1"
            | constant out_stand1 \<rightharpoonup> (SML) "CodeConst.outStand1"

text\<open>module Monad\<close>

consts bind :: "'a ml_monad \<Rightarrow> ('a \<Rightarrow> 'b ml_monad) \<Rightarrow> 'b ml_monad"
code_printing constant bind \<rightharpoonup> (Haskell) "CodeConst.Monad.bind"
            | constant bind \<rightharpoonup> (OCaml) "CodeConst.Monad.bind"
            | constant bind \<rightharpoonup> (Scala) "CodeConst.Monad.bind"
            | constant bind \<rightharpoonup> (SML) "CodeConst.Monad.bind"

consts return :: "'a \<Rightarrow> 'a ml_monad"
code_printing constant return \<rightharpoonup> (Haskell) "CodeConst.Monad.return"
            | constant return \<rightharpoonup> (OCaml) "CodeConst.Monad.return"
            | constant return \<rightharpoonup> (Scala) "CodeConst.Monad.Return" \<comment> \<open>syntax!\<close>
            | constant return \<rightharpoonup> (SML) "CodeConst.Monad.return"

text\<open>module Printf\<close>

consts sprintf0 :: "ml_string \<Rightarrow> ml_string"
code_printing constant sprintf0 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf0"
            | constant sprintf0 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf0"
            | constant sprintf0 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf0"
            | constant sprintf0 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf0"

consts sprintf1 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> ml_string"
code_printing constant sprintf1 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf1"
            | constant sprintf1 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf1"
            | constant sprintf1 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf1"
            | constant sprintf1 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf1"

consts sprintf2 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> ml_string"
code_printing constant sprintf2 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf2"
            | constant sprintf2 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf2"
            | constant sprintf2 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf2"
            | constant sprintf2 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf2"

consts sprintf3 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> ml_string"
code_printing constant sprintf3 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf3"
            | constant sprintf3 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf3"
            | constant sprintf3 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf3"
            | constant sprintf3 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf3"

consts sprintf4 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> ml_string"
code_printing constant sprintf4 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf4"
            | constant sprintf4 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf4"
            | constant sprintf4 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf4"
            | constant sprintf4 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf4"

consts sprintf5 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> '\<alpha>5 \<Rightarrow> ml_string"
code_printing constant sprintf5 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf5"
            | constant sprintf5 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf5"
            | constant sprintf5 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf5"
            | constant sprintf5 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf5"

text\<open>module String\<close>

consts String_concat :: "ml_string \<Rightarrow> ml_string list \<Rightarrow> ml_string"
code_printing constant String_concat \<rightharpoonup> (Haskell) "CodeConst.String.concat"
            | constant String_concat \<rightharpoonup> (OCaml) "CodeConst.String.concat"
            | constant String_concat \<rightharpoonup> (Scala) "CodeConst.String.concat"
            | constant String_concat \<rightharpoonup> (SML) "CodeConst.String.concat"

text\<open>module Sys\<close>

consts Sys_is_directory2 :: "ml_string \<Rightarrow> bool ml_monad"
code_printing constant Sys_is_directory2 \<rightharpoonup> (Haskell) "CodeConst.Sys.isDirectory2"
            | constant Sys_is_directory2 \<rightharpoonup> (OCaml) "CodeConst.Sys.isDirectory2"
            | constant Sys_is_directory2 \<rightharpoonup> (Scala) "CodeConst.Sys.isDirectory2"
            | constant Sys_is_directory2 \<rightharpoonup> (SML) "CodeConst.Sys.isDirectory2"

text\<open>module To\<close>

consts ToNat :: "(nat \<Rightarrow> integer) \<Rightarrow> nat \<Rightarrow> ml_int"
code_printing constant ToNat \<rightharpoonup> (Haskell) "CodeConst.To.nat"
            | constant ToNat \<rightharpoonup> (OCaml) "CodeConst.To.nat"
            | constant ToNat \<rightharpoonup> (Scala) "CodeConst.To.nat"
            | constant ToNat \<rightharpoonup> (SML) "CodeConst.To.nat"

subsection\<open>Some Notations (I): Raw Translations\<close>

syntax "_sprint0" :: "_ \<Rightarrow> ml_string" ("sprint0 (_)\<acute>")
translations "sprint0 x\<acute>" \<rightleftharpoons> "CONST sprintf0 x"

syntax "_sprint1" :: "_ \<Rightarrow> _ \<Rightarrow> ml_string" ("sprint1 (_)\<acute>")
translations "sprint1 x\<acute>" \<rightleftharpoons> "CONST sprintf1 x"

syntax "_sprint2" :: "_ \<Rightarrow> _ \<Rightarrow> ml_string" ("sprint2 (_)\<acute>")
translations "sprint2 x\<acute>" \<rightleftharpoons> "CONST sprintf2 x"

syntax "_sprint3" :: "_ \<Rightarrow> _ \<Rightarrow> ml_string" ("sprint3 (_)\<acute>")
translations "sprint3 x\<acute>" \<rightleftharpoons> "CONST sprintf3 x"

syntax "_sprint4" :: "_ \<Rightarrow> _ \<Rightarrow> ml_string" ("sprint4 (_)\<acute>")
translations "sprint4 x\<acute>" \<rightleftharpoons> "CONST sprintf4 x"

syntax "_sprint5" :: "_ \<Rightarrow> _ \<Rightarrow> ml_string" ("sprint5 (_)\<acute>")
translations "sprint5 x\<acute>" \<rightleftharpoons> "CONST sprintf5 x"

subsection\<open>Some Notations (II): Polymorphic Cartouches\<close>

syntax "_cartouche_string'" :: String.literal
translations "_cartouche_string" \<rightleftharpoons> "_cartouche_string'"

parse_translation \<open>
  [( @{syntax_const "_cartouche_string'"}
   , parse_translation_cartouche
       @{binding cartouche_type'}
       (( "fun\<^sub>p\<^sub>r\<^sub>i\<^sub>n\<^sub>t\<^sub>f"
        , ( Cartouche_Grammar.nil1
          , Cartouche_Grammar.cons1
          , let fun f c x = Syntax.const c $ x in
            fn (0, x) => x
             | (1, x) => f @{const_syntax sprintf1} x
             | (2, x) => f @{const_syntax sprintf2} x
             | (3, x) => f @{const_syntax sprintf3} x
             | (4, x) => f @{const_syntax sprintf4} x
             | (5, x) => f @{const_syntax sprintf5} x
            end))
        :: Cartouche_Grammar.default)
       (fn 37 \<comment> \<open>\<^verbatim>\<open>#"%"\<close>\<close> => (fn x => x + 1)
         | _ => I)
       0)]
\<close>

subsection\<open>Generic Locale for Printing\<close>

locale Print =
  fixes To_string :: "string \<Rightarrow> ml_string"
  fixes To_nat :: "nat \<Rightarrow> ml_int"
begin
  declare[[cartouche_type' = "fun\<^sub>p\<^sub>r\<^sub>i\<^sub>n\<^sub>t\<^sub>f"]]
end

text\<open>As remark, printing functions (like @{term sprintf5}...) are currently 
weakly typed in Isabelle, we will continue the typing using the type system of target languages.\<close>

end
