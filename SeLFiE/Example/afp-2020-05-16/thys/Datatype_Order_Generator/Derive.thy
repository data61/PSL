(*  Title:       Deriving class instances for datatypes
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2013 René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

section \<open>Loading derive-commands\<close>
theory Derive
imports 
  Order_Generator
  Hash_Generator
  Deriving.Countable_Generator
begin

text\<open>
We just load the commands to derive (linear) orders, hash-functions, and the
command to show that a datatype is countable, so that now all of them are available.
There are further generators available in the AFP entries of lightweight containers and Show.
\<close>

print_derives

end
