(*  Title:      Basis for hotel key card system

    Author:     Tobias Nipkow, TU Muenchen
*)

theory Basis
imports Notation
begin

typedecl guest
typedecl key
typedecl room

type_synonym card = "key * key"

end
