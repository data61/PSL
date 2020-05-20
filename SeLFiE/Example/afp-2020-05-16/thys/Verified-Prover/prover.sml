(* 
   To use this file, open OCaml by typing ocaml, and at the prompt type #use "prover.ml";; 

   Formulae are represented using de Bruijn notation: 

   forall x. forall y. P x y 
   
   is
   
   forall. forall. P 1 0

   i.e. the variables are numbers indicating how many foralls in the
   syntax tree you have to jump until you reach the relevant binding
   forall.

   Variables are: x_0, x_1, ... They are represented just using their number: 0, 1, ...
   
   Predicates are: P_1, P_2, ... and their negations: \overline{P_1}, \overline{P_2}, ... 
   They are represented as follows:

   P_2(x,y)

   is

   PAtom 2 [x,y]

   and

   \overline{P_3} [y,z]

   is

   NAtom 3 [y,z]

   N.B. these definitions extracted from thy file by hand, and possibly contain transcription errors.

*)

open List;;

type pred = int;;

type var = int;;

type form = 
    PAtom of (pred*(var list))
  | NAtom of (pred*(var list))
  | FConj of form * form
  | FDisj of form * form
  | FAll of form
  | FEx of form
;;

let rec preSuc t = match t with
    [] -> []
  | (a::list) -> (match a with 0 -> preSuc list | sucn -> (sucn-1::preSuc list));;

let rec fv t = match t with
    PAtom (p,vs) -> vs
  | NAtom (p,vs) -> vs
  | FConj (f,g) -> (fv f)@(fv g)
  | FDisj (f,g) -> (fv f)@(fv g)
  | FAll f -> preSuc (fv f)
  | FEx f -> preSuc (fv f);;

let suc x = x+1;;

let bump phi y = match y with 0 -> 0 | sucn -> suc (phi (sucn-1));;

let rec subst r f = match f with
    PAtom (p,vs) -> PAtom (p,map r vs)
  | NAtom (p,vs) -> NAtom (p,map r vs)
  | FConj (f,g) -> FConj (subst r f, subst r g)
  | FDisj (f,g) -> FDisj (subst r f, subst r g)
  | FAll f -> FAll (subst (bump r) f)
  | FEx f -> FEx (subst (bump r) f);;

let finst body w = subst (fun v -> match v with 0 -> w | sucn -> (sucn-1)) body;;

let s_of_ns ns = map snd ns;;

let sfv s = flatten (map fv s);;

let rec maxvar t = match t with
    [] -> 0
  | (a::list) -> max a (maxvar list);;

let newvar vs = suc (maxvar vs);;

let subs t = match t with 
    [] -> [[]]
  | (x::xs) -> let (m,f) = x in
      match f with 
	  PAtom (p,vs) -> if mem (NAtom (p,vs)) (map snd xs) then [] else [xs@[(0,PAtom (p,vs))]]
	| NAtom (p,vs) -> if mem (PAtom (p,vs)) (map snd xs) then [] else [xs@[(0,NAtom (p,vs))]]
	| FConj (f,g)  -> [xs@[(0,f)];xs@[(0,g)]]
	| FDisj (f,g) -> [xs@[(0,f);(0,g)]]
	| FAll f -> [xs@[(0,finst f (newvar (sfv (s_of_ns (x::xs)))))]]
	| FEx f -> [xs@[(0,finst f m);(suc m,FEx f)]];;

let rec prove' l = (if l = [] then true else prove' ((fun x -> flatten (map subs x)) l));;

let prove s = prove' [s];;

let my_f = FDisj (
  (FAll (FConj ((NAtom (0,[0])), (NAtom (1,[0])))),
  (FDisj ((FEx ((PAtom (1,[0])))),(FEx (PAtom (0,[0])))))));;

prove [(0,my_f)];;
