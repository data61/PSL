(*  Title:       DPT (Decision Procedure Toolkit) SAT solver ported to SML
    Author:      Armin Heller, TU Muenchen
    Maintainer:  Jasmin Blanchette <blanchette at in.tum.de>
*)

(* Ported to Standard ML by Armin Heller. The original OCaml files are
available from http://sourceforge.net/projects/dpt/.

Original copyright notice from the OCaml sources: 

 Copyright 2007 Intel Corporation 

 Licensed under the Apache License, Version 2.0 (the "License"); you
 may not use this file except in compliance with the License.  You
 may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
 implied.  See the License for the specific language governing
 permissions and limitations under the License. *)

signature DPT_SAT_SOLVER =
sig
  type solver
  val empty_solver : unit -> solver
  val init : solver -> int list list -> unit
  val solve : solver -> unit
  val satisfied : solver -> bool
  val assignment : solver -> int -> bool option
end

structure DPT_SAT_Solver : DPT_SAT_SOLVER = 
struct

structure Vec = 
struct

fun limit_for x = Array.maxLen

fun capacity_for n x =
  (if (n > Array.maxLen) then 
       error "capacity_for: Invalid_argument \"exceeds limit\""
   else () ;
   Int.max (1, n))

fun capacity_atleast m n x = 
let val result = Int.min (limit_for x, (Int.max (2 * n, m)))
in if (m > result) then
       error "capacity_atleast: Invalid_argument \"exceeds limit\""
   else () ;
   result end

fun array_make size x cap triv = 
  let val a = Array.array (cap, triv)
      val n = Unsynchronized.ref 0
  in while !n < size do
     (
         Array.update (a, !n, x) ;
         n := !n + 1
     ) ;
     a end

fun array_init size f cap triv = 
  let val a = Array.array (cap, triv)
      val n = Unsynchronized.ref 0
  in while !n < size do
     (
         Array.update (a, !n, f (!n)) ;
         n := !n + 1
     ) ;
     a end

fun array_extend a size cap triv = 
  let val a' = Array.array (cap, triv)
  in ArraySlice.copy {src = ArraySlice.slice (a, 0, SOME size), 
                      dst = a', 
                      di = 0} ; a' end

fun array_top a size = Array.sub (a, size - 1)

fun array_pop a size triv = 
  let val last = size - 1
      val result = Array.sub (a, last)
  in Array.update (a, last, triv) ;
     result end

fun array_push a size x = Array.update (a, size, x)

fun array_delete a size i triv = 
  let val last = size - 1
  in ArraySlice.copy {src = ArraySlice.slice (a, i + 1, SOME (last - i)), 
                      dst = a, 
                      di = i} ;
     last end

fun array_swap_out a size i triv = 
  let val last = size - 1
  in Array.update (a, i, Array.sub (a, last)) ;
     Array.update (a, last, triv) ;
     last end

fun array_insert a size i x = 
  (ArraySlice.copy {src = ArraySlice.slice (a, i, SOME (size - i)), 
                    dst = a, 
                    di = i + 1} ;
   Array.update (a, i, x))

fun array_fast_filter p a i size triv = 
  if i = size then 
      size
  else if p (Array.sub (a, i)) then
      array_fast_filter p a (i + 1) size triv
  else
  (
      Array.update (a, i, Array.sub (a, size - 1)) ;
      Array.update (a, size - 1, triv) ;
      array_fast_filter p a i (size - 1) triv
  )


fun array_fast_filter_const p x a i size triv =
if i = size then 
  size
else if p x (Array.sub (a, i)) then
  array_fast_filter_const p x a (i + 1) size triv
else
(
  Array.update (a, i, Array.sub (a, size - 1)) ;
  Array.update (a, size - 1, triv) ;
  array_fast_filter_const p x a i (size - 1) triv
)


fun array_first_not p a i size =
if i = size then size 
else if not (p (Array.sub (a, i))) then i
else array_first_not p a (i + 1) size


fun array_first_not2 p x a i size =
if i = size then size 
else if not (p x (Array.sub (a, i))) then i 
else array_first_not2 p x a (i + 1) size


fun array_first_noti p a i size =
if i = size then size
else if not (p i (Array.sub (a, i))) then i
else array_first_noti p a (i + 1) size


fun array_first_noti2 p x a i size =
if i = size then size
else if not (p x i (Array.sub (a, i))) then i
else array_first_noti2 p x a (i + 1) size


fun array_filter p a i size triv =
let val j = Unsynchronized.ref (array_first_not p a i size) 
    val k = Unsynchronized.ref (!j + 1)
in
    while !k < size do
    (
        let val x = Array.sub (a, !k)
        in if p x then
           (
                     Array.update (a, !j, x) ;
                     j := !j + 1
                 ) else () ; 
           k := !k + 1 end
    ) ;
    k := !j ;
    while !k < size do
    (
        Array.update (a, !k, triv) ;
        k := !k + 1
    ) ;
    !j
end


fun array_filter_const p x a i size triv =
let val j = Unsynchronized.ref (array_first_not2 p x a i size)
    val k = Unsynchronized.ref (!j + 1)
in
    while !k < size do
    (
        let val y = Array.sub (a, !k)
        in if p x y then
           (
                     Array.update (a, !j, y) ;
                     j := !j + 1
                 ) else () end
    ) ;
    k := !j ;
    while !k < size do
    (
        Array.update (a, !k, triv) ;
        k := !k + 1
    ) ;
    !j
end

fun array_filteri p a i size triv =
let val j = Unsynchronized.ref (array_first_noti p a i size)
    val k = Unsynchronized.ref (!j + 1)
in
    while !k < size do
    (
        let val x = Array.sub (a, !k) in
                  if p (!k) x then
            (
                      Array.update (a, !j, x) ;
                      j := !j + 1
                  ) else () ;
            k := !k + 1 end
    ) ;
    k := !j ;
    while !k < size do
    (
        Array.update (a, !k, triv) ;
        k := !k + 1
    ) ;
    !j
end


fun array_filteri_const p x a i size triv =
let val j = Unsynchronized.ref (array_first_noti2 p x a i size)
    val k = Unsynchronized.ref (!j + 1)
in
    while !k < size do
    (
        let val y = Array.sub (a, !k) 
        in if p x (!k) y then
           (
                     Array.update (a, !j, y) ;
                     j := !j + 1
           ) else () end
    ) ;
    k := !j ;
    while !k < size do
    (
        Array.update (a, !k, triv) ;
        k := !k + 1
    ) ;
    !j
end

fun subarray_first p a i j =
if i = j then j 
else if p (Array.sub (a, i)) then i
else subarray_first p a (i + 1) j

fun subarray_first_const p x a i j =
if i = j then j 
else if p x (Array.sub (a, i)) then i 
else subarray_first_const p x a (i + 1) j

fun array_first p a i j = 
let val result = subarray_first p a i j
in if result = j then error "array_first: Not_found"
   else result end

fun array_first_const p x a i j =
let val result = subarray_first_const p x a i j
in if result = j then raise error "array_first: Not_found"
   else result end

type 'a t = 
   {contents : 'a array Unsynchronized.ref, 
    size : int Unsynchronized.ref, 
    dummy: 'a}

fun make n x triv = 
  {contents = Unsynchronized.ref (array_make n x (capacity_for n triv) triv), 
   size = Unsynchronized.ref n,
   dummy = triv} : 'a t

val create = make

fun init n f triv = 
  {contents = Unsynchronized.ref (array_init n f (capacity_for n triv) triv), 
   size = Unsynchronized.ref n, 
   dummy = triv} : 'a t

fun copy (v : 'a t) = 
{contents = Unsynchronized.ref (Array.tabulate
                     (Array.length (!(#contents v)), 
                      (fn i => Array.sub (!(#contents v), i)))), 
 size = Unsynchronized.ref (!(#size v)), 
 dummy = (#dummy v)} : 'a t

fun capacity_above n x =
let val result = Int.min (limit_for x, 2 * n) in
  if (n >= result) then
      error "capacity_above: Invalid_argument \"exceeds limit\""
  else () ;
  result end


fun ensure_cap (v : 'a t) =
let val cap = Array.length (!(#contents v)) 
in if !(#size v) = cap then
       (#contents v) := array_extend 
                            (!(#contents v)) cap 
                            (capacity_above cap (#dummy v)) 
                            (#dummy v)
   else () end

fun of_array a triv =
let val n = Array.length a
in {contents = Unsynchronized.ref (array_extend a n (capacity_for n triv) triv), 
          size = Unsynchronized.ref n, 
          dummy = triv} : 'a t end


fun of_list l triv =
let val n = length l
    val a = Array.array (capacity_for n triv, triv)
    fun init i [] = ()
      | init i (h :: t) = (Array.update (a, i, h) ; 
                           init (i + 1) t)
in init 0 l ;
   {contents = Unsynchronized.ref a, 
          size = Unsynchronized.ref n, 
          dummy = triv} : 'a t end

fun to_array (v : 'a t) = 
let val a = Array.array (!(#size v), #dummy v)
in ArraySlice.copy {src = ArraySlice.slice 
                              (!(#contents v), 0, SOME (!(#size v))), 
                    dst = a, di = 0} ; a end

fun to_list (v : 'a t) = 
  ArraySlice.foldr (op ::) [] 
                   (ArraySlice.slice 
                        (!(#contents v), 0, SOME (!(#size v))))

fun length (v : 'a t) = !(#size v)

fun is_empty (v : 'a t) = !(#size v) = 0

fun grow (v : 'a t) n x = 
let val cap = Array.length (!(#contents v))
in if n > cap then 
   (
       (#contents v) :=
       array_extend (!(#contents v)) (!(#size v)) 
                          (capacity_atleast n cap (#dummy v)) (#dummy v)
   )
   else () ;
   ArraySlice.modify (fn _ => x)
                     (ArraySlice.slice (!(#contents v), 
                                        !(#size v), 
                                        SOME (n - !(#size v)))) ;
   (#size v) := n end

fun grow_init (v : 'a t) n f =
let val cap = Array.length (!(#contents v))
in if n > cap then 
   (
       (#contents v) :=
       array_extend (!(#contents v)) (!(#size v)) 
                          (capacity_atleast n cap (#dummy v)) (#dummy v)
   )
   else () ;
   ArraySlice.modify f 
                     (ArraySlice.slice (!(#contents v), 
                                        !(#size v), 
                                        SOME (n - !(#size v)))) ;
   (#size v) := n end

fun shrink (v : 'a t) n =
  (ArraySlice.modify (fn _ => #dummy v)
                     (ArraySlice.slice (!(#contents v), n, 
                                        SOME (!(#size v) - n))) ;
   (#size v) := n)

fun clear (v : 'a t) = shrink v 0

fun get (v : 'a t) i = Array.sub (!(#contents v), i)

fun set (v : 'a t) i x = Array.update (!(#contents v), i, x)

fun set_all (v : 'a t) i j x = 
  ArraySlice.modify (fn _ => x)
                    (ArraySlice.slice (!(#contents v), 
                                       i, SOME (j - i)))

fun top (v : 'a t) = array_top (!(#contents v)) (!(#size v))

fun pop (v : 'a t) =
let val result = array_pop (!(#contents v)) (!(#size v)) (#dummy v)
in (#size v) := !(#size v) - 1 ;
   result end

fun push (v : 'a t) x = 
  (ensure_cap v ;
   array_push (!(#contents v)) (!(#size v)) x ;
   (#size v) := !(#size v) + 1)

fun insert (v : 'a t) i x =
  (ensure_cap v ;
   array_insert (!(#contents v)) (!(#size v)) i x ;
   (#size v) := !(#size v) + 1)

fun delete (v : 'a t) i = 
  (#size v) := array_delete (!(#contents v)) (!(#size v)) i (#dummy v)

fun array_swap a i j = 
  if i <> j then
      let val tmp = Array.sub (a, i)
      in Array.update (a, i, Array.sub (a, j)) ;
         Array.update (a, j, tmp) end
  else ()

fun swap (v : 'a t) i j =
  array_swap (!(#contents v)) i j

fun swap_out (v : 'a t) i =
  (#size v) := array_swap_out (!(#contents v)) (!(#size v)) i (#dummy v)

fun array_rev a i j = 
  if i < j then
      (array_swap a i (j - 1) ;
       array_rev a (i + 1) (j - 1))
  else ()

fun rev (v : 'a t) = array_rev (!(#contents v)) 0 (!(#size v))

fun array_iter c a i j = 
  if i <> j then
      (c (Array.sub (a, i)) ;
       array_iter c a (i + 1) j)
  else ()

fun iter c (v : 'a t) = array_iter c (!(#contents v)) 0 (!(#size v))

fun array_iter_const c x a i j = 
  if i <> j then
      (c x (Array.sub (a, i)) ;
       array_iter_const c x a (i + 1) j)
  else ()

fun iter_const c x (v : 'a t) = array_iter_const c x (!(#contents v)) 0 (!(#size v))

fun array_iteri c a i j =
if i <> j then
    (c i (Array.sub (a, i)) ;
     array_iteri c a (i + 1) j)
else ()

fun iteri c (v : 'a t) = array_iteri c (!(#contents v)) 0 (!(#size v))

fun array_iter_const c x a i j =
if i <> j then
    (c x (Array.sub (a, i)) ;
     array_iter_const c x a (i + 1) j)
else ()

fun iteri_const c x (v : 'a t) = array_iter_const c x (!(#contents v)) 0 (!(#size v))

fun modify f (v : 'a t) = ArraySlice.modify f (ArraySlice.slice (!(#contents v), 
                                                      0, SOME (!(#size v))))

fun modify_const f x (v : 'a t) = modify (f x) v

fun fold_left f acc (v : 'a t) = ArraySlice.foldl (uncurry f) acc 
                                       (ArraySlice.slice
                                            (!(#contents v), 0, SOME (!(#size v))))

fun fold_right f acc (v : 'a t) = ArraySlice.foldr (uncurry f) acc 
                                        (ArraySlice.slice
                                             (!(#contents v), 0, SOME (!(#size v))))

fun uncurry3 f (x, y, z) = f x y z

fun foldi_left f acc (v : 'a t) = ArraySlice.foldli (uncurry3 f) acc 
                                         (ArraySlice.slice
                                              (!(#contents v), 0, SOME (!(#size v))))

fun foldi_right f acc (v : 'a t) = ArraySlice.foldri (uncurry3 f) acc 
                        (ArraySlice.slice
                             (!(#contents v), 0, SOME (!(#size v))))

fun first p (v : 'a t) = array_first p (!(#contents v)) 0 (!(#size v))

fun first_const p x (v : 'a t) = array_first_const p x (!(#contents v)) 0 (!(#size v))

fun find p (v : 'a t) = Array.sub (!(#contents v), array_first p (!(#contents v)) 0 (!(#size v)))

fun find_const p x (v : 'a t) = (!(#contents v), array_first_const p x (!(#contents v)) 0 (!(#size v))) 

fun memb eq x (v : 'a t) = 
  ArraySlice.exists (eq x)
                    (ArraySlice.slice ((!(#contents v)), 
                                       0, SOME (!(#size v))))


fun exists p (v : 'a t) = ArraySlice.exists p 
                                 (ArraySlice.slice ((!(#contents v)), 
                                                    0, SOME (!(#size v))))

fun exists_const p x (v : 'a t) = exists (p x) v

fun for_all p (v : 'a t) = ArraySlice.all p 
                                        (ArraySlice.slice ((!(#contents v)), 
                                                           0, SOME (!(#size v))))

fun for_all_const p x (v : 'a t) = for_all (p x) v


fun fast_filter p (v : 'a t) = 
  (#size v) := array_filter p (!(#contents v)) 0 (!(#size v)) (#dummy v)

fun fast_filter_const p x (v : 'a t) = 
  (#size v) := array_filter_const p x (!(#contents v)) 0 (!(#size v)) (#dummy v)

fun filter p (v : 'a t) = 
  (#size v) := array_filter p (!(#contents v)) 0 (!(#size v)) (#dummy v)

fun filter_const p x (v : 'a t) = 
  (#size v) := array_filter_const p x (!(#contents v)) 0 (!(#size v)) (#dummy v)


fun filteri p (v : 'a t) = 
  (#size v) := array_filteri p (!(#contents v)) 0 (!(#size v)) (#dummy v)

fun filteri_const p x (v : 'a t) = 
  (#size v) := array_filteri_const p x (!(#contents v)) 0 (!(#size v)) (#dummy v)

fun merge cmp b n m i a j k =
if n <> m then
  if j = k orelse (fn res => res = LESS orelse res = EQUAL) 
                      (cmp (Array.sub (b, n)) (Array.sub (a, j)))then
      (Array.update (a, i, Array.sub (b, n)) ;
       merge cmp b (n + 1) m (i + 1) a j k)
  else
      (Array.update (a, i, Array.sub (a, j)) ;
       merge cmp b n m (i + 1) a (j + 1) k)
else ()

fun msort cmp a i j tmp =
if i + 1 < j then 
  let val mid = i + (j - i) div 2
  in msort cmp a i mid tmp ;
     msort cmp a mid j tmp ;
     ArraySlice.copy {src = ArraySlice.slice (a, i, SOME (mid - i)), 
                      dst = tmp, 
                      di = 0} ;
     merge cmp tmp 0 (mid - i) i a mid j end
else ()

fun merge_sort cmp a i j =
  let val tmp = Array.array ((j - i) div 2, Array.sub (a, i))
  in msort cmp a i j tmp end

val array_sort = merge_sort

val array_stable_sort = merge_sort

fun sort cmp (v : 'a t) = array_sort cmp (!(#contents v)) 0 (!(#size v))

fun stable_sort cmp (v : 'a t) = array_stable_sort cmp (!(#contents v)) 0 (!(#size v))

end

type 'a vec = 'a Vec.t

structure PriorityQueue = 
struct


val invalid_position = ~1

fun int_add m n x = 
  if n < Vec.length m then
      Vec.set m n x
  else
      Vec.grow m (n + 1) x

fun real_add m n x = 
  if n < Vec.length m then
      Vec.set m n x
  else Vec.grow m (n + 1) x

type t = {priority: real vec, 
        position: int vec, 
        heap: int vec}
fun queue_length (x : t) = Vec.length (#heap x)

val root_position = 0

fun parent_position i = (i - 1) div 2

fun left_child_position i = 2 * i + 1

fun right_sibling_position i = i + 1

fun ensure_map_memb q e = 
  if not (e < Vec.length (#priority q)) then
  (
      real_add (#priority q) e 0.0 ;
      int_add (#position q) e invalid_position
  ) else ()

fun higher_priority q x y = 
  let val x_score : real = Vec.get (#priority q) x
      val y_score : real = Vec.get (#priority q) y
  in x_score > y_score orelse ((x_score - y_score) * (x_score - y_score) <= 0.0 andalso x > y) end

fun create e = 
  {priority = Vec.make 0 0.0 0.0, 
   position = Vec.make 0 invalid_position invalid_position, 
   heap = Vec.make 0 e e} : t

fun is_empty (q : t) = Vec.is_empty (#heap q)

fun memb (h : t) x = 
  0 <= x andalso x < Vec.length (#position h)
  andalso Vec.get (#position h) x <> invalid_position

fun percolate_up (h : t) j =
  if j > 0 then
      let val je = Vec.get (#heap h) j
          val i = parent_position j
          val ie = Vec.get (#heap h) i
      in if higher_priority h je ie then
         (
             Vec.set (#heap h) j ie ;
             Vec.set (#heap h) i je ;
             Vec.set (#position h) je i ;
             Vec.set (#position h) ie j ;
             percolate_up h i
         )
         else ()
      end
  else ()

fun percolate_down (h : t) i = 
  let val size = Vec.length (#heap h)
      val l = left_child_position i
  in if l < size then
         let val r = right_sibling_position l
             val j = 
                 if r < size andalso
                    (higher_priority h) 
                        (Vec.get (#heap h) r) 
                        (Vec.get (#heap h) l)
                 then r
                 else l
             val ie = Vec.get (#heap h) i
             val je = Vec.get (#heap h) j
         in if (higher_priority h) je ie then
            (
                Vec.set (#heap h) i je ;
                Vec.set (#heap h) j ie ;
                Vec.set (#position h) je i ;
                Vec.set (#position h) ie j ;
                percolate_down h j
            )
            else ()
         end
     else ()
  end

fun enqueue (h : t) e = 
  (ensure_map_memb h e ;
   if Vec.get (#position h) e = invalid_position
   then let val i = Vec.length (#heap h)
        in Vec.push (#heap h) e ;
           Vec.set (#position h) e i ;
           percolate_up h i end
   else ())

fun head q = 
  if is_empty q then raise error "queue empty!"
  else Vec.get (#heap q) root_position

fun drop q = 
  if is_empty q then raise error "queue empty!"
  else
  (
      Vec.set (#position q) (head q) invalid_position ;
      Vec.swap_out (#heap q) root_position ;
      if not (is_empty q) then
          let val e = head q 
          in Vec.set (#position q) e root_position ;
             percolate_down q root_position end
      else ()
  )

fun dequeue q = 
  let val result = head q
  in drop q ; result end

fun priority (q : t) e = 
  if e < Vec.length (#priority q) then
      Vec.get (#priority q) e
  else 0.0

fun inc_priority q e (x : real) = 
(
  ensure_map_memb q e ;
  let val old = Vec.get (#priority q) e
  in Vec.set (#priority q) e (old + x) ;
     if memb q e then
         percolate_up q (Vec.get (#position q) e)
     else () end
)

fun scale (q : t) x = Vec.modify (fn y => x * y) (#priority q)


end


type priority_queue = PriorityQueue.t

val check_assertions : bool Unsynchronized.ref = Unsynchronized.ref true

fun assert condition err_str = 
  if !check_assertions then
      if not (condition ()) then error err_str else ()
  else ()

type clause = {literals : int array, activity : real Unsynchronized.ref}
datatype reason = Unassigned
              | Decision
              | Propagation of clause


fun new_clause lit_list = 
  {literals = Array.fromList lit_list, activity = Unsynchronized.ref 0.0}

fun array_to_list a = Array.foldr (op ::) [] a

val (max_float : real) = Real.maxFinite

val (min_float : real) = Real.minNormalPos

val (empty_queue : unit -> priority_queue) = (fn _ => PriorityQueue.create (~1))

val (queue_length : priority_queue -> int) = PriorityQueue.queue_length

val (empty_clause : clause) = new_clause []

val (invalid_level : int) = ~1

type solver = 
{
   clause : clause vec, 
   learned : clause vec, 
   trace : int vec, 
   assignment_array : bool option array Unsynchronized.ref, 
   reason_array : reason array Unsynchronized.ref, 
   level_array : int array Unsynchronized.ref, 
   conflict_detected : bool Unsynchronized.ref, 
   decision_level : int Unsynchronized.ref, 
   position : int array Unsynchronized.ref, 
   early_level_array : int array Unsynchronized.ref, 
   cls_increment : real Unsynchronized.ref, 
   early_reason_array : clause array Unsynchronized.ref, 
   scale : real Unsynchronized.ref, 
   conflict_level : int Unsynchronized.ref, 
   decision_queue : priority_queue Unsynchronized.ref, 
   lower_conflict_lits : int list Unsynchronized.ref, 
   next_inference_lit : int Unsynchronized.ref, 
   num_implication_points : int Unsynchronized.ref, 
   var_increment : real Unsynchronized.ref, 
   num_vars : int Unsynchronized.ref, 
   max_var : int Unsynchronized.ref, 
   shy_of_max : real Unsynchronized.ref, 
   conflict_vars : int list Unsynchronized.ref, 
   pending_literals : int Queue.T Unsynchronized.ref, 
   num_conflicts : int Unsynchronized.ref, 
   dispatch_lit : int Unsynchronized.ref, 
   next_inference_cls : int Unsynchronized.ref, 
   pending_clauses : int list Queue.T Unsynchronized.ref, 
   bias : (bool array) Unsynchronized.ref, 
   num_decisions : int Unsynchronized.ref, 
   watchers : clause list Unsynchronized.ref array Unsynchronized.ref, 
   num_inferences : int Unsynchronized.ref, 
   conflict_limit : int Unsynchronized.ref,
   learneds_limit : int Unsynchronized.ref
}

fun empty_solver () : solver = 
  {
      clause = Vec.make 0 empty_clause empty_clause, 
      learned = Vec.make 0 empty_clause empty_clause, 
      trace = Vec.of_list [] 0, 
      assignment_array = Unsynchronized.ref (Array.fromList []), 
      reason_array = Unsynchronized.ref (Array.fromList []), 
      level_array = Unsynchronized.ref (Array.fromList []), 
      conflict_detected = Unsynchronized.ref false, 
      decision_level = Unsynchronized.ref 0, 
      position = Unsynchronized.ref (Array.fromList []), 
      early_level_array = Unsynchronized.ref (Array.fromList []), 
      cls_increment = Unsynchronized.ref 1.0, 
      early_reason_array = Unsynchronized.ref (Array.fromList []), 
      scale = Unsynchronized.ref 1.05, 
      conflict_level = Unsynchronized.ref 0, 
      decision_queue = Unsynchronized.ref (empty_queue ()), 
      lower_conflict_lits = Unsynchronized.ref [], 
      next_inference_lit = Unsynchronized.ref 0, 
      num_implication_points = Unsynchronized.ref 0, 
      var_increment = Unsynchronized.ref 0.0, 
      num_vars = Unsynchronized.ref 0, 
      max_var = Unsynchronized.ref 0, 
      shy_of_max = Unsynchronized.ref (max_float / 1.05), 
      conflict_vars = Unsynchronized.ref [], 
      pending_literals = Unsynchronized.ref (Queue.empty), 
      num_conflicts = Unsynchronized.ref 0, 
      dispatch_lit = Unsynchronized.ref 0, 
      next_inference_cls = Unsynchronized.ref 0, 
      pending_clauses = Unsynchronized.ref (Queue.empty), 
      bias = Unsynchronized.ref (Array.fromList []), 
      num_decisions = Unsynchronized.ref 0, 
      watchers = Unsynchronized.ref (Array.fromList []), 
      num_inferences = Unsynchronized.ref 0, 
      conflict_limit = Unsynchronized.ref 100, 
      learneds_limit = Unsynchronized.ref 0
  }

fun assignment (s : solver) lit = 
  let val var = abs lit
      val var_val = Array.sub (!(#assignment_array s), var) in
      if lit > 0 then var_val else Option.map not var_val
  end

fun is_true (s : solver) lit = assignment s lit = SOME true

fun is_false (s : solver) lit = 
  let val result = assignment s lit = SOME false in 
      assert (fn _ => result = is_true s (~lit)) "" ;
      result end

fun reason (s : solver) lit = Array.sub (!(#reason_array s), abs lit)

fun is_assigned (s : solver) lit = 
  let val result = reason s lit <> Unassigned in
      assert (fn _ => result = is_true s lit orelse is_false s lit) 
             "is_assigned violates: result = is_true lit orelse is_false lit" ;
      result
  end

fun array_forall f a = 
  let val i = Unsynchronized.ref 0
      val result = Unsynchronized.ref true in 
      while !i < Array.length a andalso !result do
          (if f (Array.sub (a, !i)) then ()
           else result := false ;
           i := !i + 1) ;
      !result end

fun array_mem x a = 
  let val i = Unsynchronized.ref 0
      val result = Unsynchronized.ref false in 
      while !i < Array.length a andalso not (!result) do
          (if x = Array.sub (a, !i) then result := true else () ;
           i := !i + 1) ;
      !result end

fun explanation_valid (s : solver) lit lits = 
  let fun others_false l = is_false s l orelse l = lit in
      array_mem lit lits andalso array_forall others_false lits
  end

fun reason_valid (s : solver) lit r = 
  case r
   of Unassigned => false
    | Decision => true
    | Propagation cls => explanation_valid s lit (#literals cls)

fun assign_lit (s : solver) lit reason' =
(
  assert (fn _ => not (!(#conflict_detected s))) 
         "assign_lit violates: not (!(#conflict_detected s))" ;
  assert (fn _ => not (is_assigned s lit)) "assign_lit violates: not (is_assigned lit)" ;
  assert (fn _ => reason_valid s lit reason') ("assign_lit violates: reason_valid lit reason'") ;
  let val var = abs lit
      val var_val = SOME (lit > 0) in
      if reason' = Decision then (#decision_level s) := !(#decision_level s) + 1 else () ;
      Array.update (!(#reason_array s), var, reason') ;
      Array.update (!(#assignment_array s), var, var_val) ;
      Array.update (!(#level_array s), var, !(#decision_level s)) ;
      Array.update (!(#position s), var, Vec.length (#trace s)) ;
      Vec.push (#trace s) lit
  end
)

fun early_level (s : solver) lit = Array.sub (!(#early_level_array s), abs lit)

fun early_reason (s : solver) lit = Array.sub (!(#early_reason_array s), abs lit)

fun rescale_clause_activities (s : solver) = 
  let fun rescale c = #activity c := !(#activity c) * min_float in 
      Vec.iter rescale (#learned s) ;
      (#cls_increment s) := !(#cls_increment s) * min_float
  end

fun inc_clause_activity (s : solver) cls = 
(
  if !(#activity cls) > max_float - !(#cls_increment s) then
      rescale_clause_activities s
  else () ;
  #activity cls := !(#activity cls) + !(#cls_increment s)
)

fun level (s : solver) lit = (Array.sub (!(#level_array s), abs lit))

fun unit_propagation_possible (s : solver) = 
  !(#next_inference_lit s) < Vec.length (#trace s) 

fun invariant (s : solver) = 
  (assert (fn _ => !(#num_vars s) > 1) "invariant violates: !(#num_vars s) > 1" ;
   assert (fn _ => !(#decision_level s) >= 0) "invariant violates: !(#decision_level s) >= 0" ;
   assert (fn _ => Vec.length (#trace s) >= !(#decision_level s)) "invariant violates: Vec.length (#trace s) >= !(#decision_level s)" ;
   assert (fn _ => Vec.length (#trace s) + queue_length (!(#decision_queue s)) >= !(#num_vars s))
          "invariant violates: Vec.length (#trace s) + queue_length (!(#decision_queue s)) >= !(#num_vars s)" ;
   assert (fn _ => Vec.length (#trace s) = 0 orelse is_true s (Vec.top (#trace s)))
          "invariant violates: Vec.length (#trace s) = 0 orelse is_true (Vec.top (#trace s))" ;
   assert (fn _ => !(#conflict_detected s) orelse Vec.length (#trace s) >= !(#next_inference_lit s))
          "invariant violates: !(#conflict_detected s) orelse Vec.length (#trace s) >= !(#next_inference_lit s)" ;
   assert (fn _ => !(#next_inference_lit s) + 1 >= !(#decision_level s))
          "invariant violates: !(#next_inference_lit s) + 1 >= !(#decision_level s)" ;
   assert (fn _ => !(#conflict_detected s) orelse not (unit_propagation_possible s) orelse
            level s (Vec.get (#trace s) (!(#next_inference_lit s))) = !(#decision_level s))
          ("invariant violates: !(#conflict_detected s) orelse not (unit_propagation_possible ()) orelse\n" ^
           "level (Vec.get (#trace s) (!(#next_inference_lit s))) = !(#decision_level s)") ;
   assert (fn _ => !(#num_implication_points s) >= 0) "invariant violates: !(#num_implication_points s) >= 0" ;
   assert (fn _ => !(#conflict_detected s) orelse !(#num_implication_points s) = 0)
          "invariant violates: !(#conflict_detected s) orelse !(#num_implication_points s) = 0" ;
   assert (fn _ => !(#conflict_detected s) orelse !(#lower_conflict_lits s) = [])
          "invariant violates: !(#conflict_detected s) orelse !(#lower_conflict_lits s) = []" ;
   assert (fn _ => not (!(#conflict_detected s)) orelse !(#conflict_level s) <= !(#decision_level s))
          "invariant violates: not (!(#conflict_detected s)) orelse !(#conflict_level s) <= !(#decision_level s)" ;
   assert (fn _ => not (!(#conflict_detected s)) orelse !(#conflict_level s) = 0 orelse 
            !(#num_implication_points s) > 0)
          ("invariant violates: not (!(#conflict_detected s)) orelse !(#conflict_level s) = 0 orelse \n" ^
           "!(#num_implication_points s) > 0") ;
   assert (fn _ => not (!(#conflict_detected s)) orelse !(#conflict_level s) = 0 orelse
            !(#decision_level s) = !(#conflict_level s)) 
          ("invariant violates: not (!(#conflict_detected s)) orelse !(#conflict_level s) = 0 orelse\n" ^
           "!(#decision_level s) = !(#conflict_level s)") ;
   assert (fn _ => not (!(#conflict_detected s)) orelse !(#conflict_level s) = 0 orelse
            !(#num_implication_points s) = 1)
          ("invariant violates: not (!(#conflict_detected s)) orelse !(#conflict_level s) = 0 orelse" ^
           "!(#num_implication_points s) = 1") ;
   assert (fn _ => 0.0 < !(#cls_increment s) andalso !(#cls_increment s) <= !(#shy_of_max s))
          ("invariant violates: 0.0 < !(#cls_increment s) andalso !(#cls_increment s) <= !(#shy_of_max s)") ;
   assert (fn _ => 0.0 < !(#var_increment s) andalso !(#var_increment s) <= !(#shy_of_max s))
          "invariant violates: 0.0 < !(#var_increment s) andalso !(#var_increment s) <= !(#shy_of_max s)" ;
   true
  )

fun remove_early_implication (s : solver) lit = 
(
  assert (fn _ => not (!(#conflict_detected s))) 
         "remove_early_implication violates: not (!(#conflict_detected s))" ;
  assert (fn _ => early_level s lit > !(#decision_level s)) 
         "remove_early_implication violates: early_level lit > !(#decision_level s)" ;
  let val var = abs lit in
      Array.update (!(#early_reason_array s), var, empty_clause) ;
      Array.update (!(#early_level_array s), var, invalid_level) ;
      assert (fn _ => not (!(#conflict_detected s))) 
             "remove_early_implication violates: not (!(#conflict_detected s))"
  end
)

fun rescale_decision_priorities (s : solver) = 
  (
      PriorityQueue.scale (!(#decision_queue s)) min_float ;
      (#var_increment s) := !(#var_increment s) * min_float
  )

fun inc_decision_priority (s : solver) lit = 
  let val var = abs lit 
      val priority = PriorityQueue.priority ((!(#decision_queue s))) var in
      if priority > max_float - !(#var_increment s) then
          rescale_decision_priorities s
      else () ;
      PriorityQueue.inc_priority (!(#decision_queue s)) var (!(#var_increment s))
  end

fun is_conflict_lit (s : solver) lit = member (op =) (!(#conflict_vars s)) (abs lit)

fun add_conflict_lit (s : solver) lit = 
(
  assert (fn _ => !(#conflict_detected s)) "add_conflict_lit violates: !(#conflict_detected s)" ;
  let val lit_level = level s lit in
      assert (fn _ => lit_level <= !(#conflict_level s)) 
             "add_conflict_lit violates: lit_level <= !(#conflict_level s)" ;
      if not (is_conflict_lit s lit) then
      (
          assert (fn _ => is_false s lit) "add_conflict_lit violates: is_false lit" ;
          (#conflict_vars s) := insert (op =) (abs lit) (!(#conflict_vars s)) ;
          inc_decision_priority s lit ;
          if lit_level = !(#conflict_level s) then
              ((#num_implication_points s) := !(#num_implication_points s) + 1)
          else (#lower_conflict_lits s) := lit :: !(#lower_conflict_lits s)
      )
      else () end
)

fun unsatisfiable (s : solver) = !(#conflict_detected s) andalso !(#conflict_level s) = 0

fun unassign_last_lit (s : solver) = 
  (assert (fn _ => not (Vec.is_empty (#trace s))) "unassign_last_lit violates: not (null (#trace s))" ;
   let val lit = Vec.pop (#trace s)
       val var = abs lit
       val reason = Array.sub (!(#reason_array s), var)
   in assert (fn _ => is_assigned s lit) "unassign_last_lit violates: is_assigned lit" ;
      assert (fn _ => reason_valid s lit reason) "unassign_last_lit violates: reason_valid lit reason" ;
      assert (fn _ => level s lit = !(#decision_level s)) "unassign_last_lit violates: level lit = !(#decision_level s)" ;
      Array.update (!(#reason_array s), var, Unassigned) ;
      Array.update (!(#assignment_array s), var, NONE) ;
      PriorityQueue.enqueue (!(#decision_queue s)) var ;
      if reason = Decision then (#decision_level s) := !(#decision_level s) - 1 else () ;
      if early_level s lit <> invalid_level then 
      (
          assert (fn _ => early_level s lit <= level s lit) 
                 "unassign_last_lit violates: early_level lit <= level lit" ;
          (#pending_literals s) := Queue.enqueue lit (!(#pending_literals s))
      ) else () end
  )

fun is_inferred (s : solver) lit = 
  (assert (fn _ => is_true s lit) "is_inferred violates: is_true lit" ;
   case reason s lit
    of Propagation _ => true
     | _ => false)

fun unit_propagating_clause (s : solver) lit = 
  case reason s lit
   of Propagation cls => 
      (assert (fn _ => explanation_valid s lit (#literals cls)) 
              "unit_propagating_clause violates: explanation_valid lit (#literals cls)" ; cls)
    | _ => raise error "unit_propagating_clause violates: false"

fun del_conflict_lit (s : solver) lit = 
  (assert (fn _ => !(#conflict_detected s)) "del_conflict_lit violates: !(#conflict_detected s)" ;
   assert (fn _ => is_conflict_lit s lit) "del_conflict_lit violates: is_conflict_lit lit" ;
   (#conflict_vars s) := filter (fn x => x <> abs lit) (!(#conflict_vars s)))

fun set_explanation (s : solver) lits = 
  let val lit = Vec.top (#trace s)
  in  Array.app (add_conflict_lit s) lits ;
      del_conflict_lit s lit ;
      (#num_implication_points s) := !(#num_implication_points s) - 1 ;
      unassign_last_lit s ;
      assert (fn _ => !(#conflict_detected s)) "set_explanation violates: !(#conflict_detected s)"
  end

fun explain_inferences (s : solver) = 
  (assert (fn _ => !(#conflict_detected s)) 
          "explain_inferences violates: (#conflict_detected s) ()" ;
   assert (fn _ => not (unsatisfiable s)) 
          "explain_inferences violates: not (unsatisfiable ())" ;
   while not (is_conflict_lit s (Vec.top (#trace s))) do
       unassign_last_lit s ;
   if !(#num_implication_points s) > 1 andalso is_inferred s (Vec.top (#trace s)) then
       let val cls = unit_propagating_clause s (Vec.top (#trace s)) in
           inc_clause_activity s cls ;
           set_explanation s (#literals cls) ;
           explain_inferences s
       end
   else ()
  )

fun set_conflict
      (s : solver) iter fold lits = 
(
  (#num_conflicts s) := !(#num_conflicts s) + 1 ;
  (#conflict_detected s) := true ;
  (#conflict_level s) := fold (fn (l, acc) => Int.max (acc, (level s l))) 0 lits ;
  iter (add_conflict_lit s) lits ;
  if !(#conflict_level s) <> 0 then explain_inferences s else ()
)

fun set_conflict_lits (s : solver) lits = 
(
  assert (fn _ => not (!(#conflict_detected s))) 
         "set_conflict_lits violates: not (!(#conflict_detected s))" ;
  assert (fn _ => array_forall (is_false s) lits) 
         "set_conflict_lits violates: array_forall is_false lits" ;
  set_conflict s Array.app Array.foldl lits ;
  assert (fn _ => !(#conflict_detected s)) "set_conflict_lits violates: !(#conflict_detected s)"
)

fun assign_early_implication (s : solver) lit = 
(
  assert (fn _ => not (!(#conflict_detected s))) 
         "assign_early_implication violates: not (!(#conflict_detected s))" ;
  let val level = early_level s lit
      val reason = early_reason s lit
  in
      if level <= !(#decision_level s) then
      (
          assert (fn _ => explanation_valid s lit (#literals reason)) ;
          if is_false s lit then
          (
              set_conflict_lits s (#literals reason) ;
              inc_clause_activity s reason
          )
          else if not (is_assigned s lit) then
              (assign_lit s lit (Propagation reason)
              )
          else ()
      )
      else
          remove_early_implication s lit ;
      assert (fn _ => invariant s) "assign_early_implication violates: invariant ()"
  end
)

fun backjump_possible (s : solver) = 
  !(#conflict_detected s) andalso 
  !(#conflict_level s) > 0 andalso 
  !(#num_implication_points s) = 1

fun backtrack (s : solver) lev = 
  (
      assert (fn _ => !(#decision_level s) > 0) "backtrack violates: !(#decision_level s) > 0" ;
      assert (fn _ => !(#decision_level s) > lev) "backtrack violates: !(#decision_level s) > lev" ;
      while !(#decision_level s) > lev do
          (
           unassign_last_lit s
          ) ;
      let val n = Vec.length (#trace s) in 
          assert (fn _ => !(#next_inference_lit s) >= n) "backtrack violates: !(#next_inference_lit s) >= n" ;
          (#next_inference_lit s) := n ;
          (#next_inference_cls s) := 0 ;
          (#dispatch_lit s) := Int.min (!(#dispatch_lit s), n)
      end
  )

fun clear_conflict (s : solver) = 
  (
   assert (fn _ => backjump_possible s) "clear_conflict violates: backjump_possible s" ;
   assert (fn _ => !(#decision_level s) = !(#conflict_level s)) "clear_conflict violates: !(#decision_level s) = !(#conflict_level s)" ;
   del_conflict_lit s (Vec.top (#trace s)) ;
   (#num_implication_points s) := 0 ;
   List.app (del_conflict_lit s) (!(#lower_conflict_lits s)) ;
   (#lower_conflict_lits s) := [] ;
   (#conflict_detected s) := false
  )

fun inference_possible (s : solver) = 
  unit_propagation_possible s orelse
  not (Queue.is_empty (!(#pending_literals s))) orelse
  not (Queue.is_empty (!(#pending_clauses s)))

fun is_empty xs = null xs

fun is_implication_point (s : solver) lit = 
  is_conflict_lit s lit andalso level s lit = !(#conflict_level s)

fun literal_map_find (s : solver) arr lit = Array.sub (!arr, lit + !(#max_var s) + 1)

fun remove_known_false (s : solver) lits = 
  let fun keep lit = (not (level s lit = 0 andalso is_false s lit))
  in filter keep lits end

fun array_sort cmp a = 
  Vec.array_sort cmp a 0 (Array.length a)

fun is_not_false (s : solver) lit = 
  let val result = assignment s lit <> SOME false 
  in result end

fun watch_valid (s : solver) cls = 
  let fun earliest_level i = 
          if early_level s i <> invalid_level then
              (assert (fn _ => early_level s i <= level s i) 
                      "watch_valid violates: early_level i <> invalid_level" ;
               early_level s i)
          else level s i
      fun ok i j = 
          let val lit = Array.sub (#literals cls, i)
              val other_lit = Array.sub (#literals cls, j)
          in is_not_false s lit orelse
             (is_true s other_lit andalso earliest_level other_lit <= level s lit)
          end
  in ok 0 1 andalso ok 1 0 end

fun backjump (s : solver) = 
(
  assert (fn _ => backjump_possible s) "backjump violates: backjump_possible s" ;
  assert (fn _ => !(#decision_level s) = !(#conflict_level s)) 
         "backjump violates: !(#decision_level s) = !(#conflict_level s)" ;
  let val lit = Vec.top (#trace s) in 
      assert (fn _ => is_implication_point s lit) 
             "backjump violates: is_implication_point lit" ;
      let
          val learn_lits = ~ lit :: !(#lower_conflict_lits s)
          val norm_learn_lits = remove_known_false s learn_lits
          val cls = new_clause norm_learn_lits
          val lits = #literals cls
          val n = Array.length lits
      in
          if n >= 2 then
              let fun lit_level_compare l0 l1 = 
                      if level s l1 < level s l0 then LESS 
                      else if level s l1 = level s l0 then EQUAL 
                      else GREATER  in
                  array_sort lit_level_compare lits ;
                  assert (fn _ => Array.sub (lits, 0) = ~ lit) 
                         "backjump violates: Array.sub (lits, 0) = ~ lit" ;
                  assert (fn _ => level s (Array.sub (lits, 0)) > level s (Array.sub (lits, 1))) 
                         ("backjump violates: level (Array.sub (lits, 0)) > " ^ 
                          "level (Array.sub (lits, 1))") ;
                  Vec.push (#learned s) cls ;
                  let
                      val watcher0 = (literal_map_find s) (#watchers s) 
                                     (Array.sub (#literals cls, 0))
                      val watcher1 = (literal_map_find s) (#watchers s) 
                                     (Array.sub (#literals cls, 1))
                  in
                      watcher0 := cls :: !watcher0 ;
                      watcher1 := cls :: !watcher1
                  end ;
                  clear_conflict s ;
                  backtrack s (level s (Array.sub (lits, 1)))
              end
          else
          (
              assert (fn _ => Array.length lits = 1) 
                     "backjump violates: Array.length lits = 1" ;
              clear_conflict s ;
              backtrack s 0
          ) ;
          assert (fn _ => Array.sub (lits, 0) = ~ lit) 
                 "backjump violates: Array.sub (lits, 0) = ~ lit" ;
          assert (fn _ => not (is_assigned s (Array.sub (lits, 0)))) ;
          while not (Queue.is_empty (!(#pending_literals s))) do
              let val (pending_literal, 
                       pending_literals) = Queue.dequeue (!(#pending_literals s)) in
                  (#pending_literals s) := pending_literals ;
                  assign_early_implication s (pending_literal)
              end ;
          assert (fn _ => not (is_assigned s (Array.sub (lits, 0))) orelse 
                  early_level s (Array.sub (lits, 0)) <> invalid_level) 
                 ("backjump violates: not (is_assigned (Array.sub (lits, 0))) " ^ 
                  "orelse early_level (Array.sub (lits, 0)) <> invalid_level") ;
          assert (fn _ => not (is_true s (Array.sub (lits, 0)))) 
                 "backjump violates: not (is_true (Array.sub (lits, 0)))" ;
          if is_false s (Array.sub (lits, 0)) then
              (set_conflict_lits s (#literals cls) ;
               assert (fn _ => !(#conflict_detected s)) "backjump violates: !(#conflict_detected s)")
          else
          (
              assign_lit s (Array.sub (lits, 0)) (Propagation cls) ;
              assert (fn _ => n = 1 orelse watch_valid s cls) 
                     "backjump violates: n = 1 orelse watch_valid cls" ;
              assert (fn _ => !(#decision_level s) < !(#conflict_level s)) 
                     "backjump violates: (#decision_level s) () < (#conflict_level s) ()" ;
              assert (fn _ => not (!(#conflict_detected s))) 
                     "backjump violates: not ((#conflict_detected s) ())" ;
              assert (fn _ => inference_possible s) 
                     "backjump violates: inference_possible ()"
          ) ;
          if !(#var_increment s) > !(#shy_of_max s) then rescale_decision_priorities s else () ;
          (#var_increment s) := !(#var_increment s) * !(#scale s) ;
          if !(#cls_increment s) > !(#shy_of_max s) then rescale_clause_activities s else () ;
          (#cls_increment s) := !(#cls_increment s) * !(#scale s) ;
          assert (fn _ => invariant s) "backjump violates: invariant ()"
      end
  end
)

fun is_assigned_var (s : solver) var = Array.sub (!(#assignment_array s), var) <> NONE

fun decision_possible (s : solver) = Vec.length (#trace s) < !(#num_vars s)

fun decide (s : solver) = 
  (assert (fn _ => not (!(#conflict_detected s))) "decide violates: not (!(#conflict_detected s))" ;
   assert (fn _ => not (inference_possible s)) "decide violates: not (inference_possible ())" ;
   assert (fn _ => decision_possible s) "decide violates: decision_possible ()" ;
   while is_assigned_var s (PriorityQueue.head ((!(#decision_queue s)))) do
       PriorityQueue.drop (!(#decision_queue s)) ;
   assert (fn _ => not (PriorityQueue.is_empty (!(#decision_queue s))))
          "decide violates: not (PriorityQueue.is_empty (#decision_queue s))" ;
   let val var = PriorityQueue.dequeue (!(#decision_queue s))
       val lit = 
           if Array.sub (!(#bias s), var) then var
           else ~ var
   in (#num_decisions s) := !(#num_decisions s) + 1 ;
      assign_lit s lit Decision  ;
      assert (fn _ => inference_possible s) "decide violates: inference_possible ()" ;
      assert (fn _ => invariant s) "decide violates: invariant ()" ;
      assert (fn _ => !(#decision_level s) > 0) "decide violates: !(#decision_level s) > 0" ;
      assert (fn _ => not (!(#conflict_detected s))) "decide violates: not (!(#conflict_detected s))" 
   end)

fun cls_compare cls0 cls1 = 
  let val len0 = Array.length (#literals cls0)
      val len1 = Array.length (#literals cls1)
  in assert (fn _ => len0 >= 2) "cls_compare violates: len0 >= 2" ;
     assert (fn _ => len1 >= 2) "cls_compare violates: len1 >= 2" ;
     if len0 = 2 then (if len1 = 2 then EQUAL else LESS)
     else if len1 = 2 then GREATER
     else let val n = if !(#activity cls0) < !(#activity cls1) then LESS
                      else if !(#activity cls0) > !(#activity cls1) then GREATER
                      else EQUAL
          in if n = EQUAL then 
                 (if len0 < len1 then LESS
                  else if len0 > len1 then GREATER
                  else EQUAL)
             else n end end

fun filteri f xs = 
  let fun fltr [] i = []
        | fltr (y :: ys) i = (if f i y then [y] else []) @ fltr ys (i + 1)
  in fltr xs 0 end

fun forget (s : solver) cls = 
  let val w0 = (literal_map_find s) (#watchers s) (Array.sub (#literals cls, 0))
      val w1 = (literal_map_find s) (#watchers s) (Array.sub (#literals cls, 1))
  in w0 := filter (fn x => x <> cls) (!w0) ;
     w1 := filter (fn x => x <> cls) (!w1) end

fun forget_some_learned_clauses (s : solver) =
  (assert (fn _ => not (!(#conflict_detected s))) 
         "forget_some_learned_clauses violates: not ((#conflict_detected s) ())" ;
   Vec.sort cls_compare (#learned s) ;
   let val half = Vec.length (#learned s) div 2
       fun keep i cls = 
           i < half orelse Array.length (#literals cls) = 2 
           orelse (forget s cls ; false)
   in Vec.filteri keep (#learned s) ;
      assert (fn _ => invariant s) 
             "forget_some_learned_clauses violates: invariant ()" ;
      assert (fn _ => not (!(#conflict_detected s))) 
             "forget_some_learned_clauses violates: not (!(#conflict_detected s))"
   end)

fun rev_rem_dup comp x acc = 
fn [] => acc
| (h::t) => 
  if comp h x = EQUAL then rev_rem_dup comp x acc t 
  else rev_rem_dup comp h (h::acc) t

fun flip f x y = f y x

fun remove_sorted_duplicates comp l =
  case sort (uncurry (flip comp)) l 
   of [] => l
    | h :: t => rev_rem_dup comp h [h] t

fun lit_compare (s : solver) lit1 lit2 = 
  let val a1 = if is_true s lit1 then SOME true else if is_false s lit1 then SOME false else NONE
      val a2 = if is_true s lit2 then SOME true else if is_false s lit2 then SOME false else NONE
  in if SOME true = a1 then
         if SOME true = a2 then
             let val level1 = level s lit1
                 val level2 = level s lit2
             in if level1 = level2 then
                    int_ord (lit1, lit2)
                else int_ord (level1, level2)
             end
         else LESS
     else if SOME true = a2 then
         GREATER
     else if NONE = a1 then
         if NONE = a2 then
             int_ord (lit1, lit2)
         else LESS
     else if NONE = a2 then
         GREATER
     else let val level1 = level s lit1
              val level2 = level s lit2
          in if level1 = level2 then
                 int_ord (lit1, lit2)
             else int_ord (level2, level1)
          end
  end

fun level_valid (s : solver) lit = 
  not (is_assigned s lit) orelse 
  0 <= level s lit andalso level s lit <= !(#decision_level s)

fun register_early_implication (s : solver) lit lev cls = 
  (assert (fn _ => not (!(#conflict_detected s))) "register_early_implication violates: not (!(#conflict_detected s))" ;
   assert (fn _ => is_true s lit) "register_early_implication violates: is_true lit" ;
   assert (fn _ => lev < level s lit) "register_early_implication violates: lev < level lit" ;
   assert (fn _ => explanation_valid s lit (#literals cls)) 
          "register_early_implication violates: explanation_valid lit (#literals cls)" ;
   let val old_early_level = early_level s lit
   in if old_early_level = invalid_level orelse lev < old_early_level then
          let val var = abs lit
          in Array.update (!(#early_reason_array s), var, cls) ;
             Array.update (!(#early_level_array s), var, lev) end
      else () ;
      assert (fn _ => not (!(#conflict_detected s))) "register_early_implication violates: not (!(#conflict_detected s))" ;
      assert (fn _ => is_true s lit) "register_early_implication violates: is_true lit"
   end)

fun add_clause (s : solver) lit_list = 
  (if not (!(#conflict_detected s)) then
       (let val norm_lits = remove_known_false s 
                                (remove_sorted_duplicates 
                                     (lit_compare s) lit_list)
            val cls = new_clause norm_lits
            val lits = #literals cls
            val len = Array.length lits
        in Array.app (inc_decision_priority s) lits ;
           case len
            of 0 => set_conflict_lits s (#literals empty_clause)
             | 1 => let val lit = Array.sub (lits, 0)
                    in assert (fn _ => is_not_false s lit orelse !(#decision_level s) > 0)
                              "add_clause violates: is_not_false lit orelse !(#decision_level s) > 0" ;
                       assert (fn _ => level_valid s lit) "add_clause violates: level_valid lit" ;
                       if is_false s lit then
                           (set_conflict_lits s (#literals cls) ;
                            inc_clause_activity s cls)
                       else
                           (
                            if not (is_assigned s lit) then
                                (assign_lit s lit (Propagation cls) ;
                                 assert (fn _ => is_true s lit) "add_clause violates: is_true lit")
                            else () ;
                            if level s lit > 0 then
                                register_early_implication s lit 0 cls
                            else ()
                           ) end
             | _ => 
               (assert (fn _ => len >= 2) "add_clause violates: len >= 2" ;
                let val lit0 = Array.sub (lits, 0)
                    val lit1 = Array.sub (lits, 1)
                in assert (fn _ => is_not_false s lit0 orelse is_false s lit1) 
                          "add_clause violates: is_not_false lit0 orelse is_false lit1" ;
                   assert (fn _ => level_valid s lit0) "add_clause violates: level_valid lit0" ;
                   assert (fn _ => level_valid s lit1) "add_clause violates: level_valid lit1" ;
                   Vec.push (#clause s) cls ;
                   Array.sub (!(#watchers s), lit0 + !(#max_var s) + 1) := cls :: !(Array.sub (!(#watchers s), lit0 + !(#max_var s) + 1)) ;
                   Array.sub (!(#watchers s), lit1 + !(#max_var s) + 1) := cls :: !(Array.sub (!(#watchers s), lit1 + !(#max_var s) + 1)) ;
                   if is_false s lit1 then
                       if is_false s lit0 then
                           (set_conflict_lits s (#literals cls) ;
                            inc_clause_activity s cls)
                       else 
                           (if not (is_assigned s lit0) then
                                (assign_lit s lit0 (Propagation cls) ;
                                 assert (fn _ => is_true s lit0) "add_clause violates: is_true lit0" ;
                                 let val lev0 = level s lit0
                                     val lev1 = level s lit1
                                 in if lev0 > lev1 then
                                        register_early_implication s lit0 lev1 cls
                                    else () end)
                            else ())
                   else () ;
                   assert (fn _ => !(#conflict_detected s) orelse watch_valid s cls) 
                          "add_clause violates: !(#conflict_detected s) orelse watch_valid cls"
                end
               )
        end)
   else
       (assert (fn _ => !(#conflict_detected s)) "add_clause violates: !(#conflict_detected s)" ;
        (#pending_clauses s) := Queue.enqueue lit_list (!(#pending_clauses s))
       ) ;
   assert (fn _ => invariant s) "add_clause violates: invariant ()")

fun unit_propagate_or_conflict (s : solver) lit watcher = 
  (assert (fn _ => not (!(#conflict_detected s)))
          "unit_propagate_or_conflict violates: not (!(#conflict_detected s))" ;
   assert (fn _ => inference_possible s) 
          "unit_propagate_or_conflict violates: inference_possible ()" ;
   assert (fn _ => is_false s lit) "unit_propagate_or_conflict violates: is_false lit" ;
   if !(#next_inference_cls s) < length (!watcher) then
       (let val cls = nth (!watcher) (!(#next_inference_cls s))
            val lits = (#literals cls)
        in assert (fn _ => Array.length lits >= 2)
                  "unit_propagate_or_conflict violates: Array.length lits >= 2" ;
           assert (fn _ => Array.sub (lits, 0) = lit orelse
                   Array.sub (lits, 1) = lit)
                  ("unit_propagate_or_conflict violates: Array.sub (lits, 0) = lit orelse " ^ 
                   "Array.sub (lits, 1) = lit") ;
           let val (lit_idx, other_idx) = 
                   if Array.sub (lits, 0) = lit then (0, 1) else (1, 0)
               val other_lit = Array.sub (lits, other_idx)
               val other_assign = assignment s other_lit
           in if other_assign = SOME true then
                  ((#next_inference_cls s) := !(#next_inference_cls s) + 1 ;
                   unit_propagate_or_conflict s lit watcher)
              else (assert (fn _ => other_assign <> SOME true)
                           "unit_propagate_or_conflict violates: other_assign <> SOME true" ;
                    let val len = Array.length (lits)
                        val i = Array.foldli (fn (i, j, ~1) => 
                                                 if is_false s j then ~1
                                                 else if i >= 2 then i else ~1
                                               | (_, _, x) => x)
                                             ~1 (lits)
                        val i = if i >= 0 then i else len
                    in if i <> len then
                           (Array.update (lits, lit_idx, Array.sub (lits, i)) ;
                            Array.update (lits, i, lit) ;
                            watcher := List.take (!watcher, !(#next_inference_cls s)) @ 
                                       List.drop (!watcher, !(#next_inference_cls s) + 1) ;
                            (literal_map_find s) (#watchers s) (Array.sub (lits, lit_idx)) := 
                            cls :: !((literal_map_find s) (#watchers s) (Array.sub (lits, lit_idx))) ;
                            unit_propagate_or_conflict s lit watcher
                           )
                       else if other_assign = NONE then
                           (assign_lit s (Array.sub (lits, other_idx)) (Propagation cls) ;
                            (#num_inferences s) := !(#num_inferences s) + 1 ;
                            (#next_inference_cls s) := !(#next_inference_cls s) + 1 ;
                            unit_propagate_or_conflict s lit watcher)
                       else
                           (set_conflict_lits s (#literals cls) ;
                            inc_clause_activity s cls)
                    end)
           end end)
   else
       (assert (fn _ => !(#next_inference_cls s) = length (!watcher))
               "unit_propagate_or_conflict violates: !(#next_inference_cls s) = length (!watcher)" ;
        (#next_inference_lit s) := !(#next_inference_lit s) + 1 ;
        (#next_inference_cls s) := 0 ;
        if !(#next_inference_lit s) < Vec.length (#trace s) then
            let val lit = ~ (Vec.get (#trace s) (!(#next_inference_lit s)))
                val watcher = (literal_map_find s) (#watchers s) lit
            in unit_propagate_or_conflict s lit watcher end
        else ())
  )

fun infer (s : solver) = 
  (assert (fn _ => not (!(#conflict_detected s))) "infer violates: not ((#conflict_detected s) ())" ;
   assert (fn _ => inference_possible s) "infer violates: inference_possible ()" ;
   if not (Queue.is_empty (!(#pending_literals s))) then
       assign_early_implication s (let val (pending_literal, 
                                            pending_literals) = Queue.dequeue (!(#pending_literals s))
                                   in ((#pending_literals s) := pending_literals ; pending_literal) end)
   else if not (Queue.is_empty (!(#pending_clauses s))) then
       (add_clause s (let val (pending_clause, 
                               pending_clauses) = Queue.dequeue (!(#pending_clauses s))
                      in ((#pending_clauses s) := pending_clauses ; pending_clause) end))
   else
   (
       assert (fn _ => !(#next_inference_lit s) < Vec.length (#trace s)) ;
       let val lit = ~ (Vec.get (#trace s) (!(#next_inference_lit s)))
           val watcher = (literal_map_find s) (#watchers s) lit
       in unit_propagate_or_conflict s lit watcher end
   ) ;
   assert (fn _ => invariant s) "infer violates: invariant ()")

fun num_learneds (s : solver) = Vec.length (#learned s)

fun satisfied (s : solver) = 
  not (!(#conflict_detected s) orelse decision_possible s 
       orelse inference_possible s)

fun solved (s : solver) = 
  satisfied s orelse unsatisfiable s

fun search (s : solver) = 
(
  while not (solved s) andalso !(#num_conflicts s) < !(#conflict_limit s) do
  (
      while (not (!(#conflict_detected s)) andalso inference_possible s) do
      (
          infer s
      ) ;
      if !(#conflict_detected s) then
          if not (unsatisfiable s) then
          (
              backjump s ;
              if num_learneds s > !(#learneds_limit s) then
                  forget_some_learned_clauses s
              else ()
          )
          else ()
      else if decision_possible s then
          decide s
      else
          assert (fn _ => satisfied s) "search violates: satisfied ()"
  ) ;
  assert (fn _ => not (!(#conflict_detected s)) orelse unsatisfiable s) 
         "search violates: not (!(#conflict_detected s)) orelse unsatisfiable ()" ;
  assert (fn _ => invariant s) "search violates: invariant ()"
)

fun num_clauses s = Vec.length (#clause s)


fun simplify s = 
let fun keep cls =
        Array.all (not o (is_true s)) (#literals cls)
        orelse (forget s cls; false)
in
  Vec.filter keep (#clause s) ;
  Vec.filter keep (#learned s)
end

fun restart s = 
  (assert (fn _ => not (!(#conflict_detected s)))
          "restart violates: not (conflict_detected s)" ;
   if !(#decision_level s) > 0 then backtrack s 0 else () ;
   simplify s ;
   assert (fn _ => invariant s) "restart violates: invariant s" ;
   assert (fn _ => not (!(#conflict_detected s))) "restart violates: not (conflict_detected s)";
   assert (fn _ => !(#decision_level s) = 0) "restart violates: !(#decision_level s) = 0")

fun solve s = 
  (#learneds_limit s := Int.max (1000, (num_clauses s div 3)) ;
   while not (solved s) do
       (restart s ;
        search s ;
        #conflict_limit s := !(#conflict_limit s) * 2 ;
        #learneds_limit s := !(#learneds_limit s) * 12 div 10))

val invalid_position = ~1

fun initialize_arrays s max_vars_plus_one = 
  ((#assignment_array s) := Array.array (max_vars_plus_one, NONE) ;
   (#level_array s) := Array.array (max_vars_plus_one, invalid_level) ;
   (#position s) := Array.array (max_vars_plus_one, invalid_position) ;
   (#reason_array s) := Array.array (max_vars_plus_one, Unassigned) ;
   (#early_reason_array s) := Array.array (max_vars_plus_one, empty_clause) ;
   (#early_level_array s) := Array.array (max_vars_plus_one, invalid_level) ;
   (#bias s) := Array.array (max_vars_plus_one, true) ;
   (#watchers s) := Array.array (2 * max_vars_plus_one, Unsynchronized.ref []) ;
   Array.modify (fn _ => Unsynchronized.ref []) (!(#watchers s)))

fun init s clauses = 
  (let val vars = sort_distinct int_ord (map abs (flat clauses))
   in (#decision_level s) := 0 ;
      (#decision_queue s) := empty_queue () ;
      List.app (PriorityQueue.enqueue (!(#decision_queue s))) vars ;
      (#conflict_detected s) := false ;
      (#conflict_level s) := 0 ;
      (#conflict_vars s) := [] ;
      (#num_implication_points s) := 0 ;
      (#lower_conflict_lits s) := [] ;
      (#next_inference_lit s) := 0 ;
      (#next_inference_cls s) := 0 ;
      (#pending_clauses s) := Queue.empty ;
      (#pending_literals s) := Queue.empty ;
      (#dispatch_lit s) := 0 ;
      (#var_increment s) := 1.0 ;
      (#cls_increment s) := 1.0 ;
      (#num_decisions s) := 0 ;
      (#num_conflicts s) := 0 ;
      (#num_inferences s) := 0 ;
      (#max_var s) := fold (curry Int.max) vars 0 ;
      initialize_arrays s (!(#max_var s) + 1) ;
      (#num_vars s) := length vars ;
      assert (fn _ => invariant s) "init violates at 1: invariant ()" ;
      List.app (add_clause s) clauses ;
      assert (fn _ => invariant s) "init violates at 2: invariant ()"
   end
  )

end;

let
  open SAT_Solver
  open Prop_Logic

  fun mk_clauses f = 
      let fun mk_clause g = 
              let fun mk_lit (BoolVar i) = i
                    | mk_lit (Not (BoolVar i)) = ~i
                    | mk_lit _ = error "mk_clauses: formula is not in CNF!"
              in case g
                  of Or (x, y) => mk_clause x @ mk_clause y
                   | True => [1, ~1]
                   | False => []
                   | _ => [mk_lit g] end
      in case f
          of And (x, y) => mk_clauses x @ mk_clauses y
           | _ => [mk_clause f] end

  fun dptsat fm = 
      let val fm = Prop_Logic.defcnf fm
          val s = DPT_SAT_Solver.empty_solver ()
          val clauses = [1, ~1, 2, ~2] :: mk_clauses fm
      in (DPT_SAT_Solver.init s (clauses) ;
          DPT_SAT_Solver.solve s ;
          if DPT_SAT_Solver.satisfied s then
              SATISFIABLE (DPT_SAT_Solver.assignment s)
          else UNSATISFIABLE NONE) end
in
  SAT_Solver.add_solver ("dptsat", dptsat)
end
