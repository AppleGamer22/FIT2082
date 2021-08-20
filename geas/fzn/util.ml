(** Various helper functions *)
exception Not_yet

module H = Hashtbl
module Q = Queue

(* Urgh. Not an efficient solution, but whatever. *)
let div_floor x d = int_of_float @@ floor @@ (float_of_int x) /. (float_of_int d)
let div_ceil x d = int_of_float @@ ceil @@ (float_of_int x) /. (float_of_int d)

let gcd x y =
  let rec aux x y = 
    match y with
    | 0 -> x
    | _ -> aux y (x mod y)
  in
  if x < y then
    aux y x
  else
    aux x y

let gcd_list xs =
  let rec aux ys acc =
    match ys with
    | [] -> acc
    | y :: ys' -> aux ys' (gcd acc y)
  in
  match xs with
  | [] -> failwith "gcd of empty list."
  | x :: xs -> aux xs x

module HashSet = struct
  type 'a t = ('a, unit) H.t

  let create k = H.create k

  (* Make sure there's only one entry per key *)
  let add t e = H.replace t e ()
  let remove t e = H.remove t e

  let elem t e =
    try
      let _ = H.find t e in true
    with Not_found -> false

  let clear t = H.clear t

  let elements t = List.rev (H.fold (fun x _ ys -> x :: ys) t [])
end

module WorkList = struct
  type 'a t = { queue : 'a Q.t ; enqueued : 'a HashSet.t }

  let create () = { queue = Q.create () ; enqueued = HashSet.create 13 }

  let push w e =
    if not (HashSet.elem w.enqueued e) then
      begin
        HashSet.add w.enqueued e ;
        Q.add e w.queue
      end

  let pop w =
    let e = Q.pop w.queue in
    HashSet.remove w.enqueued e ;
    e

  let clear w =
    Q.clear w.queue ;
    HashSet.clear w.enqueued

  let is_empty w = Queue.is_empty w.queue
end

type fmtt = (unit, Format.formatter, unit) format
let print_array f
  ?(pre=("@[[|" : fmtt))
  ?(sep=(";@ " : fmtt))
  ?(post=("@]|]" : fmtt)) fmt xs =
  Format.fprintf fmt pre ;
  let sz = Array.length xs in
  if sz > 0 then
    begin
      f fmt xs.(0) ;
      for i = 1 to sz - 1 do
        Format.fprintf fmt sep ;
        f fmt xs.(i)
      done
    end ;
  Format.fprintf fmt post

let print_list f
  ?(pre=("@[[" : fmtt))
  ?(sep=(";@ " : fmtt))
  ?(post=("@]]" : fmtt)) fmt xs =
  let rec aux = function
    | [] -> Format.fprintf fmt post
    | y :: ys -> (Format.fprintf fmt sep ; f fmt y; aux ys)
  in
  Format.fprintf fmt pre ;
  match xs with
  | y :: ys -> (f fmt y ; aux ys)
  | _ -> () ;
  Format.fprintf fmt post

let hashtbl_map f tbl =
  let tbl' = H.create (H.length tbl) in
  H.iter (fun k v -> H.add tbl' k (f k v)) tbl ;
  tbl' 

let array_last a = a.(Array.length a - 1)
let array_drop a = Array.sub a 0 (Array.length a - 1)

let array_fold2 f r0 a b =
  let sz = min (Array.length a) (Array.length b) in
  let rec aux k r =
    if k < sz then
      aux (k + 1) (f r a.(k) b.(k))
    else r
  in aux 0 r0

let array_foldi f r0 xs =
  let sz = Array.length xs in
  let rec aux k r =
    if k < sz then
      aux (k+1) (f k r xs.(k))
    else
      r
  in aux 0 r0

let array_everyi f xs =
  let sz = Array.length xs in
  let rec aux k =
    if k < sz then
      if f k xs.(k) then
        aux (k+1)
      else
        false
    else true in
  aux 0

let array_combine a b =
  let sz = min (Array.length a) (Array.length b) in
  Array.init sz (fun i -> a.(i), b.(i))

let array_fold1 f xs =
  let sz = Array.length xs in
  assert (sz > 0) ;
  let rec aux k acc =
    if k < sz then
      aux (k+1) (f acc xs.(k))
    else
      acc
  in
  aux 1 xs.(0)
