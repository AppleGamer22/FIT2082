(* Representation of domains for preprocessing *)
type t =
  | Range of int * int
  | Set of int list

let range lb ub = Range (lb, ub)
let set ks = Set ks

let rappend xs ys = List.fold_left (fun s k -> k :: s) ys xs

let rec merge xs ys =
  let rec aux xs ys acc =
    match xs, ys with
    | ([], s) | (s, []) -> rappend acc s
    | x :: xs', y :: ys' ->
        if x < y then
          aux xs' ys (x :: acc) 
        else if y < x then
          aux xs ys' (y :: acc)
        else
          aux xs' ys' (x :: acc)
  in aux xs ys []

let union x y = match x, y with
  | Set kx, Set ky -> Set (merge kx ky)
  | Range (lx, ux), Range (ly, uy) ->
      Range (min lx ly, max ux uy)
  | (Range (l, u), Set k) | (Set k, Range (l, u)) ->
      Range
        ((List.fold_left min l k),
         (List.fold_left max u k))

let set_intersect xs ys =
  let rec aux xs ys acc =
    match xs, ys with
    | [], _
    | _, [] -> List.rev acc
    | (x :: xs', y :: ys') when x < y ->
      aux xs' (y :: ys') acc
    | (x :: xs', y :: ys') when x > y ->
      aux (x :: xs') ys' acc
    | x :: xs', _ :: ys' ->
      aux xs' ys' (x :: acc)
  in aux xs ys []

let intersect x y = match x, y with
  | Set kx, Set ky ->
    begin
      match set_intersect kx ky with
      | [] -> None
      | z -> Some (Set z)
    end
  | Range (lx, ux), Range(ly, uy) ->
    let lz = max lx ly in
    let uz = min ux uy in
    if lz > uz then
      None
    else
      Some (Range (lz, uz))
  | Range (l, u), Set ks
  | Set ks, Range (l, u) ->
    match List.filter (fun k -> l <= k && k <= u) ks with
    | [] -> None
    | z -> Some (Set z)

let bounds d =
  match d with
  | Range (l, u) -> l, u
  | Set (k :: ks) -> List.fold_left min k ks, List.fold_left max k ks
  | _ -> failwith "Bounds of empty domain"

(* Compute the set of holes in a given domain *)
let holes d =
  match d with
  | Range _ -> []
  | Set ks ->
     let rec aux x ys acc =
       match ys with
       | [] -> List.rev acc
       | y :: ys' ->
          if x < y then
            aux (y+1) ys' ((x, y-1) :: acc)
          else
            aux (y+1) ys' acc
     in
     match List.sort compare ks with
     | x :: xs -> aux (x+1) xs []
     | _ -> []

let lb d = match d with
  | Range (l, _) -> l
  | Set (k :: ks) -> List.fold_left min k ks
  | Set [] -> failwith "Empty domain has no lb"

let ub d = match d with
  | Range (_, u) -> u
  | Set (k :: ks) -> List.fold_left max k ks
  | Set [] -> failwith "Empty domain has no ub"

let size d = match d with
  | Range (l, u) -> if l <= u then u - l + 1 else 0
  | Set xs -> List.length xs

let neg d = match d with
  | Range (l, u) -> Range (-u, -l)
  | Set xs -> Set (List.map ((-) 0) xs |> List.rev)

let add d k = match d with
  | Range (l, u) -> Range (l+k, u+k)
  | Set xs -> Set (List.map ((+) k) xs)
