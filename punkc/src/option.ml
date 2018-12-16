let is_some x =
  match x with
    Some _ -> true
  | None -> false

let map x f =
  match x with
    Some x' -> Some (f x')
  | None -> None

let value_map x ~default ~f =
  match x with
    Some x' -> f x'
  | None -> default
