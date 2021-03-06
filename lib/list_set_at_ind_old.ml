let set_at_idx i x l0 =
  let rec aux l acc i = match l with
    | [] -> l0
    | _::l' when i=0 -> List.rev_append acc (x::l')
    | y::l' ->
      aux l' (y::acc) (i-1)
  in
  aux l0 [] i
