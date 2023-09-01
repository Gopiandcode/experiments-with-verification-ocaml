
let make_counter () =
  let i = ref 0 in
  fun () ->
    let vl = !i in
    i := vl + 1;
    vl
