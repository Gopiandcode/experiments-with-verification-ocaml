
type 'a t = {
  mutable size : int;
  mutable vec : 'a array;
}

 let filter' (p: 'a -> bool) (v: 'a t) =
   let i = ref 0 in (* cur element *)
   let j = ref 0 in  (* cur insertion point *)
   let n = v.size in
   let rec loop () =
     if !i < n then begin
       if p v.vec.(! i) then (
         (* move element i at the first empty slot.
            invariant: i >= j*)
         v.vec.(!j) <- v.vec.(!i);
         incr i;
         incr j
       ) else incr i;
       loop ()
     end
     else () in
   loop ();
   v.size <- !j
