
type 'a t = {
  mutable contents: 'a list;
}

let create () = {
  contents=[];
}

let push st x =
  st.contents <- x :: st.contents
  
let pop st =
  match st.contents with
  | [] -> None
  | h :: t ->
    st.contents <- t;
    Some h

let length st = List.length st
