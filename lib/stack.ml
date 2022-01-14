
type 'a t = {
  mutable contents: 'a list;
  mutable length: int
}

let create () = {
  contents=[];
  length=0
}

let push st x =
  st.contents <- x :: st.contents;
  st.length <- st.length + 1
  
let pop st =
  match st.contents with
  | [] -> None
  | h :: t ->
    st.contents <- t;
    st.length <- st.length - 1;
    Some h
      
