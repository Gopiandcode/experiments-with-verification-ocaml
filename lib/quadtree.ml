let max_depth = 10
type 'a elt = {
  mutable elt_x: int; mutable elt_y: int;
  elt_w: int; elt_h: int;
  element: 'a;
  mutable parents: 'a leaf list;
  root: 'a t
} and 'a leaf = {
  mutable elts: 'a elt list
}
and 'a quad = {
      mutable nw: 'a tree;
      mutable ne: 'a tree;
      mutable se: 'a tree;
      mutable sw: 'a tree;
}  
and 'a tree =
 | Quad of 'a quad
 | Leaf of 'a leaf     
and 'a t = {
  x: int; y: int; w: int; h: int;
  mutable modification_allowed: bool;
  mutable tree: 'a tree
}

let root t = t.root

let value t = t.element

let pos t = (t.elt_x,t.elt_y)

let bbox t = (t.elt_x,t.elt_y,t.elt_w,t.elt_h)

let create ~x ~y ~w ~h = {x;y;w;h;tree=Leaf {elts=[]}; modification_allowed=true}

let nw (x,y,w,h) =
  let w1 = w - w / 2 in
  let h1 = h - h / 2 in
  x,y, h1, w1

let ne (x,y, w,h) =
  let w2 = w / 2 in
  let w1 = w - w2 in
  let h1 = h - h / 2 in
  x + w1,y, h1, w2

let sw (x,y, w,h) =
  let w1 = w - w/2 in
  let h2 = h / 2 in
  let h1 = h - h2 in
  x,y + h1, h2, w1

let se (x,y, w,h) =
  let w2 = w/2 in
  let w1 = w - w2 in
  let h2 = h / 2 in
  let h1 = h - h2 in
  x + w1,y + h1, h2, w2

let intersects (x1,y1,w1,h1) (x2,y2,w2,h2) =
  not (x1+w1<x2 || x2+w2<x1 || y1+h1<y2 || y2+h2<y1)

let remove_node node elt =
  elt.parents <- List.filter (fun parent -> not (parent = node)) elt.parents

let intersects_node nw (elt: 'a elt) =
  intersects nw (elt.elt_x, elt.elt_y, elt.elt_w, elt.elt_h)

let intersects_node_pair (elt1: 'a elt) (elt2: 'a elt) =
  intersects (elt1.elt_x, elt1.elt_y, elt1.elt_w, elt1.elt_h) (elt2.elt_x, elt2.elt_y, elt2.elt_w, elt2.elt_h)

let build_leaf elts =
  let node = {elts} in
  List.iter (fun elt -> elt.parents <- node :: elt.parents) elts;
  Leaf node

let rec insert_tree d v bp = function
  | (Leaf contents) when d < max_depth ->
    let elts = contents.elts in
    List.iter (remove_node contents) elts;
    let elts = (v :: elts) in
    let nw = build_leaf (List.filter (intersects_node (nw bp)) elts) in
    let ne = build_leaf (List.filter (intersects_node (ne bp)) elts) in
    let sw = build_leaf (List.filter (intersects_node (sw bp)) elts) in
    let se = build_leaf (List.filter (intersects_node (se bp)) elts) in
    Quad {nw;ne;sw;se}
  | ((Leaf contents) as node) ->
    contents.elts <- v :: contents.elts;
    v.parents <- contents :: v.parents;
    node
  | ((Quad (contents)) as node) ->
    if intersects_node (nw bp) v then begin
      contents.nw <- insert_tree (d + 1) v (nw bp) contents.nw;
    end;
    if intersects_node (ne bp) v then begin
      contents.ne <- insert_tree (d + 1) v (ne bp) contents.ne;
    end;
    if intersects_node (sw bp) v then begin
      contents.sw <- insert_tree (d + 1) v (sw bp) contents.sw;
    end;
    if intersects_node (se bp) v then begin
      contents.se <- insert_tree (d + 1) v (se bp) contents.se;
    end;
    node

let insert_elt elt qtree =
  qtree.tree <- insert_tree 0 elt (qtree.x,qtree.y,qtree.w,qtree.h) qtree.tree

let insert v ~x:elt_x ~y:elt_y ~w:elt_w ~h:elt_h qtree =
  assert (qtree.modification_allowed);
  let elt: 'a elt =
    { elt_x; elt_y; elt_w; elt_h; element=v; parents=[]; root=qtree } in
  qtree.tree <- insert_tree 0 elt (qtree.x,qtree.y,qtree.w,qtree.h) qtree.tree;
  elt
