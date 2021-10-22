module MLS.TreeMath

open MLS.TreeMath.Internal

let node_index (l:nat) = x:nat{level x == l}

val left: #l:pos -> node_index l -> node_index (l-1)
let left #l x =
  level_left_right x;
  left x

val right: #l:pos -> node_index l -> node_index (l-1)
let right #l x =
  level_left_right x;
  right x

val root: l:nat -> node_index l
let root l =
  level_root l;
  root l

val parent: #l:nat -> node_index l -> node_index (l+1)
let parent x =
  level_parent x;
  parent x
