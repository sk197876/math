(** Federer (1969), 3.4.2(8), p. 315: an adapted
    coordinate cube is a product of cubes with equal side lengths. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric EuclideanBlockCoordinates EuclideanCoordinateCubeUP ConcatenatedFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_coordinate_cube_blocks]: the cubes
    A and B with common side r in 3.4.2(8), p. 315.
    The actual coordinate inequalities give their exact product,
    including the singleton cube when the second block is empty. *)
Theorem critical_coordinate_cube_blocks (R:realType) a b
    (z:R_n R (a+b)) (r:R)
    (Q:set (inner_metric_space (@euclidean_inner_productP R (a+b)))):
  is_euclidean_coordinate_cube z r Q ->exists QA QB,
    is_euclidean_coordinate_cube (euclidean_block_split z).1 r QA /\
    is_euclidean_coordinate_cube (euclidean_block_split z).2 r QB /\
    forall u v,Q (euclidean_block_join (u,v)) <->QA u /\QB v.
Proof.
move=>hQ.
have [QA hQA]:=euclidean_coordinate_cube_exists (euclidean_block_split z).1 hQ.1.
have [QB hQB]:=euclidean_coordinate_cube_exists (euclidean_block_split z).2 hQ.1.
exists QA,QB;split;first exact:hQA.
split;first exact:hQB.
move=>u v;split.
- move=>hx;split.
  + apply:(hQA.2 u).2=>i.
    have hh:=(hQ.2 _).1 hx (lshift b i).
    rewrite euclidean_block_join_left in hh.
    rewrite /euclidean_block_split /= ffunE;exact:hh.
  + apply:(hQB.2 v).2=>i.
    have hh:=(hQ.2 _).1 hx (rshift a i).
    rewrite euclidean_block_join_right in hh.
    rewrite /euclidean_block_split /= ffunE;exact:hh.
- move=>[hu hv];apply:(hQ.2 _).2=>i.
  rewrite -(splitK i);case:(split i)=>j.
  + rewrite euclidean_block_join_left.
    have hh:=(hQA.2 u).1 hu j;by rewrite /euclidean_block_split /= ffunE in hh.
  + rewrite euclidean_block_join_right.
    have hh:=(hQB.2 v).1 hv j;by rewrite /euclidean_block_split /= ffunE in hh.
Qed.
