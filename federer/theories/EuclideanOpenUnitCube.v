(** Federer (1969), 3.2.33, p. 270: the actual open
    unit cube used as the domain of the smooth example. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality finmap lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  EuclideanCoordinateMetric NormDifferentialUP FiniteOffTargetBallCover EuclideanBlockCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_open_unit_cube]: W consists of the
    points whose every coordinate is strictly between zero and one,
    Federer 3.2.33, p. 270. The empty coordinate family
    gives the one-point zero-dimensional cube. *)
Definition euclidean_open_unit_cube (R:realType) n:set (R_n R n):=
  [set x|forall i,0<x i<1].

(** Source for [euclidean_open_unit_cube_interior]: supporting
    the actual domain in the class-infinity assertion of
    Federer 3.2.33, p. 270. A positive finite minimum
    of the distances to the coordinate faces gives an interior
    norm ball, including the empty-coordinate case. *)
Lemma euclidean_open_unit_cube_interior (R:realType) n (x:R_n R n):
  euclidean_open_unit_cube x ->
  norm_domain_interior (inner_norm (@euclidean_inner_productP R n))
    (@euclidean_open_unit_cube R n) x.
Proof.
move=>hx.
pose d i:R:=Order.min (x i) (1-x i).
have hd i:0<d i by rewrite /d lt_min (andP (hx i)).1 subr_gt0 (andP (hx i)).2.
have [r [hr hLower]]:=@finite_positive_values_lower_bound R (Choice.clone 'I_n _)
  setT d (@finite_finset [the finType of 'I_n] setT) (fun i _=>hd i).
exists r; split; first exact hr.
move=>h hh i.
have hi:`|h i|<r:=le_lt_trans (euclidean_coordinate_norm_bound i h) hh.
rewrite ltr_norml in hi.
have /andP [hLow hHigh]:=hi.
have hdx:d i<=x i by rewrite /d ge_min lexx.
have hd1:d i<= 1-x i by rewrite /d ge_min lexx orbT.
have hri:r<=x i:=le_trans (hLower i Logic.I) hdx.
have hr1:r<= 1-x i:=le_trans (hLower i Logic.I) hd1.
rewrite ffunE; apply/andP; split; lra.
Qed.

(** Source for [euclidean_open_unit_cube_join]: the product
    coordinate description of the cube, supporting the fibre
    cubes in Federer 3.2.33, p. 270. *)
Lemma euclidean_open_unit_cube_join (R:realType) a b (u:R_n R a) (v:R_n R b):
  euclidean_open_unit_cube (euclidean_block_join (u,v)) <->
  euclidean_open_unit_cube u /\euclidean_open_unit_cube v.
Proof.
split.
- move=>h; split=>i; first have:=h (lshift b i); last have:=h (rshift a i);
    by rewrite ?euclidean_block_join_left ?euclidean_block_join_right.
- move=>[hu hv] i; rewrite -(splitK i); case:(split i)=>j.
  + by rewrite euclidean_block_join_left.
  + by rewrite euclidean_block_join_right.
Qed.
