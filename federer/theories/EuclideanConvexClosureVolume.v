(** Federer (1969), 3.2.35, p. 272:
    every nonempty convex set has the same
    ambient volume as its closure, including
    arbitrary nonmeasurable original sources. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanLebesgueDimensions EuclideanConvexInteriorAlternative ConvexInteriorClosureVolume
  MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_convex_closure_volume]:
    supporting the unrestricted closure reduction
    of Steiner's formula in Federer 3.2.35,
    p. 272. The proved affine-span split
    supplies an original interior point, where
    actual dilation-volume squeezing applies, or
    proves the entire closure null. This
    avoids a Borel or Suslin premise on S
    and never asserts a hull difference null. *)
Theorem euclidean_convex_closure_volume (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  S!=set0 ->is_inner_convex S ->
  euclidean_lebesgue_measure n (closure S)=euclidean_lebesgue_measure n S.
Proof.
move=>hNonempty hS.
have [[b hb]|hNull]:=euclidean_convex_interior_or_null_closure hNonempty hS.
- exact:convex_interior_closure_volume hS hb.
- have hSNull:=@measure_null_subset R _ (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) S (closure S) (@subset_closure _ S) hNull.
  by rewrite hNull hSNull.
Qed.
