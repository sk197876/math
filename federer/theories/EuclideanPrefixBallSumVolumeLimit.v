(** Actual compressed-ball volume convergence in Federer
    (1969), 3.2.45, pp. 279–280, using the
    proved compact convex volume continuity of 3.2.36. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  EuclideanLinearMaps VectorSetSum CompactSetDistanceProfile CompactHausdorffMetric
  EuclideanPrefixBallSums CompactConvexVolumeHausdorffBound PositiveUniformErrorRadius
  EuclideanLebesgueDimensions NaturalScaledReciprocalTail ExtendedRealOrderLimit RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_prefix_ball_sum_volume_error]: supporting
    anisotropic tube limit for Federer 3.2.45,
    pp. 279–280. The original compact convex volume
    error bound of 3.2.36, p. 272, applies to
    the exact ball sums, whose Hausdorff distance is
    at most h*r. A positive local cutoff controls
    every positive h below it, including a zero
    radius and a thin limiting body. *)
Theorem euclidean_prefix_ball_sum_volume_error (R : realType) n m
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (r : R) :
  K !=set0 -> compact K -> is_inner_convex K -> 0<=r ->
  let B : set (inner_metric_space (@euclidean_inner_productP R n)) :=
    [set x | inner_norm (@euclidean_inner_productP R n) x<=r] in
  let S := fun h : R => vector_set_sum K
    ((@euclidean_diagonal_map R n (fun j => if (j<m)%N then h else 1)) @` B) in
  forall eps : R, 0<eps -> exists d : R, 0<d /\ forall h : R, 0<h -> h<d ->
    `|fine (euclidean_lebesgue_measure n (S h))-fine (euclidean_lebesgue_measure n (S 0))|<eps.
Proof.
move=> hNonempty hCompact hConvex hr B S eps hEps.
pose X := inner_metric_space (@euclidean_inner_productP R n).
have [hZeroNonempty [hZeroCompact hZeroConvex]] :=
  @euclidean_prefix_ball_sum_geometry R n m K 0 r hNonempty hCompact hConvex hr.
pose A : compact_hausdorff_space X := exist _ (S 0) (mem_set (conj hZeroCompact hZeroNonempty)).
have [C [hC hError]] := @compact_convex_volume_hausdorff_bound R n A hZeroConvex.
have [q [hq [hq1 hSmall]]] := positive_uniform_error_radius_exists hC hEps.
have hR : 0<r+1 by lra.
exists (q/(r+1)); split; first by rewrite divr_gt0.
move=> h hh hCutoff.
have [hHNonempty [hHCompact hHConvex]] :=
  @euclidean_prefix_ball_sum_geometry R n m K h r hNonempty hCompact hConvex hr.
pose D : compact_hausdorff_space X := exist _ (S h) (mem_set (conj hHCompact hHNonempty)).
have hDistance : mdist A D<=h*r.
  exact: (@euclidean_prefix_ball_sum_hausdorff_bound R n m K h r A D (ltW hh) hr erefl erefl).
have hScaled : h*(r+1)<q by move: hCutoff; rewrite ltr_pdivlMr.
have hNear : mdist A D<q by nra.
have hNearOne : mdist A D<1 := lt_le_trans hNear hq1.
have hBound := hError D hHConvex hNearOne q hq hq1 hNear.
change (is_true (`|fine (euclidean_lebesgue_measure n (S 0))-
  fine (euclidean_lebesgue_measure n (S h))|<=q*C)) in hBound.
rewrite distrC; exact: le_lt_trans hBound hSmall.
Qed.

(** Source for [euclidean_prefix_ball_sum_volume_sequence_limit]: supporting
    finite evaluation of the anisotropic coefficient limit
    in Federer 3.2.45, pp. 279–280. The actual
    compression factors 1/(N+1) approach zero through
    positive values by the proved Archimedean reciprocal
    tail. Apply the full local volume error bound
    before taking the original extended order limit.
    No sequence of new measure objects is selected. *)
Theorem euclidean_prefix_ball_sum_volume_sequence_limit (R : realType) n m
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (r : R) :
  K !=set0 -> compact K -> is_inner_convex K -> 0<=r ->
  let B : set (inner_metric_space (@euclidean_inner_productP R n)) :=
    [set x | inner_norm (@euclidean_inner_productP R n) x<=r] in
  let S := fun h : R => vector_set_sum K
    ((@euclidean_diagonal_map R n (fun j => if (j<m)%N then h else 1)) @` B) in
  extended_order_limit
    (fun N : nat => (fine (euclidean_lebesgue_measure n (S (N.+1%:R^-1))))%:E)
    (fine (euclidean_lebesgue_measure n (S 0)))%:E.
Proof.
move=> hNonempty hCompact hConvex hr B S; apply: real_error_extended_order_limit=> eps hEps.
have [d [hd hError]] := @euclidean_prefix_ball_sum_volume_error R n m K r
  hNonempty hCompact hConvex hr eps hEps.
have [N hN] := @natural_scaled_reciprocal_tail R 1 d ltr01 hd.
exists N=> J hJ.
have hCutoff := (hN J.+1 (leq_trans hJ (leqnSn J))).2.
rewrite mul1r in hCutoff.
apply: hError; first by rewrite invr_gt0 ltr0n.
exact hCutoff.
Qed.
