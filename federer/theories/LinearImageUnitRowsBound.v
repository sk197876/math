(** Expanded continuity support for Federer (1969), 3.2.45,
    p. 279: maps whose rows have norm at most one are bounded
    by the original projection-volume supremum. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerNorm
  EuclideanRowFamily NormalJacobianRowBound LinearImageProjectedVolumeBound ProjectedVolumeGauge
  EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [linear_image_unit_rows_projected_volume_bound]:
    expanded support for Federer 3.2.45, p. 279. The earlier
    polar volume bound and exterior Hadamard inequality give the
    claim for all actual source sets, without convexity or rank
    hypotheses. The empty row family has product one. *)
Lemma linear_image_unit_rows_projected_volume_bound (R : realType) n m
    (v : 'I_m -> R_n R n) (F : {linear R_n R n -> R_n R m})
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (m <= n)%N -> is_euclidean_row_family v F ->
  (forall i, (inner_norm (@euclidean_inner_productP R n) (v i) <= 1)%R) ->
  @euclidean_lebesgue_measure R m (F @` S) <= @projected_volume_gauge R n m S.
Proof.
move=> hMN hRows hNorm.
have hR i :
    (inner_norm (@euclidean_inner_productP R n)
      (Adjoint.inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
        (@coordinate_basisP R n) F (@coordinate_basis R m i)) <= 1)%R.
  by rewrite (euclidean_row_family_adjoint hRows).
have hJ := @normal_jacobian_row_product_bound R n m F (fun _ => 1%R) hR.
rewrite prodr_const card_ord expr1n in hJ.
have hImage := @linear_image_projected_volume_bound R n m F S hMN.
have hCost := lee_wpmul2r (@projected_volume_gauge_nonnegative R n m S hMN) (lee_tofin hJ).
rewrite mul1e in hCost.
exact: le_trans hImage hCost.
Qed.
