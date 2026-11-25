(** Expanded continuity support for Federer (1969), 3.2.45,
    p. 279: changing one bounded row has a volume error controlled
    by the original projection-volume supremum of the same source. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerNorm
  InnerConvex InnerProductUP Bilinear EuclideanRowFamily ConvexLinearImageRowSum
  NormalJacobianRowBound LinearImageProjectedVolumeBound ProjectedVolumeGauge
  EuclideanNormalJacobian EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_linear_image_one_row_perturbation]: expanded
    support for the continuity assertion in Federer 3.2.45,
    p. 279. Reuse the first-row Fubini argument, its coordinate
    transport, the earlier polar image-volume bound, and Hadamard's
    inequality. The error is relative to the actual projection-volume
    supremum, so it remains valid for thin convex bodies. *)
Theorem convex_linear_image_one_row_perturbation (R : realType) n m
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (v w : 'I_m.+1 -> R_n R n)
    (F G : {linear R_n R n -> R_n R m.+1}) (i : 'I_m.+1) (delta : R) :
  (m.+1 <= n)%N -> compact K -> is_inner_convex K ->
  is_euclidean_row_family v F -> is_euclidean_row_family w G ->
  (forall j, j != i -> v j = w j) ->
  (forall j, j != i -> (inner_norm (@euclidean_inner_productP R n) (v j) <= 1)%R) ->
  (inner_norm (@euclidean_inner_productP R n) (v i-w i) <= delta)%R ->
  @euclidean_lebesgue_measure R m.+1 (F @` K) <=
    euclidean_lebesgue_measure m.+1 (G @` K) +
      delta%:E * @projected_volume_gauge R n m.+1 K.
Proof.
move=> hMN hCompact hConvex hV hW hCommon hNorm hDifference.
pose d (j : 'I_m.+1) : R_n R n := if j == i then (v j-w j)%R else v j.
have [D hD] := euclidean_row_family_exists d.
have hDCommon x j (hJ : j != i) : D x j = G x j.
  by rewrite hD /d (negbTE hJ) (hCommon j hJ) -hW.
have hFCommon x j (hJ : j != i) : F x j = G x j.
  by rewrite hV (hCommon j hJ) -hW.
have hSum x : F x i = (G x i+D x i)%R.
  rewrite hV hW hD /d eqxx (bilBr (inner_bilinear (@euclidean_inner_productP R n))).
  change (euclidean_inner_product x (v i) =
    (euclidean_inner_product x (w i) +
      (euclidean_inner_product x (v i)-euclidean_inner_product x (w i)))%R).
  by rewrite addrC subrK.
have hVolume := @convex_linear_image_one_row_sum_volume R n m K G D F i
  hCompact hConvex hDCommon hFCommon hSum.
have hSmall :
    (inner_norm (@euclidean_inner_productP R n)
      (Adjoint.inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R m.+1)
        (@coordinate_basisP R n) D (@coordinate_basis R m.+1 i)) <= delta)%R.
  by rewrite (euclidean_row_family_adjoint hD) /d eqxx.
have hOther j (hJ : j != i) :
    (inner_norm (@euclidean_inner_productP R n)
      (Adjoint.inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R m.+1)
        (@coordinate_basisP R n) D (@coordinate_basis R m.+1 j)) <= 1)%R.
  rewrite (euclidean_row_family_adjoint hD) /d (negbTE hJ).
  exact: hNorm.
have hJacobian := @normal_jacobian_one_small_row R n m.+1 D i delta hSmall hOther.
have hImage := @linear_image_projected_volume_bound R n m.+1 D K hMN.
have hCost := lee_wpmul2r (@projected_volume_gauge_nonnegative R n m.+1 K hMN)
  (lee_tofin hJacobian).
have hFinal := leeD (lexx (euclidean_lebesgue_measure m.+1 (G @` K))) (le_trans hImage hCost).
exact: le_trans hVolume hFinal.
Qed.
