(** Federer (1969), 3.2.36, pp. 272--273: finite scalar
    representatives of the actual bounded-convex intrinsic volumes. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  IntegralGeometricGauge ConvexIntrinsicVolumeIntegrals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_intrinsic_finite_part_value]: the finite
    coefficients in the positive-radius polynomial comparison of Federer
    3.2.36, p. 273. The already proved nonnegative finiteness of
    the actual bounded-convex gauge justifies its scalar representative;
    no default value at infinity is used. All natural degrees remain. *)
Lemma convex_intrinsic_finite_part_value (R:realType) n m (hmn:(m<=n)%N)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->
  @integral_geometric_gauge R n m hmn 1 S=
    (fine (@integral_geometric_gauge R n m hmn 1 S))%:E.
Proof.
move=>hNonempty hConvex hBound.
have [hNonnegative hFinite]:=@convex_intrinsic_volume_nonnegative_finite R n m hmn 1 S
  hNonempty hConvex hBound (lexx 1).
symmetry; apply:fineK; by rewrite (ge0_fin_numE hNonnegative).
Qed.
