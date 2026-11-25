(** Federer (1969), 3.2.45, p. 280: the degree-drop estimate
    follows from the existing projection composition average and the
    diameter estimate for each projected body. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  IntegralGeometricGauge ProjectionBeta HausdorffDiameterCost MetricDiameterUP MetricDiameter
  ExtendedRealOrderTopology ConvexIntrinsicVolumeIntegrals ConvexIntrinsicDegreeDiameterBound
  HausdorffDiameterCostBelowPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_intrinsic_degree_power_bound]: the displayed
    degree comparison before the cube-product estimate in Federer
    3.2.45, p. 280. All nonempty bounded convex sources, natural
    degrees and zero differences retain their original beta constants. *)
Theorem convex_intrinsic_degree_power_bound (R : realType) n r k
    (hJN : (r + k <= n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  S !=set0 -> is_inner_convex S -> metric_set_bounded S ->
  (@projection_beta R n (r + k) hJN 1)%:E *
      @integral_geometric_gauge R n (r + k) hJN 1 S <=
    ((@projection_beta R n k (leq_trans (leq_addl r k) hJN) 1)%:E *
      @integral_geometric_gauge R n k (leq_trans (leq_addl r k) hJN) 1 S) *
      (extended_metric_diameter S)^+r.
Proof.
move=> hNonempty hConvex hBound.
have h := @convex_intrinsic_degree_diameter_bound R n r k hJN S hNonempty hConvex hBound.
apply: (le_trans h).
rewrite muleC.
apply: lee_wpmul2l.
- apply: mule_ge0.
  + rewrite lee_fin; exact: ltW (@projection_beta_positive R n k
      (leq_trans (leq_addl r k) hJN) 1 (lexx 1)).
  + exact: (@convex_intrinsic_volume_nonnegative_finite R n k
      (leq_trans (leq_addl r k) hJN) 1 S hNonempty hConvex hBound (lexx 1)).1.
- exact: hausdorff_diameter_cost_below_power.
Qed.

(** Source for [convex_intrinsic_degree_ratio_bound]: supporting
    division by the positive original beta coefficient in the same
    degree estimate, Federer 3.2.45, p. 280. The actual measures
    and every zero-dimensional case remain in the statement. *)
Corollary convex_intrinsic_degree_ratio_bound (R : realType) n r k
    (hJN : (r + k <= n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  S !=set0 -> is_inner_convex S -> metric_set_bounded S ->
  @integral_geometric_gauge R n (r + k) hJN 1 S <=
    ((@projection_beta R n k (leq_trans (leq_addl r k) hJN) 1 /
        @projection_beta R n (r + k) hJN 1)%R)%:E *
      @integral_geometric_gauge R n k (leq_trans (leq_addl r k) hJN) 1 S *
      (extended_metric_diameter S)^+r.
Proof.
move=> hNonempty hConvex hBound.
pose b := @projection_beta R n (r + k) hJN 1.
have hb : (0 < b)%R := @projection_beta_positive R n (r + k) hJN 1 (lexx 1).
have hb0 : b != 0%R by rewrite gt_eqF.
have h := @convex_intrinsic_degree_power_bound R n r k hJN S hNonempty hConvex hBound.
have hInv : 0 <= (b^-1)%R%:E by rewrite lee_fin invr_ge0; exact: ltW hb.
have hScaled := lee_wpmul2l hInv h.
rewrite !muleA -EFinM mulVf //= in hScaled.
have hScalar : ((b^-1)%R%:E *
    (@projection_beta R n k (leq_trans (leq_addl r k) hJN) 1)%:E) =
    ((@projection_beta R n k (leq_trans (leq_addl r k) hJN) 1 / b)%R)%:E.
  by rewrite -EFinM mulrC.
rewrite hScalar in hScaled.
rewrite div1r in hScaled.
rewrite /integral_geometric_gauge !muleA.
exact hScaled.
Qed.
