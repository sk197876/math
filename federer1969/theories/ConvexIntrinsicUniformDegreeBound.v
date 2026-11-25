(** Federer (1969), 3.2.45, p. 280: one finite constant
    controls every higher intrinsic degree of the second factor. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  IntegralGeometricGauge ProjectionBeta SteinerTubePolynomial MetricDiameterUP MetricDiameter
  ExtendedRealOrderTopology ConvexIntrinsicVolumeIntegrals ConvexIntrinsicDegreePowerBound
  FinitePositivePowerMajorant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_intrinsic_uniform_degree_bound]: the finite
    constant M depending only on the dimensions and k in Federer
    3.2.45, p. 280. Its existence follows from the displayed
    beta-weighted degree comparison and the existing finite order
    bound. The same M works for all original nonempty bounded convex
    sets. The zero degree difference has coefficient exactly one. *)
Theorem convex_intrinsic_uniform_degree_bound (R : realType) n k (hKN : (k <= n)%N) :
  exists M : R, (1 < M)%R /\
    forall r (hJN : (r + k <= n)%N)
      (S : set (inner_metric_space (@euclidean_inner_productP R n))),
      S !=set0 -> is_inner_convex S -> metric_set_bounded S ->
      @integral_geometric_gauge R n (r + k) hJN 1 S <=
        (M^+r)%:E * @integral_geometric_gauge R n k hKN 1 S *
          (extended_metric_diameter S)^+r.
Proof.
pose b := @projection_beta R n k hKN 1.
pose a (j : 'I_n.+1) : R := (b / @projection_beta R n j (steiner_dimension_guard j) 1)%R.
have [M [hM hAll]] := finite_positive_power_majorant a.
exists M; split=> // r hJN S hNonempty hConvex hBound.
case: r hJN=> [hJN|r hJN].
- have -> : hJN = hKN := Prop_irrelevance _ _.
  by rewrite expr0 expe0 mul1e mule1.
- have hRatio := @convex_intrinsic_degree_ratio_bound R n r.+1 k hJN S
    hNonempty hConvex hBound.
  have hK : leq_trans (leq_addl r.+1 k) hJN = hKN := Prop_irrelevance _ _.
  rewrite hK in hRatio.
  pose j : 'I_n.+1 := Ordinal (leq_ltn_trans hJN (ltnSn n)).
  have hCoefficient :
      ((@projection_beta R n k hKN 1 / @projection_beta R n (r.+1 + k) hJN 1)%R)%:E <=
      (M^+r.+1)%:E.
    rewrite lee_fin.
    have h := hAll j r.+1 (ltn0Sn r).
    have hGuard : steiner_dimension_guard j = hJN := Prop_irrelevance _ _.
    by rewrite /a /j /= hGuard in h.
  have hG := (@convex_intrinsic_volume_nonnegative_finite R n k hKN 1 S
    hNonempty hConvex hBound (lexx 1)).1.
  have hD : 0 <= (extended_metric_diameter S)^+r.+1.
    apply: expe_ge0; exact: metric_diameter_nonnegative (extended_metric_diameter_specification S).
  apply: (le_trans hRatio).
  have hFinal := lee_wpmul2r hD (lee_wpmul2r hG hCoefficient).
  exact hFinal.
Qed.
