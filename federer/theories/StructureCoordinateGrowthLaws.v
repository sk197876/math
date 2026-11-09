(** Federer (1969), 3.3.4, p. 289:
    nonnegative actual coordinate costs,
    radial-cutoff monotonicity and transfer
    of the original two growth alternatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MeasureUP MeasureBasic StructureCoordinateGrowth StructureRadialCostLimits
  StructureConeDensityValues ExtendedRealBounds PositiveRadiusLimits PositiveRightOrderLimit
  StructureZeroLimitComparison StructureInfiniteLimitComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Growth.
Variable R:realType.
Variables m k:nat.
Variable phi:set (inner_metric_space (@euclidean_inner_productP R (m+k)))->\bar R.
Variable A:set (inner_metric_space (@euclidean_inner_productP R (m+k))).
Variable a:inner_metric_space (@euclidean_inner_productP R (m+k)).
Variable f:{linear R_n R (m+k)->R_n R (m+k)}.
Variable j:'I_k.

(** Source for [structure_coordinate_cost_nonnegative]:
    every original coordinate-cone cost used
    for B_j/C_j in Federer 3.3.4,
    p. 289, is nonnegative at positive
    radius and aperture, including infinite mass. *)
Lemma structure_coordinate_cost_nonnegative (r s:R):
  is_measure phi ->0<r ->0<s ->(0<=structure_coordinate_cost phi A a f j r s)%E.
Proof.
move=>hPhi hr hs; rewrite /structure_coordinate_cost.
apply:mule_ge0; last by rewrite lee_fin exprn_ge0 // invr_ge0 ltW.
apply:mule_ge0; first exact:measure_nonnegative hPhi _.
by rewrite lee_fin exprn_ge0 // invr_ge0 ltW.
Qed.

(** Source for [structure_coordinate_supremum_nonnegative]:
    the original positive-cutoff radius supremum
    is nonnegative, supporting the ordinary
    zero alternative B_j in Federer 3.3.4,
    p. 289. An actual positive half-cutoff
    radius witnesses its nonempty domain. *)
Lemma structure_coordinate_supremum_nonnegative (delta s:R):
  is_measure phi ->0<delta ->0<s ->
  (0<=structure_coordinate_radial_supremum phi A a f j delta s)%E.
Proof.
move=>hPhi hd hs.
have hr:=structure_density_positive_half_bounds hd.
apply:le_trans (structure_coordinate_cost_nonnegative hPhi (andP hr).1 hs) _.
apply:extended_real_sup_upper; by exists (delta/2).
Qed.

(** Source for [structure_coordinate_supremum_cutoff_mono]:
    the original radius supremum decreases
    with its cutoff, supporting B_j/C_j
    in Federer 3.3.4, p. 289. No
    measure or finite-value hypothesis is used. *)
Lemma structure_coordinate_supremum_cutoff_mono (delta eta s:R):
  delta<=eta ->
  (structure_coordinate_radial_supremum phi A a f j delta s<=
    structure_coordinate_radial_supremum phi A a f j eta s)%E.
Proof.
move=>hde; apply:extended_real_sup_least=>v [r [/andP [hr hrd] ->]].
apply:extended_real_sup_upper; exists r; split=>//.
apply/andP; split=>//; exact:lt_le_trans hrd hde.
Qed.

(** Source for [structure_coordinate_zero_smaller_cutoff]:
    B_j's ordinary zero limit survives
    decreasing the positive radius cutoff,
    supporting Federer 3.3.4, p. 289.
    The conclusion retains every positive
    real aperture and possible infinite costs. *)
Lemma structure_coordinate_zero_smaller_cutoff (delta eta:R):
  is_measure phi ->0<delta ->delta<=eta ->
  positive_right_extended_order_limit (structure_coordinate_radial_supremum phi A a f j eta) 0%E ->
  positive_right_extended_order_limit (structure_coordinate_radial_supremum phi A a f j delta) 0%E.
Proof.
move=>hPhi hd hde hLimit.
apply:(@structure_zero_limit_scaled_comparison R
  (structure_coordinate_radial_supremum phi A a f j delta)
  (structure_coordinate_radial_supremum phi A a f j eta) 1 1 1 ltr01 ltr01 ltr01)=>//.
- move=>s hs; exact:structure_coordinate_supremum_nonnegative hPhi hd hs.
- move=>s _; rewrite mul1r mul1e; exact:structure_coordinate_supremum_cutoff_mono hde.
Qed.

(** Source for [structure_coordinate_infinite_larger_cutoff]:
    C_j's infinite upper limit survives
    increasing the radius cutoff, supporting
    Federer 3.3.4, p. 289. Only the
    original supremum monotonicity is used. *)
Lemma structure_coordinate_infinite_larger_cutoff (delta eta:R):
  delta<=eta ->
  positive_radius_upper_limit (structure_coordinate_radial_supremum phi A a f j delta)=+oo%E ->
  positive_radius_upper_limit (structure_coordinate_radial_supremum phi A a f j eta)=+oo%E.
Proof.
move=>hde hInfinite.
apply:(@structure_infinite_limit_scaled_comparison R
  (structure_coordinate_radial_supremum phi A a f j delta)
  (structure_coordinate_radial_supremum phi A a f j eta) 1 1 1 ltr01 ltr01 ltr01)=>//.
move=>s _; rewrite mul1r mul1e; exact:structure_coordinate_supremum_cutoff_mono hde.
Qed.
End Growth.
