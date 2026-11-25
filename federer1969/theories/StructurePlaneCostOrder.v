(** Federer (1969), 3.3.10, p. 296: order laws for the original
    plane-growth alternatives used in the three incidence sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct InnerMetric
  StructureCone StructurePlaneGrowth StructureConeDensityValues ExtendedRealBounds
  MeasureUP MeasureBasic PositiveRightOrderLimit PositiveRadiusLimits
  StructureZeroLimitComparison StructureInfiniteLimitComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_plane_radial_nonnegative]: nonnegative
    original radius suprema in the zero-growth incidence assertion
    of Federer 3.3.10, p. 296, through 3.3.4(1), p. 288.
    A positive half-cutoff witnesses the actual nonempty domain. *)
Lemma structure_plane_radial_nonnegative (R:realType) n k m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)) (V:G (R_n R n) k) (delta s:R):
  is_measure phi ->0<delta ->0<s ->
  (0<=structure_plane_radial_supremum m phi A a V delta s)%E.
Proof.
move=>hPhi hDelta hs.
have hHalf:=structure_density_positive_half_bounds hDelta.
have hCost:(0<=phi (A `&` structure_cone V a (delta/2)%:E s)*
    (((delta/2)^-1)^+m)%:E*((s^-1)^+m)%:E)%E.
  apply:mule_ge0; last by rewrite lee_fin exprn_ge0 // invr_ge0 ltW.
  apply:mule_ge0; first exact:measure_nonnegative hPhi _.
  rewrite lee_fin; apply:exprn_ge0; rewrite invr_ge0; exact:ltW (andP hHalf).1.
apply:le_trans hCost _; apply:extended_real_sup_upper; by exists (delta/2).
Qed.

(** Source for [structure_plane_radial_subset]: source restriction
    for the first fixed-projection conclusion of Federer 3.3.10,
    p. 296. The original E subset A remains arbitrary; positive
    normalization and actual outer monotonicity give the order. *)
Lemma structure_plane_radial_subset (R:realType) n k m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)) (V:G (R_n R n) k) (delta s:R):
  is_measure phi ->E `<=` A ->0<s ->
  (structure_plane_radial_supremum m phi E a V delta s<=
    structure_plane_radial_supremum m phi A a V delta s)%E.
Proof.
move=>hPhi hEA hs.
apply:extended_real_sup_least=>v [r [/andP [hr hrd] ->]].
have hSub:(E `&` structure_cone V a r%:E s) `<=` (A `&` structure_cone V a r%:E s).
  move=>x [hx hCone]; split; [exact:hEA x hx|exact:hCone].
have hCost:=@measure_mono R _ phi hPhi _ _ hSub.
have hR:(0<=((r^-1)^+m)%:E)%E by rewrite lee_fin exprn_ge0 // invr_ge0 ltW.
have hS:(0<=((s^-1)^+m)%:E)%E by rewrite lee_fin exprn_ge0 // invr_ge0 ltW.
apply:le_trans (lee_wpmul2r hS (lee_wpmul2r hR hCost)) _.
apply:extended_real_sup_upper; exists r; split=>//; by apply/andP; split.
Qed.

(** Source for [structure_plane_radial_cutoff_mono]: cofinal
    positive radial cutoffs in the incidence sets of Federer
    3.3.10, p. 296. Every original real radius is retained. *)
Lemma structure_plane_radial_cutoff_mono (R:realType) n k m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)) (V:G (R_n R n) k) (delta eta s:R):
  delta<=eta ->
  (structure_plane_radial_supremum m phi A a V delta s<=
    structure_plane_radial_supremum m phi A a V eta s)%E.
Proof.
move=>hde; apply:extended_real_sup_least=>v [r [/andP [hr hrd] ->]].
apply:extended_real_sup_upper; exists r; split=>//.
apply/andP; split=>//; exact:lt_le_trans hrd hde.
Qed.

(** Source for [structure_plane_zero_growth_subset]: the
    source restriction needed to apply 3.3.8 to the first
    incidence section in Federer 3.3.10, p. 296. Original
    ordinary zero growth for A gives ordinary zero growth
    for each original subset E, without measurability. *)
Lemma structure_plane_zero_growth_subset (R:realType) n k m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)) (V:G (R_n R n) k):
  is_measure phi ->E `<=` A ->structure_plane_zero_growth m phi A a V ->
  structure_plane_zero_growth m phi E a V.
Proof.
move=>hPhi hEA [delta [hDelta hLimit]].
exists delta; split; first exact:hDelta.
apply:(@structure_zero_limit_scaled_comparison R
  (structure_plane_radial_supremum m phi E a V delta)
  (structure_plane_radial_supremum m phi A a V delta) 1 1 1 ltr01 ltr01 ltr01)=>//.
- move=>s hs; exact:(@structure_plane_radial_nonnegative R n k m phi E a V delta s hPhi hDelta hs).
- move=>s /andP [hs _]; rewrite mul1r mul1e.
  exact:structure_plane_radial_subset hPhi hEA hs.
Qed.

(** Source for [structure_plane_zero_smaller_cutoff]: the
    cofinal reciprocal-cutoff description of the first incidence
    set in Federer 3.3.10, p. 296, from 3.3.2 and 3.3.4. *)
Lemma structure_plane_zero_smaller_cutoff (R:realType) n k m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)) (V:G (R_n R n) k) (delta eta:R):
  is_measure phi ->0<delta ->delta<=eta ->
  positive_right_extended_order_limit (structure_plane_radial_supremum m phi A a V eta) 0%E ->
  positive_right_extended_order_limit (structure_plane_radial_supremum m phi A a V delta) 0%E.
Proof.
move=>hPhi hDelta hDE hLimit.
apply:(@structure_zero_limit_scaled_comparison R
  (structure_plane_radial_supremum m phi A a V delta)
  (structure_plane_radial_supremum m phi A a V eta) 1 1 1 ltr01 ltr01 ltr01)=>//.
- move=>s hs; exact:structure_plane_radial_nonnegative hPhi hDelta hs.
- move=>s _; rewrite mul1r mul1e; exact:structure_plane_radial_cutoff_mono hDE.
Qed.

(** Source for [structure_plane_infinite_larger_cutoff]: the
    cofinal reciprocal-cutoff description of the second incidence
    set in Federer 3.3.10, p. 296. Increasing the radial cutoff
    preserves the infinite upper limit, without ordinary convergence. *)
Lemma structure_plane_infinite_larger_cutoff (R:realType) n k m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)) (V:G (R_n R n) k) (delta eta:R):
  delta<=eta ->
  positive_radius_upper_limit (structure_plane_radial_supremum m phi A a V delta)=+oo%E ->
  positive_radius_upper_limit (structure_plane_radial_supremum m phi A a V eta)=+oo%E.
Proof.
move=>hDE hLimit.
apply:(@structure_infinite_limit_scaled_comparison R
  (structure_plane_radial_supremum m phi A a V delta)
  (structure_plane_radial_supremum m phi A a V eta) 1 1 1 ltr01 ltr01 ltr01)=>//.
move=>s _; rewrite mul1r mul1e; exact:structure_plane_radial_cutoff_mono hDE.
Qed.
