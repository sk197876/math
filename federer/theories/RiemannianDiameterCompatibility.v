(** Federer (1969), 3.2.46, p. 281: at every cutoff
    below one, coverings for the original path distance and
    its finite metric carrier have exactly the same diameters.
    This proves compatibility of the Hausdorff definitions;
    no invariance under arbitrary nonlinear metric changes is used. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric MetricDiameterUP MetricDiameter RiemannianTensorUP
  RiemannianMetricCarrier RiemannianDistance ExtendedRealUnitCap
  ExtendedRealUnitCapOrder RiemannianDiameterUP RiemannianDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Diameters.
Context (R : realType) n A g (hg : @is_continuous_riemannian_tensor R n A g).
Local Notation M := (riemannian_metric_space hg).

(** Source for [riemannian_small_diameter_specification]:
    a finite-carrier diameter below one satisfies the independent
    original-rho diameter laws, supporting 3.2.46, p. 281. *)
Lemma riemannian_small_diameter_specification (S : set M) d (delta : R) :
  is_extended_metric_diameter S d -> (d <= delta%:E)%E -> delta < 1 ->
  @is_riemannian_diameter R n A g hg S d.
Proof.
move=> hD hCut hDelta.
have hD0 := metric_diameter_nonnegative hD.
case E : d=> [r| |].
- have hrDelta : r <= delta by move: hCut; rewrite E lee_fin.
  have hr1 : r < 1 := le_lt_trans hrDelta hDelta.
  constructor.
  + by rewrite -E.
  + move=> x y hx hy.
    have hPair := metric_diameter_upper hD hx hy.
    rewrite E lee_fin riemannian_metric_distanceE
      (extended_real_unit_cap_small_le (riemannian_distance_nonnegative A g (val x) (val y)) hr1)
      in hPair.
    exact hPair.
  + move=> b hb hBound; rewrite -E.
    apply: (metric_diameter_least hD hb)=> x y hx hy.
    apply: le_trans _ (hBound x y hx hy).
    rewrite riemannian_metric_distanceE.
    exact: extended_real_unit_cap_below_original (riemannian_distance_nonnegative A g (val x) (val y)).
- by move: hCut; rewrite E.
- by move: hD0; rewrite E.
Qed.

(** Source for [riemannian_capped_diameter_bound]: capping
    cannot enlarge a diameter, supporting the actual covering
    comparison in 3.2.46, p. 281. *)
Lemma riemannian_capped_diameter_bound (S : set M) :
  (extended_metric_diameter S <= riemannian_diameter hg S)%E.
Proof.
pose hOriginal := riemannian_diameter_specification hg S.
apply: (metric_diameter_least (extended_metric_diameter_specification S)
  (riemannian_diameter_nonnegative hOriginal))=> x y hx hy.
apply: le_trans _ (riemannian_diameter_upper hOriginal hx hy).
rewrite riemannian_metric_distanceE.
exact: extended_real_unit_cap_below_original (riemannian_distance_nonnegative A g (val x) (val y)).
Qed.

(** Source for [riemannian_small_diameter_equal]: below each
    cutoff delta<1, the original and finite-carrier diameters
    agree exactly, supporting 3.2.46, p. 281. Empty generators
    are allowed in this supporting identity. *)
Lemma riemannian_small_diameter_equal (S : set M) (delta : R) :
  (extended_metric_diameter S <= delta%:E)%E -> delta < 1 ->
  riemannian_diameter hg S = extended_metric_diameter S.
Proof.
move=> hCut hDelta.
exact: (riemannian_diameter_unique (riemannian_diameter_specification hg S)
  (riemannian_small_diameter_specification (extended_metric_diameter_specification S) hCut hDelta)).
Qed.

(** Source for [riemannian_small_diameter_cutoff]: the two
    metrics give the same admissible generators at each small
    cutoff, with no boundedness or measurability premise,
    supporting 3.2.46, p. 281. *)
Lemma riemannian_small_diameter_cutoff (S : set M) (delta : R) :
  delta < 1 ->
  (riemannian_diameter hg S <= delta%:E)%E =
    (extended_metric_diameter S <= delta%:E)%E.
Proof.
move=> hDelta; apply/idP/idP=> hCut.
- exact: le_trans (riemannian_capped_diameter_bound S) hCut.
- by rewrite (riemannian_small_diameter_equal hCut hDelta).
Qed.
End Diameters.
