(** Federer (1969), 2.10.25, pp. 188–189: the upper-integral estimate for
    Hausdorff masses of fibres. Apply the weighted-integral equality 2.10.24
    to each cutoff integrand, then pass to its increasing supremum. No
    measurability of A or of the fibre integrand is imposed. Degrees k,m are
    natural numbers in the present Hausdorff interface; Federer's
    real-degree extension remains a separate obligation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBoundsUP PartialFunctionUP PartialFunctionBasic
  LipschitzUP LipschitzBasic EuclideanBallVolume HausdorffMeasure HausdorffFibreCost
  HausdorffFibreCutoffs HausdorffFibreWeightedBound HausdorffNullImageFibres
  HausdorffWeightedSigmaFinite HausdorffProperWeighted HausdorffLengthUP HausdorffDiameterCost
  WeightedMetricLimit MetricScaleEnvelope CaratheodoryBorelRegular MeasureUP MeasureIntegralBounds
  IncreasingUpperIntegralBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_fibre_cutoff_integral_bound]: supporting
    last display in the proof of 2.10.25, p. 189.
    The printed alternative support/properness hypothesis
    transfers to each cutoff function. This establishes
    an upper-integral bound without asserting measurability. *)
Theorem hausdorff_fibre_cutoff_integral_bound (R : realType) (X Y : metricType R)
    (f : X -> Y) (L : R) k m A n :
  is_metric_lipschitz_bound setT f L -> (0<L)%R ->
  hausdorff_fibre_integral_condition f A k m ->
  @hausdorff_measure R X (k+m) A< +oo ->
  measure_upper_integral (@hausdorff_measure R Y m)
    (partial_function_total (hausdorff_fibre_cutoff f A k n))<=
    (hausdorff_fibre_bound_constant k m L)%:E* @hausdorff_measure R X (k+m) A.
Proof.
move=> hf hL hcond hfinite.
have hh := @hausdorff_fibre_weighted_limit_bound R X Y f L k m A
  ((n.+1%:R : R)^-1)%R _ hf hL (@reciprocal_metric_cutoff_positive R n)
  (metric_scale_envelope_specification _ _ _) hfinite.
have heq : weighted_metric_limit (fun j : @nonempty_metric_sets R Y=>val j)
    (fun j=>hausdorff_diameter_cost m (val j)) (@hausdorff_measure R Y m)
    (hausdorff_fibre_cutoff f A k n)=
    measure_upper_integral (@hausdorff_measure R Y m)
      (partial_function_total (hausdorff_fibre_cutoff f A k n)).
  case: hcond=> [[B [hB hcover]]|hY].
  - apply: (@hausdorff_weighted_sigma_finite_equality R Y m _ B)
      (hausdorff_fibre_cutoff_nonnegative f A k n) hB _.
    move=> y hy; apply: hcover.
    change (is_true (0<hausdorff_fibre_mass f A k y)).
    apply: lt_le_trans hy _.
    apply: (extended_real_supremum_upper (hausdorff_fibre_cutoffs_supremum f A k y)).
    by exists n.
  - exact: hausdorff_weighted_proper_equality hY (hausdorff_fibre_cutoff_nonnegative f A k n).
by rewrite -heq.
Qed.

(** Source for [hausdorff_positive_lipschitz_fibre_integral_bound]:
    direct positive-Lipschitz-bound case of 2.10.25,
    pp. 188–189. Finite source mass permits the
    uniform cutoff estimate and increasing upper-integral
    argument; infinite source mass gives an infinite
    right-hand side because the displayed coefficient
    is strictly positive. *)
Theorem hausdorff_positive_lipschitz_fibre_integral_bound (R : realType) (X Y : metricType R)
    (f : X -> Y) (L : R) k m A :
  is_metric_lipschitz_bound setT f L -> (0<L)%R ->
  hausdorff_fibre_integral_condition f A k m ->
  measure_upper_integral (@hausdorff_measure R Y m)
    (partial_function_total (hausdorff_fibre_mass f A k))<=
    (hausdorff_fibre_bound_constant k m L)%:E* @hausdorff_measure R X (k+m) A.
Proof.
move=> hf hL hcond.
have hC : (0<hausdorff_fibre_bound_constant k m L)%R.
  rewrite /hausdorff_fibre_bound_constant; apply: mulr_gt0; first exact: exprn_gt0 hL.
  apply: divr_gt0; last exact: (euclidean_unit_ball_volumeE R (k+m)).2.
  exact: mulr_gt0 (euclidean_unit_ball_volumeE R k).2 (euclidean_unit_ball_volumeE R m).2.
have hCE : 0<(hausdorff_fibre_bound_constant k m L)%:E by rewrite lte_fin.
have hM0 := measure_nonnegative (@hausdorff_measure_is_measure R X (k+m)) A.
case hM : (@hausdorff_measure R X (k+m) A)=> [M| |] in hM0 *; [|rewrite (gt0_muley hCE); exact: leey|by []].
rewrite -EFinM.
apply: (@nonnegative_upper_integral_increasing_bound R Y (@hausdorff_measure R Y m)
  (@hausdorff_measure_is_measure R Y m) (hausdorff_fibre_cutoff f A k)
  (hausdorff_fibre_mass f A k) (hausdorff_fibre_bound_constant k m L*M)%R).
- exact: hausdorff_fibre_cutoff_nonnegative.
- exact: hausdorff_fibre_cutoffs_increasing.
- exact: hausdorff_fibre_cutoffs_supremum.
- move=> n.
  have hfinite : @hausdorff_measure R X (k+m) A< +oo by rewrite hM; exact: ltry.
  have hh := hausdorff_fibre_cutoff_integral_bound n hf hL hcond hfinite.
  by rewrite hM -EFinM in hh.
Qed.

(** Source for [hausdorff_lipschitz_fibre_integral_bound]: direct
    integer-degree inequality of 2.10.25, pp. 188–189,
    with any proved nonnegative Lipschitz bound. Zero
    bounds in positive target degree use the null
    image; target degree zero uses 0^0=1 and the
    same estimate with bound one. Thus zero times
    infinite source mass is handled explicitly. *)
Theorem hausdorff_lipschitz_fibre_integral_bound (R : realType) (X Y : metricType R)
    (f : X -> Y) (L : R) k m A :
  is_metric_lipschitz_bound setT f L ->
  hausdorff_fibre_integral_condition f A k m ->
  measure_upper_integral (@hausdorff_measure R Y m)
    (partial_function_total (hausdorff_fibre_mass f A k))<=
    (hausdorff_fibre_bound_constant k m L)%:E* @hausdorff_measure R X (k+m) A.
Proof.
move=> hf hcond; case: (ltP 0%R L)=> [hL|hL].
  exact: hausdorff_positive_lipschitz_fibre_integral_bound hf hL hcond.
have hz : L=0%R by apply/eqP; rewrite eq_le hL hf.1.
rewrite hz; rewrite hz in hf; case: m hcond=> [hcond|m hcond].
- have h1 := @metric_lipschitz_bound_increase R X Y setT f 0%R 1%R hf ler01.
  have hh := @hausdorff_positive_lipschitz_fibre_integral_bound R X Y f 1%R k 0 A h1 ltr01 hcond.
  by rewrite /hausdorff_fibre_bound_constant !expr0 in hh *.
- rewrite /hausdorff_fibre_bound_constant exprS mul0r mul0r mul0e.
  rewrite (@zero_lipschitz_positive_degree_fibre_integral_zero R X Y f k m.+1 A hf (ltn0Sn m)).
  exact: lexx.
Qed.
