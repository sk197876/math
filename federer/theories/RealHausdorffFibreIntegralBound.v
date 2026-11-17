(** Federer (1969), 2.10.25, pp. 188–189: the upper-integral estimate for
    Hausdorff masses of fibres. Apply the weighted-integral equality 2.10.24
    to each cutoff integrand, then pass to its increasing supremum. No
    measurability of A or of the fibre integrand is imposed. Degrees k,m are
    arbitrary nonnegative real numbers with the actual Gamma normalization. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation RealPowerCoverVariants MetricRealPowerCost RealPower ExtendedRealOrderTopology ExtendedRealBoundsUP PartialFunctionUP PartialFunctionBasic
  LipschitzUP LipschitzBasic EuclideanBallVolume HausdorffMeasure RealHausdorffFibreCost
  RealHausdorffFibreCutoffs RealHausdorffFibreWeightedBound RealHausdorffNullImageFibres
  RealHausdorffWeightedSigmaFinite RealHausdorffProperWeighted HausdorffLengthUP HausdorffDiameterCost
  WeightedMetricLimit MetricScaleEnvelope CaratheodoryBorelRegular MeasureUP MeasureIntegralBounds
  IncreasingUpperIntegralBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_hausdorff_fibre_cutoff_integral_bound]: supporting
    last display in the proof of 2.10.25, p. 189.
    The printed alternative support/properness hypothesis
    transfers to each cutoff function. This establishes
    an upper-integral bound without asserting measurability. *)
Theorem real_hausdorff_fibre_cutoff_integral_bound (R : realType) (X Y : metricType R)
    (f : X -> Y) (L k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) A n :
  is_metric_lipschitz_bound setT f L -> (0<L)%R ->
  real_hausdorff_fibre_integral_condition f A hk hm ->
  @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A< +oo ->
  measure_upper_integral (@real_hausdorff_measure R Y m hm)
    (partial_function_total (real_hausdorff_fibre_cutoff f A hk n))<=
    (real_hausdorff_fibre_bound_constant hk hm L)%:E* @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A.
Proof.
move=> hf hL hcond hfinite.
have hh := @real_hausdorff_fibre_weighted_limit_bound R X Y f L k m hk hm A
  ((n.+1%:R : R)^-1)%R _ hf hL (@reciprocal_metric_cutoff_positive R n)
  (metric_scale_envelope_specification _ _ _) hfinite.
have heq : weighted_metric_limit (fun j : @nonempty_metric_sets R Y=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hm) m (val j)) (@real_hausdorff_measure R Y m hm)
    (real_hausdorff_fibre_cutoff f A hk n)=
    measure_upper_integral (@real_hausdorff_measure R Y m hm)
      (partial_function_total (real_hausdorff_fibre_cutoff f A hk n)).
  case: hcond=> [[B [hB hcover]]|hY].
  - apply: (@real_hausdorff_weighted_sigma_finite_equality R Y m hm _ B)
      (real_hausdorff_fibre_cutoff_nonnegative f A hk n) hB _.
    move=> y hy; apply: hcover.
    change (is_true (0<real_hausdorff_fibre_mass f A hk y)).
    apply: lt_le_trans hy _.
    apply: (extended_real_supremum_upper (real_hausdorff_fibre_cutoffs_supremum f A hk y)).
    by exists n.
  - exact: real_hausdorff_weighted_proper_equality hY (real_hausdorff_fibre_cutoff_nonnegative f A hk n).
by rewrite -heq.
Qed.

(** Source for [real_hausdorff_positive_lipschitz_fibre_integral_bound]:
    direct positive-Lipschitz-bound case of 2.10.25,
    pp. 188–189. Finite source mass permits the
    uniform cutoff estimate and increasing upper-integral
    argument; infinite source mass gives an infinite
    right-hand side because the displayed coefficient
    is strictly positive. *)
Theorem real_hausdorff_positive_lipschitz_fibre_integral_bound (R : realType) (X Y : metricType R)
    (f : X -> Y) (L k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) A :
  is_metric_lipschitz_bound setT f L -> (0<L)%R ->
  real_hausdorff_fibre_integral_condition f A hk hm ->
  measure_upper_integral (@real_hausdorff_measure R Y m hm)
    (partial_function_total (real_hausdorff_fibre_mass f A hk))<=
    (real_hausdorff_fibre_bound_constant hk hm L)%:E* @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A.
Proof.
move=> hf hL hcond.
have hC := @real_hausdorff_fibre_bound_constant_positive R k m hk hm L hL.
have hCE : 0<(real_hausdorff_fibre_bound_constant hk hm L)%:E by rewrite lte_fin.
have hM0 := measure_nonnegative (@real_hausdorff_measure_is_measure R X (k+m)%R (addr_ge0 hk hm)) A.
case hM : (@real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A)=> [M| |] in hM0 *; [|rewrite (gt0_muley hCE); exact: leey|by []].
rewrite -EFinM.
apply: (@nonnegative_upper_integral_increasing_bound R Y (@real_hausdorff_measure R Y m hm)
  (@real_hausdorff_measure_is_measure R Y m hm) (real_hausdorff_fibre_cutoff f A hk)
  (real_hausdorff_fibre_mass f A hk) (real_hausdorff_fibre_bound_constant hk hm L*M)%R).
- exact: real_hausdorff_fibre_cutoff_nonnegative.
- exact: real_hausdorff_fibre_cutoffs_increasing.
- exact: real_hausdorff_fibre_cutoffs_supremum.
- move=> n.
  have hfinite : @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A< +oo by rewrite hM; exact: ltry.
  have hh := real_hausdorff_fibre_cutoff_integral_bound n hf hL hcond hfinite.
  by rewrite hM -EFinM in hh.
Qed.

(** Source for [real_hausdorff_lipschitz_fibre_integral_bound]: direct
    real-degree inequality of 2.10.25, pp. 188–189,
    with any proved nonnegative Lipschitz bound. Zero
    bounds in positive target degree use the null
    image; target degree zero uses 0^0=1 and the
    same estimate with bound one. Thus zero times
    infinite source mass is handled explicitly. *)
Theorem real_hausdorff_lipschitz_fibre_integral_bound (R : realType) (X Y : metricType R)
    (f : X -> Y) (L k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) A :
  is_metric_lipschitz_bound setT f L ->
  real_hausdorff_fibre_integral_condition f A hk hm ->
  measure_upper_integral (@real_hausdorff_measure R Y m hm)
    (partial_function_total (real_hausdorff_fibre_mass f A hk))<=
    (real_hausdorff_fibre_bound_constant hk hm L)%:E* @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A.
Proof.
move=> hf hcond; case: (ltP 0%R L) => [hL|hL].
  exact: real_hausdorff_positive_lipschitz_fibre_integral_bound hf hL hcond.
have hz : L=0%R by apply/eqP; rewrite eq_le hL hf.1.
rewrite hz; rewrite hz in hf.
case: (eqVneq m 0%R) => [hmzero|hmne].
- have h1 := @metric_lipschitz_bound_increase R X Y setT f 0%R 1%R hf ler01.
  have hh := @real_hausdorff_positive_lipschitz_fibre_integral_bound R X Y
    f 1%R k m hk hm A h1 ltr01 hcond.
  have he : real_hausdorff_fibre_bound_constant hk hm 0%R=
      real_hausdorff_fibre_bound_constant hk hm 1%R.
    have hpow : real_power 0%R m=real_power 1%R m.
      by rewrite hmzero !real_power_zero_exponent.
    by rewrite /real_hausdorff_fibre_bound_constant hpow.
  by rewrite he.
- have hpos : (0<m)%R by rewrite lt_def hmne hm.
  rewrite /real_hausdorff_fibre_bound_constant real_power_zero_base // mul0r mul0e.
  rewrite (@real_zero_lipschitz_positive_degree_fibre_integral_zero R X Y
    f k m hk hm A hf hpos).
  exact: lexx.
Qed.
