(** Federer (1969), 2.10.27, p. 190: supporting upper-integral estimate for
    images of fibres under two nonexpanding maps. Bound the image-fibre
    cutoffs directly by source covering costs, apply the equality criterion
    of 2.10.24, pp. 186–188, and take the increasing cutoff limit as in
    2.10.25, p. 189. The support hypothesis is on the actual image-fibre
    masses; it is not replaced by a hypothesis on source fibre masses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation
  RealHausdorffMeasureLaws MetricRealPowerCost RealPower RealPowerNaturalHausdorff
  MetricDiameterMaps RealHausdorffFibreCost RealHausdorffFibreCutoffs
  RealHausdorffProperWeighted RealHausdorffWeightedSigmaFinite ExtendedRealOrderTopology ExtendedRealBoundsUP PartialFunctionUP PartialFunctionBasic
  LipschitzUP LipschitzFunctionCompact EuclideanBallVolume HausdorffMeasure HausdorffFibreCost
  RealHausdorffFamilyCutoffs RealImageFibreWeightedBound HausdorffWeightedSigmaFinite HausdorffProperWeighted
  HausdorffLengthUP HausdorffDiameterCost WeightedMetricLimit MetricScaleEnvelope CaratheodoryBorelRegular
  MeasureUP MeasureIntegralBounds IncreasingUpperIntegralBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_hausdorff_image_fibre_integral_condition]: supporting
    image-fibre version of the alternative hypothesis
    in 2.10.27, p. 190. For Cartesian projections,
    these images are exactly the printed sections.
    This predicate does not introduce an axiom. *)
Definition real_hausdorff_image_fibre_integral_condition (R : realType) (X Y Z : metricType R)
    (f : X -> Y) (g : X -> Z) (A : set X) (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) :=
  (exists B : nat -> set Y, (forall n, @real_hausdorff_measure R Y m hm (B n)< +oo) /\
    [set y | 0< @real_hausdorff_measure R Z k hk (g @` (A `&` f @^-1` [set y]))] `<=` \bigcup_n B n) \/
  metric_boundedly_compact Y.

(** Source for [real_nonexpanding_image_fibre_cutoff_integral_bound]:
    supporting cutoff estimate for 2.10.27, p. 190,
    following the weighted-cover proof on p. 189.
    A finite source mass is used here; the
    infinite case is handled in the final estimate. *)
Theorem real_nonexpanding_image_fibre_cutoff_integral_bound (R : realType) (X Y Z : metricType R)
    (f : X -> Y) (g : X -> Z) (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) A n :
  is_metric_lipschitz_bound setT f 1%R -> is_metric_lipschitz_bound setT g 1%R ->
  real_hausdorff_image_fibre_integral_condition f g A hk hm ->
  @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A< +oo ->
  measure_upper_integral (@real_hausdorff_measure R Y m hm)
    (partial_function_total (real_hausdorff_set_family_cutoff (fun y=>g @` (A `&` f @^-1` [set y])) hk n))<=
    (@real_hausdorff_fibre_bound_constant R k m hk hm 1%R)%:E* @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A.
Proof.
move=> hf hg hcond hfinite.
pose F y := g @` (A `&` f @^-1` [set y]).
have hh := @real_hausdorff_image_fibre_weighted_limit_bound R X Y Z f g 1%R k m hk hm A
  ((n.+1%:R : R)^-1)%R _ hf hg ltr01 (@reciprocal_metric_cutoff_positive R n)
  (metric_scale_envelope_specification _ _ _) hfinite.
have heq : weighted_metric_limit (fun j : @nonempty_metric_sets R Y=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hm) m (val j)) (@real_hausdorff_measure R Y m hm)
    (real_hausdorff_set_family_cutoff F hk n)=
    measure_upper_integral (@real_hausdorff_measure R Y m hm)
      (partial_function_total (real_hausdorff_set_family_cutoff F hk n)).
  case: hcond=> [[B [hB hcover]]|hY].
  - apply: (@real_hausdorff_weighted_sigma_finite_equality R Y m hm _ B)
      (real_hausdorff_set_family_cutoff_nonnegative F hk n) hB _.
    move=> y hy; apply: hcover.
    change (is_true (0< @real_hausdorff_measure R Z k hk (F y))).
    apply: lt_le_trans hy _.
    apply: (extended_real_supremum_upper (real_hausdorff_set_family_cutoffs_supremum F hk y)).
    by exists n.
  - exact: real_hausdorff_weighted_proper_equality hY (real_hausdorff_set_family_cutoff_nonnegative F hk n).
by rewrite -heq.
Qed.

(** Source for [real_nonexpanding_image_fibre_integral_bound]: supporting
    general form of the first estimate in
    2.10.27, p. 190. Two nonexpanding maps
    replace the particular projections. The finite
    support-cover/properness alternative is imposed on
    the actual image-fibre mass integrand. Infinite
    source and fibre masses and zero degrees remain included. *)
Theorem real_nonexpanding_image_fibre_integral_bound (R : realType) (X Y Z : metricType R)
    (f : X -> Y) (g : X -> Z) (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) A :
  is_metric_lipschitz_bound setT f 1%R -> is_metric_lipschitz_bound setT g 1%R ->
  real_hausdorff_image_fibre_integral_condition f g A hk hm ->
  measure_upper_integral (@real_hausdorff_measure R Y m hm)
    (partial_function_total (fun y=>(@real_hausdorff_measure R Z k hk
      (g @` (A `&` f @^-1` [set y])) : extended_real_line R)))<=
    (@real_hausdorff_fibre_bound_constant R k m hk hm 1%R)%:E* @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A.
Proof.
move=> hf hg hcond.
pose F y := g @` (A `&` f @^-1` [set y]).
have hC := @real_hausdorff_fibre_bound_constant_positive R k m hk hm 1%R ltr01.
have hCE : 0<(@real_hausdorff_fibre_bound_constant R k m hk hm 1%R)%:E by rewrite lte_fin.
have hM0 := measure_nonnegative (@real_hausdorff_measure_is_measure R X (k+m)%R (addr_ge0 hk hm)) A.
case hM : (@real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A)=> [M| |] in hM0 *;
  [|rewrite (gt0_muley hCE); exact: leey|by []].
rewrite -EFinM.
apply: (@nonnegative_upper_integral_increasing_bound R Y (@real_hausdorff_measure R Y m hm)
  (@real_hausdorff_measure_is_measure R Y m hm) (real_hausdorff_set_family_cutoff F hk)
  (fun y=>(@real_hausdorff_measure R Z k hk (F y) : extended_real_line R))
  (@real_hausdorff_fibre_bound_constant R k m hk hm 1%R*M)%R).
- exact: real_hausdorff_set_family_cutoff_nonnegative.
- exact: real_hausdorff_set_family_cutoffs_increasing.
- exact: real_hausdorff_set_family_cutoffs_supremum.
- move=> n.
  have hfinite : @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A< +oo by rewrite hM; exact: ltry.
  have hh := real_nonexpanding_image_fibre_cutoff_integral_bound n hf hg hcond hfinite.
  by rewrite hM -EFinM in hh.
Qed.
