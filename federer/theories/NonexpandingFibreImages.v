(** Federer (1969), 2.10.27, p. 190: supporting upper-integral estimate for
    images of fibres under two nonexpanding maps. Bound the image-fibre
    cutoffs directly by source covering costs, apply the equality criterion
    of 2.10.24, pp. 186–188, and take the increasing cutoff limit as in
    2.10.25, p. 189. The support hypothesis is on the actual image-fibre
    masses; it is not replaced by a hypothesis on source fibre masses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBoundsUP PartialFunctionUP PartialFunctionBasic
  LipschitzUP LipschitzFunctionCompact EuclideanBallVolume HausdorffMeasure HausdorffFibreCost
  HausdorffFamilyCutoffs ImageFibreWeightedBound HausdorffWeightedSigmaFinite HausdorffProperWeighted
  HausdorffLengthUP HausdorffDiameterCost WeightedMetricLimit MetricScaleEnvelope CaratheodoryBorelRegular
  MeasureUP MeasureIntegralBounds IncreasingUpperIntegralBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_image_fibre_integral_condition]: supporting
    image-fibre version of the alternative hypothesis
    in 2.10.27, p. 190. For Cartesian projections,
    these images are exactly the printed sections.
    This predicate does not introduce an axiom. *)
Definition hausdorff_image_fibre_integral_condition (R : realType) (X Y Z : metricType R)
    (f : X -> Y) (g : X -> Z) (A : set X) (k m : nat) :=
  (exists B : nat -> set Y, (forall n, @hausdorff_measure R Y m (B n)< +oo) /\
    [set y | 0< @hausdorff_measure R Z k (g @` (A `&` f @^-1` [set y]))] `<=` \bigcup_n B n) \/
  metric_boundedly_compact Y.

(** Source for [nonexpanding_image_fibre_cutoff_integral_bound]:
    supporting cutoff estimate for 2.10.27, p. 190,
    following the weighted-cover proof on p. 189.
    A finite source mass is used here; the
    infinite case is handled in the final estimate. *)
Theorem nonexpanding_image_fibre_cutoff_integral_bound (R : realType) (X Y Z : metricType R)
    (f : X -> Y) (g : X -> Z) k m A n :
  is_metric_lipschitz_bound setT f 1%R -> is_metric_lipschitz_bound setT g 1%R ->
  hausdorff_image_fibre_integral_condition f g A k m ->
  @hausdorff_measure R X (k+m) A< +oo ->
  measure_upper_integral (@hausdorff_measure R Y m)
    (partial_function_total (hausdorff_set_family_cutoff (fun y=>g @` (A `&` f @^-1` [set y])) k n))<=
    (@hausdorff_fibre_bound_constant R k m 1%R)%:E* @hausdorff_measure R X (k+m) A.
Proof.
move=> hf hg hcond hfinite.
pose F y := g @` (A `&` f @^-1` [set y]).
have hh := @hausdorff_image_fibre_weighted_limit_bound R X Y Z f g 1%R k m A
  ((n.+1%:R : R)^-1)%R _ hf hg ltr01 (@reciprocal_metric_cutoff_positive R n)
  (metric_scale_envelope_specification _ _ _) hfinite.
have heq : weighted_metric_limit (fun j : @nonempty_metric_sets R Y=>val j)
    (fun j=>hausdorff_diameter_cost m (val j)) (@hausdorff_measure R Y m)
    (hausdorff_set_family_cutoff F k n)=
    measure_upper_integral (@hausdorff_measure R Y m)
      (partial_function_total (hausdorff_set_family_cutoff F k n)).
  case: hcond=> [[B [hB hcover]]|hY].
  - apply: (@hausdorff_weighted_sigma_finite_equality R Y m _ B)
      (hausdorff_set_family_cutoff_nonnegative F k n) hB _.
    move=> y hy; apply: hcover.
    change (is_true (0< @hausdorff_measure R Z k (F y))).
    apply: lt_le_trans hy _.
    apply: (extended_real_supremum_upper (hausdorff_set_family_cutoffs_supremum F k y)).
    by exists n.
  - exact: hausdorff_weighted_proper_equality hY (hausdorff_set_family_cutoff_nonnegative F k n).
by rewrite -heq.
Qed.

(** Source for [nonexpanding_image_fibre_integral_bound]: supporting
    general form of the first estimate in
    2.10.27, p. 190. Two nonexpanding maps
    replace the particular projections. The finite
    support-cover/properness alternative is imposed on
    the actual image-fibre mass integrand. Infinite
    source and fibre masses and zero degrees remain included. *)
Theorem nonexpanding_image_fibre_integral_bound (R : realType) (X Y Z : metricType R)
    (f : X -> Y) (g : X -> Z) k m A :
  is_metric_lipschitz_bound setT f 1%R -> is_metric_lipschitz_bound setT g 1%R ->
  hausdorff_image_fibre_integral_condition f g A k m ->
  measure_upper_integral (@hausdorff_measure R Y m)
    (partial_function_total (fun y=>(@hausdorff_measure R Z k
      (g @` (A `&` f @^-1` [set y])) : extended_real_line R)))<=
    (@hausdorff_fibre_bound_constant R k m 1%R)%:E* @hausdorff_measure R X (k+m) A.
Proof.
move=> hf hg hcond.
pose F y := g @` (A `&` f @^-1` [set y]).
have hC : (0<@hausdorff_fibre_bound_constant R k m 1%R)%R.
  rewrite /hausdorff_fibre_bound_constant expr1n mul1r.
  apply: divr_gt0; last exact: (euclidean_unit_ball_volumeE R (k+m)).2.
  exact: mulr_gt0 (euclidean_unit_ball_volumeE R k).2 (euclidean_unit_ball_volumeE R m).2.
have hCE : 0<(@hausdorff_fibre_bound_constant R k m 1%R)%:E by rewrite lte_fin.
have hM0 := measure_nonnegative (@hausdorff_measure_is_measure R X (k+m)) A.
case hM : (@hausdorff_measure R X (k+m) A)=> [M| |] in hM0 *;
  [|rewrite (gt0_muley hCE); exact: leey|by []].
rewrite -EFinM.
apply: (@nonnegative_upper_integral_increasing_bound R Y (@hausdorff_measure R Y m)
  (@hausdorff_measure_is_measure R Y m) (hausdorff_set_family_cutoff F k)
  (fun y=>(@hausdorff_measure R Z k (F y) : extended_real_line R))
  (@hausdorff_fibre_bound_constant R k m 1%R*M)%R).
- exact: hausdorff_set_family_cutoff_nonnegative.
- exact: hausdorff_set_family_cutoffs_increasing.
- exact: hausdorff_set_family_cutoffs_supremum.
- move=> n.
  have hfinite : @hausdorff_measure R X (k+m) A< +oo by rewrite hM; exact: ltry.
  have hh := nonexpanding_image_fibre_cutoff_integral_bound n hf hg hcond hfinite.
  by rewrite hM -EFinM in hh.
Qed.
