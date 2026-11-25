(** Federer (1969), 2.10.27, p. 190: first product-section inequality, with
    an arbitrary metric realization of the Cartesian product whose two
    projections are nonexpanding. Apply the direct image-fibre estimate to
    the abstract projections; no isometry of slices or construction-specific
    product metric is assumed. The sharp Euclidean spherical comparison on
    pp. 190–191 is separate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation
  RealHausdorffMeasureLaws MetricRealPowerCost RealPower RealPowerNaturalHausdorff
  MetricDiameterMaps RealHausdorffFibreCost RealHausdorffFibreCutoffs
  RealHausdorffProperWeighted RealHausdorffWeightedSigmaFinite ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  EuclideanBallVolume MetricCartesianProductUP LipschitzFunctionCompact HausdorffMeasure
  HausdorffFibreCost RealNonexpandingFibreImages MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_metric_section_integral_condition]: direct
    finite-measure positive-section support/properness
    alternative in 2.10.27, p. 190. A cover
    formulation is equivalent to the printed exact
    union after intersecting its members with the support. *)
Definition real_metric_section_integral_condition (R : realType) (P Y Z : metricType R)
    (pair : Y -> Z -> P) (A : set P) (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) :=
  (exists B : nat -> set Y, (forall n, @real_hausdorff_measure R Y m hm (B n)< +oo) /\
    [set y | 0< @real_hausdorff_measure R Z k hk (metric_product_section pair A y)] `<=` \bigcup_n B n) \/
  metric_boundedly_compact Y.

(** Source for [federer_2_10_27_real_hausdorff]: direct first
    inequality of 2.10.27, p. 190, in the
    real-degree interfaces, using the actual Gamma normalization. Both projections need
    only Lipschitz bound one, so empty or singleton
    factors are included. Keep the printed support
    alternative on the actual section-mass integrand;
    neither A nor that function is assumed measurable. *)
Theorem federer_2_10_27_real_hausdorff (R : realType) (P Y Z : metricType R)
    (pair : Y -> Z -> P) (first : P -> Y) (second : P -> Z)
    (hp : is_metric_cartesian_product pair first second) (A : set P) (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) :
  real_metric_section_integral_condition pair A hk hm ->
  measure_upper_integral (@real_hausdorff_measure R Y m hm)
    (partial_function_total (fun y=>(@real_hausdorff_measure R Z k hk
      (metric_product_section pair A y) : extended_real_line R)))<=
    (real_hausdorff_normalisation hk*real_hausdorff_normalisation hm/
      real_hausdorff_normalisation (addr_ge0 hk hm))%R%:E* @real_hausdorff_measure R P (k+m)%R (addr_ge0 hk hm) A.
Proof.
move=> hcond.
have hi : real_hausdorff_image_fibre_integral_condition first second A hk hm.
  case: hcond=> [[B [hB hcover]]|hY]; last by right.
  left; exists B; split=> // y hy; apply: hcover.
  change (is_true (0< @real_hausdorff_measure R Z k hk (metric_product_section pair A y))).
  rewrite -(@metric_product_section_image R P Y Z pair first second hp A y); exact hy.
have hh := @real_nonexpanding_image_fibre_integral_bound R P Y Z first second k m hk hm A
  (metric_product_first_nonexpanding hp) (metric_product_second_nonexpanding hp) hi.
have heq : (fun y=>(@real_hausdorff_measure R Z k hk (second @` (A `&` first @^-1` [set y])) : extended_real_line R))=
    (fun y=>(@real_hausdorff_measure R Z k hk (metric_product_section pair A y) : extended_real_line R)).
  apply: funext=> y; by rewrite (@metric_product_section_image R P Y Z pair first second hp A y).
by rewrite heq /real_hausdorff_fibre_bound_constant real_power_one_base mul1r in hh.
Qed.
