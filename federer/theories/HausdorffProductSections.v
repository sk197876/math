(** Federer (1969), 2.10.27, p. 190: first product-section inequality, with
    an arbitrary metric realization of the Cartesian product whose two
    projections are nonexpanding. Apply the direct image-fibre estimate to
    the abstract projections; no isometry of slices or construction-specific
    product metric is assumed. The sharp Euclidean spherical comparison on
    pp. 190–191 is separate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  EuclideanBallVolume MetricCartesianProductUP LipschitzFunctionCompact HausdorffMeasure
  HausdorffFibreCost NonexpandingFibreImages MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_section_integral_condition]: direct
    finite-measure positive-section support/properness
    alternative in 2.10.27, p. 190. A cover
    formulation is equivalent to the printed exact
    union after intersecting its members with the support. *)
Definition metric_section_integral_condition (R : realType) (P Y Z : metricType R)
    (pair : Y -> Z -> P) (A : set P) (k m : nat) :=
  (exists B : nat -> set Y, (forall n, @hausdorff_measure R Y m (B n)< +oo) /\
    [set y | 0< @hausdorff_measure R Z k (metric_product_section pair A y)] `<=` \bigcup_n B n) \/
  metric_boundedly_compact Y.

(** Source for [federer_2_10_27_hausdorff]: direct first
    inequality of 2.10.27, p. 190, in the
    natural-degree interfaces. Both projections need
    only Lipschitz bound one, so empty or singleton
    factors are included. Keep the printed support
    alternative on the actual section-mass integrand;
    neither A nor that function is assumed measurable. *)
Theorem federer_2_10_27_hausdorff (R : realType) (P Y Z : metricType R)
    (pair : Y -> Z -> P) (first : P -> Y) (second : P -> Z)
    (hp : is_metric_cartesian_product pair first second) (A : set P) k m :
  metric_section_integral_condition pair A k m ->
  measure_upper_integral (@hausdorff_measure R Y m)
    (partial_function_total (fun y=>(@hausdorff_measure R Z k
      (metric_product_section pair A y) : extended_real_line R)))<=
    (euclidean_unit_ball_volume R k*euclidean_unit_ball_volume R m/
      euclidean_unit_ball_volume R (k+m))%R%:E* @hausdorff_measure R P (k+m) A.
Proof.
move=> hcond.
have hi : hausdorff_image_fibre_integral_condition first second A k m.
  case: hcond=> [[B [hB hcover]]|hY]; last by right.
  left; exists B; split=> // y hy; apply: hcover.
  change (is_true (0< @hausdorff_measure R Z k (metric_product_section pair A y))).
  rewrite -(@metric_product_section_image R P Y Z pair first second hp A y); exact hy.
have hh := @nonexpanding_image_fibre_integral_bound R P Y Z first second k m A
  (metric_product_first_nonexpanding hp) (metric_product_second_nonexpanding hp) hi.
have heq : (fun y=>(@hausdorff_measure R Z k (second @` (A `&` first @^-1` [set y])) : extended_real_line R))=
    (fun y=>(@hausdorff_measure R Z k (metric_product_section pair A y) : extended_real_line R)).
  apply: funext=> y; by rewrite (@metric_product_section_image R P Y Z pair first second hp A y).
by rewrite heq /hausdorff_fibre_bound_constant expr1n mul1r in hh.
Qed.
