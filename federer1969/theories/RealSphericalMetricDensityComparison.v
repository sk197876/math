(** Federer 2.10.19(3)-(5), p. 181: compare the original real-degree
    metric density with the existing weak covering density. Keep
    positive-radius balls of diameter zero and their vanishing costs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricDensities RealMetricDensityLimits RealHausdorffNormalisation
  RealPower MetricRealPowerCost RealPowerCoverVariants MetricClosedBalls
  MetricDiameterUP MetricDiameter EuclideanBallDiameter HausdorffMeasureUP
  PositiveRadiusLimits PositiveRadiusLimitBounds DensityDenominatorComparison
  CaratheodoryDensityQuotient WeakCaratheodoryDensityQuotient
  CaratheodoryDensityUpperBound CoveringRelationLimits ExtendedRealBounds
  MeasureUP MeasureBasic PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_spherical_metric_density_le_covering_upper]:
    supporting comparison for Federer 2.10.19(3)-(5), p. 181. Every
    centred positive-radius ball is a related closed ball, and its
    actual diameter cost is at most the real-degree radius denominator.
    Apply the existing denominator comparison, including zero costs. *)
Lemma real_spherical_metric_density_le_covering_upper (R : realType)
    (X : metricType R) (p : R) (hp : (0<=p)%R) (mu : set X -> \bar R) a :
    is_measure mu -> upper_real_metric_density hp mu a<=
      covering_upper_limit (caratheodory_family_relation (@is_positive_metric_closed_ball R X))
        (caratheodory_measure_cost_ratio mu
          (@metric_real_diameter_cost R X (real_hausdorff_normalisation hp) p)) a.
Proof.
move=> hm.
apply: extended_real_inf_greatest => b [e [he ->]].
have hehalf : (0<e/2)%R by lra.
pose c := @metric_real_diameter_cost R X (real_hausdorff_normalisation hp) p.
apply: (@positive_radius_upper_eventual_bound R (real_metric_ball_density hp mu a)
  (extended_real_sup (covering_value_range
    (caratheodory_family_relation (@is_positive_metric_closed_ball R X))
    (caratheodory_measure_cost_ratio mu c) a e)) (e/2)%R hehalf)
  => r /andP [hr hre].
pose S := metric_closed_ball a r.
have hF : is_positive_metric_closed_ball S := @positive_closed_ball_satisfies_laws R X a r hr.
have haS : S a by rewrite /S /metric_closed_ball /= mdistxx; exact: ltW hr.
have hsmall : extended_metric_diameter S<e%:E.
  have hd := metric_ball_diameter_upper a (ltW hr).
  apply: le_lt_trans hd _; rewrite lte_fin; lra.
have hcost : 0<=c S := @metric_real_diameter_cost_ge0 R X
  (real_hausdorff_normalisation hp) p S
  (ltW (real_hausdorff_normalisation_positive hp)).
have hcostb : c S<=
    (real_hausdorff_normalisation hp*real_power (2*r)%R p)%R%:E.
  have hd := metric_ball_diameter_upper a (ltW hr).
  have heq : (r+r)%R=(2*r)%R by ring.
  rewrite heq in hd.
  have hh := @metric_real_power_cost_monotone R (real_hausdorff_normalisation hp) p
    (extended_metric_diameter S) (2*r)%R%:E
    (ltW (real_hausdorff_normalisation_positive hp)) hp
    (metric_diameter_nonnegative (extended_metric_diameter_specification S)) hd.
  by rewrite metric_real_power_cost_finite in hh.
have hcf : c S < +oo := le_lt_trans hcostb
  (@ltry R (real_hausdorff_normalisation hp*real_power (2*r)%R p)%R).
have hmn := @measure_nonnegative R X mu hm S.
have [z hdiv] := caratheodory_density_divide_finite_denominator hmn hcost hcf.
have hgraph := (@caratheodory_measure_cost_ratio_graph R X mu c S z).2 hdiv.
have hv : covering_value_range (caratheodory_family_relation (@is_positive_metric_closed_ball R X))
    (caratheodory_measure_cost_ratio mu c) a e z.
  exists S; split; first by split.
  by split.
have hpos := @real_metric_density_denominator_positive R p r hp hr.
have hlow := density_smaller_denominator_bound hmn hcost hpos hcostb hdiv.
exact: le_trans hlow (extended_real_sup_upper hv).
Qed.
