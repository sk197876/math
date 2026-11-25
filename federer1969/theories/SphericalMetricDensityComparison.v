(** Density comparison supporting Federer (1969), 2.10.19(3)–(5), p. 181. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import MetricClosedBalls MetricDiameterUP MetricDiameter EuclideanBallDiameter
  HausdorffMeasureUP HausdorffDiameterCost EuclideanBallVolume MetricDensities MetricDensityNumericalBounds
  PositiveRadiusLimits PositiveRadiusLimitBounds SphericalBallCostBound DensityDenominatorComparison
  CaratheodoryDensityQuotient WeakCaratheodoryDensityQuotient CaratheodoryDensityUpperBound
  CoveringRelationLimits ExtendedRealBounds MeasureUP MeasureBasic PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [spherical_metric_density_le_covering_upper]: supporting
    comparison for 2.10.19(3)–(5), p. 181 Every small positive-radius
    centred ball is a related closed ball with diameter at most twice its
    radius. Vanishing ball cost is handled explicitly. *)
Lemma spherical_metric_density_le_covering_upper (R : realType) (X : metricType R)
    (m : nat) (mu : set X -> \bar R) a : is_measure mu ->
  upper_metric_density m mu a<=
    covering_upper_limit (caratheodory_family_relation (@is_positive_metric_closed_ball R X))
      (caratheodory_measure_cost_ratio mu (@hausdorff_diameter_cost R X m)) a.
Proof.
move=> hm.
apply: extended_real_inf_greatest=> b [e [he ->]].
have hehalf : (0<e/2)%R by lra.
apply: (@positive_radius_upper_eventual_bound R (metric_ball_density m mu a)
  (extended_real_sup (covering_value_range
    (caratheodory_family_relation (@is_positive_metric_closed_ball R X))
    (caratheodory_measure_cost_ratio mu (@hausdorff_diameter_cost R X m)) a e))
  (e/2)%R hehalf)=> r /andP[hr hre].
pose S := metric_closed_ball a r.
have hF : is_positive_metric_closed_ball S := @positive_closed_ball_satisfies_laws R X a r hr.
have haS : S a by rewrite /S /metric_closed_ball /= mdistxx; exact: ltW hr.
have hsmall : extended_metric_diameter S<e%:E.
  have hd := metric_ball_diameter_upper a (ltW hr).
  apply: le_lt_trans hd _; rewrite lte_fin; lra.
have hcost := @hausdorff_diameter_cost_nonnegative R X m S.
have hcostb := @spherical_ball_cost_bound R X m a r hr.
have hcf : hausdorff_diameter_cost m S < +oo := le_lt_trans hcostb
  (@ltry R (euclidean_unit_ball_volume R m*r^+m)%R).
have hmn := @measure_nonnegative R X mu hm S.
have [z hdiv] := caratheodory_density_divide_finite_denominator hmn hcost hcf.
have hgraph := (@caratheodory_measure_cost_ratio_graph R X mu (@hausdorff_diameter_cost R X m) S z).2 hdiv.
have hv : covering_value_range (caratheodory_family_relation (@is_positive_metric_closed_ball R X))
    (caratheodory_measure_cost_ratio mu (@hausdorff_diameter_cost R X m)) a e z.
  exists S; split; first by split.
  by split.
have hpos := @metric_ball_density_denominator_positive R m r hr.
have hlow := density_smaller_denominator_bound hmn hcost hpos hcostb hdiv.
exact: le_trans hlow (extended_real_sup_upper hv).
Qed.
