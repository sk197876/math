(** The corrected density on the local counterexample to Federer (1969),
    2.10.17(2), p. 179. The positive point mass divided by the free
    singleton cost is infinity under the corrected zero-denominator
    convention. Thus the corrected upper-density hypothesis fails, while the
    original partial quotient had upper density one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP MetricDiameterMaps
  CoveringRelationLimits ExtendedRealBounds MeasureRestriction PointMassMeasure
  SubsingletonCoverCost CaratheodoryDensityQuotient CaratheodoryDensityFunction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [corrected_subsingleton_point_density_infinite]: supporting
    check of the correction to 2.10.17(2), p. 179. Every positive cutoff
    contains the zero-cost singleton with corrected quotient infinity, as
    prescribed. *)
Lemma corrected_subsingleton_point_density_infinite (R : realType) :
  @covering_upper_limit R [the metricType R of real_line_metric R] (fun x S => S x)
    (caratheodory_density_function (point_mass R (0%R : R))
      (@subsingleton_cover_cost R R) [set (0%R : R)]) (0%R : R) = +oo.
Proof.
pose X := [the metricType R of real_line_metric R].
pose A : set X := [set (0%R : R)].
apply/eqP; rewrite eq_le leey andTb.
apply: extended_real_inf_greatest=> b [e [he ->]].
apply: extended_real_sup_upper; exists A; split; first by [].
split; first by rewrite extended_metric_diameter_singleton lte_fin.
change (caratheodory_density_divide (point_mass R (0%R : R) (A `&` A)) (subsingleton_cover_cost R A)=Some +oo).
rewrite setIid subsingleton_cover_cost_singleton (@point_mass_in R X (0%R : R) A (erefl _)).
apply: caratheodory_density_divide_positive_zero; by rewrite lte_fin ltr01.
Qed.
