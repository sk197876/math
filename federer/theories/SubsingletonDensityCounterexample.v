(** A local counterexample to the printed partial-quotient form of Federer
    (1969), 2.10.17(2), p. 179. On R take all subsets as generators, charge
    zero for subsingletons and one otherwise, and let mu be unit mass at
    zero with A={0}. Then psi(A)=0, while every defined related quotient is
    one and arbitrarily small two-point sets are in its domain. Its upper
    density is one, yet mu(A)>2 psi(A). The correction is separate from
    Federer's erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricDiameter MetricDiameterMaps MetricDiameterReal
  PartialFunctionUP CoveringRelationUP CoveringRelationFineness CoveringRelationLimits CoveringConstantLimit
  MeasureUP RegularMeasureUP PointMassMeasure PointMassRegularity MeasureRestriction MeasureDerivates
  CaratheodoryLimitUP CaratheodoryMeasure SubsingletonCoverCost SubsingletonCoverMeasure SubsingletonPointRatio.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [all_sets_covering_relation_fine]: supporting
    standing fineness hypothesis for the local counterexample
    to 2.10.17(2), p. 179. Every point is covered
    at every positive scale by its singleton. *)
Lemma all_sets_covering_relation_fine (R : realType) (X : metricType R) (x : X) :
  covering_relation_fine_at (fun x S => S x) x.
Proof.
apply: (covering_relation_fine_iff_small_diameter _ _).2=> e he.
exists [set x]; split=> //; rewrite extended_metric_diameter_singleton lte_fin; exact he.
Qed.

Section RealCounterexample.
Variable R : realType.
Local Notation X := [the metricType R of real_line_metric R].
Local Notation C := (fun (x : X) (S : set X) => S x).
Local Notation mu := (point_mass R (0%R : R)).
Local Notation A := ([set (0%R : R)]).
Local Notation c := (@subsingleton_cover_cost R X).
Local Notation psi := (@subsingleton_cover_measure R X).
Local Notation f := (@subsingleton_point_ratio R X (0%R : R)).

(** Source for [subsingleton_point_ratio_real_domain_fine]:
    supporting quotient-domain fineness at zero for the
    local counterexample to 2.10.17(2), p. 179.
    The two-point set {0,e/2} has positive cost and
    diameter at most e/2 for every e>0. *)
Lemma subsingleton_point_ratio_real_domain_fine :
  covering_relation_fine_at (fun x S => C x S /\ partial_function_domain f S) (0%R : R).
Proof.
apply: (covering_relation_fine_iff_small_diameter _ _).2=> e he.
pose b := (e/2)%R.
have hb : (0<b)%R by rewrite /b; lra.
have hbe : (b<e)%R by rewrite /b; lra.
have hneq : (0%R : R)!=b by rewrite eq_sym (gt_eqF hb).
pose S : set X := [set (0%R : R)] `|` [set b].
have hcost : c S= 1 := subsingleton_cover_cost_pair R hneq.
have hS : S (0%R : R) by left.
have hratio := @subsingleton_point_ratio_one R X (0%R : R) S hS hcost.
exists S; split; first by split=> //; exists 1.
have hsub : S `<=` `[(0%R : R),b].
  move=> x [->|->]; rewrite /= in_itv /= lexx (ltW hb); by [].
have hdiam := @extended_metric_diameter_mono R X S `[(0%R : R),b] hsub.
rewrite (@extended_metric_diameter_segment R (0%R : R) b (ltW hb)) subr0 in hdiam.
apply: le_lt_trans hdiam _; by rewrite lte_fin.
Qed.

(** Source for [subsingleton_point_ratio_real_upper_one]:
    supporting exact upper density in the local
    counterexample to 2.10.17(2), p. 179. The
    original quotient ignores zero-cost singleton cells
    but has value one on its fine related domain. *)
Lemma subsingleton_point_ratio_real_upper_one :
  covering_upper_limit C f (0%R : R)= 1.
Proof.
apply: covering_upper_limit_constant_fine_domain subsingleton_point_ratio_real_domain_fine _=> S y hS hy.
exact: subsingleton_point_ratio_value hS hy.
Qed.

(** Source for [printed_caratheodory_density_bound_false]: local
    counterexample to the unmodified printed 2.10.17(2), p. 179. All
    standing measure, regularity, nonnegative cost and fineness hypotheses
    hold; the original upper density is in [0,2), but mu(A)>2 psi(A). *)
Theorem printed_caratheodory_density_bound_false :
  (forall S, 0<=c S) /\ is_measure mu /\ is_regular_measure mu /\
  is_caratheodory_limit (fun S : set X => S) c psi /\
  (forall x, covering_relation_fine_at C x) /\
  (forall x, A x -> 0<=covering_upper_limit C f x /\ covering_upper_limit C f x<(2 : R)%:E) /\
  (2 : R)%:E*psi A<mu A.
Proof.
split; first exact: subsingleton_cover_cost_nonnegative.
split; first exact: point_mass_is_measure.
split.
- move=> B; exists B; split=> //; split=> //; exact: point_mass_every_set_measurable.
split; first exact: caratheodory_measure_specification.
split; first exact: all_sets_covering_relation_fine.
split.
- move=> x ->; rewrite subsingleton_point_ratio_real_upper_one; split;
    rewrite ?lee_fin ?lte_fin; lra.
- rewrite subsingleton_cover_singleton_zero mule0 (@point_mass_in R X (0%R : R) A (erefl _)) lte_fin; exact: ltr01.
Qed.
End RealCounterexample.
