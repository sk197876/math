(** Supporting weak-cost restriction theorem for Federer (1969), 2.10.19(5),
    p. 181. The corrected covering quotient permits zero generator costs;
    the actual metric density has positive-radius normalisation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureHull MeasureAlmostUP MeasureAlmostBasic
  TopologicalBorel BorelRegularMeasureUP BorelRegularRestriction CaratheodoryLimitUP
  CaratheodoryLimitMeasure CaratheodoryBorelRegular CaratheodoryWeakEnlargementUP CaratheodoryEnlargementGrowth
  WeakCaratheodorySubmeasureDensity CaratheodoryPositiveCostLimits CaratheodoryDensityUpperBound
  MeasureDerivates PartialFunctionUP CoveringRelationUP CoveringRelationLimits CoveringLimitGraphEquivalence
  DiameterEnlargements.
From Federer Require Import WeakCaratheodoryDensityQuotient CaratheodoryDensityFunction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weak_caratheodory_restricted_upper_density]: supporting
    Borel-hull reduction for 2.10.19(5), p. 181 A may be nonmeasurable and
    only psi(A) is required finite. The auxiliary corrected covering limsup
    is at most one; its lower bound is supplied separately when transferring
    to positive-radius metric density. *)
Theorem weak_caratheodory_restricted_upper_density (R : realType) (X : metricType R)
    (F : set (set X)) (c psi : set X -> \bar R)
    (E : set X -> set X) (k : R) (A : set X) :
  is_weak_caratheodory_enlargement F c E k ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall S, F S -> closed S) -> psi A < +oo ->
  measure_almost_everywhere psi [set x |
    covering_upper_limit (caratheodory_family_relation F) (caratheodory_measure_cost_ratio (measure_restrict psi A) c) x<=1].
Proof.
move=> hE hpsi hclosed hAf.
have hcost (j : set_type F) : 0<=c (val j : set X).
  exact: (@weak_enlargement_cost_nonnegative R X F c E k hE _ (set_valP j)).
have hpm := caratheodory_limit_is_measure hpsi hcost.
have hgenB (j : set_type F) : borel_set (val j : set X).
  exact: closed_borel_set (hclosed _ (set_valP j)).
have hpr := caratheodory_limit_borel_regular hpsi hcost hgenB.
have hmeas S (hS : F S) : measure_measurable psi S.
  exact: (@borel_regular_borel_measurable R X psi hpm hpr S (closed_borel_set (hclosed S hS))).
have [C [hAC [hC hmass]]] := borel_regular_cover hpr A.
have hCm := @borel_regular_borel_measurable R X psi hpm hpr C hC.
have hH := @measure_hull_of_finite_equal_measure R X psi hpm A C hAC hCm hmass hAf.
pose mu := measure_restrict psi C.
have hm := measure_restrict_is_measure hpm C.
have hr := @borel_regular_restrict_borel R X psi hpm hpr C hC.
have hfin : mu setT < +oo by rewrite /mu /measure_restrict setIT -hmass.
have hdom B : mu B<=psi B.
  apply: (@measure_mono R X psi hpm)=> x [_ hx]; exact hx.
have hmS S (hS : F S) : measure_measurable mu S := @measure_restrict_measurable R X psi C S (hmeas S hS).
have hu := @weak_caratheodory_submeasure_upper_density R X F c mu psi E k
  hE hm hr hfin hdom hpsi hclosed hmS.
have hnum S (hS : F S) : measure_restrict psi A S=mu S.
  rewrite /mu /measure_restrict (setIC A S) (setIC C S).
  exact: (@measure_hull_test R X psi A C hH S (hmeas S hS)).
have heq x : covering_upper_limit (caratheodory_family_relation F)
    (caratheodory_measure_cost_ratio (measure_restrict psi A) c) x=
    covering_upper_limit (caratheodory_family_relation F) (caratheodory_measure_cost_ratio mu c) x.
  apply: (covering_limits_graph_equivalent _ x).1=> y S [hS _] z.
  by rewrite /caratheodory_measure_cost_ratio /caratheodory_density_function /= !setTI (hnum S hS).
apply: (@measure_almost_everywhere_mono R X psi hpm _ _ _ hu)=> x hx.
change (covering_upper_limit (caratheodory_family_relation F)
  (caratheodory_measure_cost_ratio (measure_restrict psi A) c) x<=1).
by rewrite heq.
Qed.
