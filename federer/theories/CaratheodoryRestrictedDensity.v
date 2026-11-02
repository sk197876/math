(** Federer (1969), 2.10.18(3), pp. 180–181: the upper density of psi
    restricted to a finite psi-measure set lies between zero and one almost
    everywhere, including outside that set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureHull MeasureAlmostUP MeasureAlmostBasic
  TopologicalBorel BorelRegularMeasureUP BorelRegularRestriction CaratheodoryLimitUP
  CaratheodoryLimitMeasure CaratheodoryBorelRegular CaratheodoryEnlargementUP CaratheodoryEnlargementGrowth
  CaratheodorySubmeasureDensity CaratheodoryPositiveCostLimits CaratheodoryDensityUpperBound
  MeasureDerivates PartialFunctionUP CoveringRelationUP CoveringRelationLimits CoveringLimitGraphEquivalence
  DiameterEnlargements.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_restricted_upper_density]: direct
    conclusion of 2.10.18(3), pp. 180–181, allowing
    a controlled containing generator. A need not be
    measurable; its finite Borel hull preserves every
    numerator on the closed generators. *)
Theorem caratheodory_restricted_upper_density (R : realType) (X : metricType R)
    (F : set (set X)) (c psi : set X -> \bar R)
    (E : set X -> set X) (k : R) (A : set X) :
  is_caratheodory_enlargement F c E k ->
  (forall x, covering_relation_fine_at (caratheodory_family_relation F) x) ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall S, F S -> closed S) -> psi A < +oo ->
  measure_almost_everywhere psi [set x |
    0<=covering_upper_limit (caratheodory_family_relation F) (measure_ratio_function (measure_restrict psi A) c) x /\
    covering_upper_limit (caratheodory_family_relation F) (measure_ratio_function (measure_restrict psi A) c) x<=1].
Proof.
move=> hE hf hpsi hclosed hAf.
have hcost (j : set_type F) : 0<=c (val j : set X).
  exact: ltW (@caratheodory_enlargement_cost_positive R X F c E k hE _ (set_valP j)).
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
have hu := @caratheodory_submeasure_upper_density R X F c mu psi E k
  hE hm hr hfin hdom hpsi hclosed hmS.
have hnum S (hS : F S) : measure_restrict psi A S=mu S.
  rewrite /mu /measure_restrict (setIC A S) (setIC C S).
  exact: (@measure_hull_test R X psi A C hH S (hmeas S hS)).
have heq x : covering_upper_limit (caratheodory_family_relation F)
    (measure_ratio_function (measure_restrict psi A) c) x=
    covering_upper_limit (caratheodory_family_relation F) (measure_ratio_function mu c) x.
  apply: (covering_limits_graph_equivalent _ x).1=> y S [hS _] z.
  by rewrite /measure_ratio_function /= (hnum S hS).
apply: (@measure_almost_everywhere_mono R X psi hpm _ _ _ hu)=> x hx.
split; last by rewrite heq.
have [hl ho] := @caratheodory_positive_cost_limits R X F c (measure_restrict psi A) E k x
  hE (measure_restrict_is_measure hpm A) (hf x).
exact: le_trans hl ho.
Qed.

(** Source for [federer_2_10_18_3]: direct formalisation
    of 2.10.18(3), pp. 180–181. The finite set
    A is arbitrary and the almost-everywhere conclusion
    holds on all of X, under the printed growth condition. *)
Theorem federer_2_10_18_3 (R : realType) (X : metricType R)
    (F : set (set X)) (c mu psi : set X -> \bar R) (eta : R) (A : set X) :
  is_measure mu -> (forall S, F S -> 0<=c S) ->
  (forall x, covering_relation_fine_at (caratheodory_family_relation F) x) ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall S, F S -> closed S) -> (forall S, F S -> measure_measurable mu S) ->
  (forall S, F S -> F (diameter_enlargement F S)) ->
  (forall S, F S -> c (diameter_enlargement F S)<eta%:E*c S /\ eta%:E*c S < +oo) ->
  psi A < +oo ->
  measure_almost_everywhere psi [set x |
    0<=covering_upper_limit (caratheodory_family_relation F) (measure_ratio_function (measure_restrict psi A) c) x /\
    covering_upper_limit (caratheodory_family_relation F) (measure_ratio_function (measure_restrict psi A) c) x<=1].
Proof.
move=> hm hc hf hpsi hclosed hmeas hF hg hAf.
have hE := federer_caratheodory_enlargement_laws hc hF hg.
exact: caratheodory_restricted_upper_density hE hf hpsi hclosed hAf.
Qed.
