(** Supporting weak-cost density consequence for Federer (1969),
    2.10.19(3)–(5), p. 181. The corrected covering quotient permits zero
    costs; original metric-density normalisations stay positive. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP BorelRegularMeasureUP CaratheodoryLimitUP
  CaratheodoryWeakEnlargementUP WeakCaratheodoryEnlargementDensityBound FiniteBorelOpenInfimum
  CaratheodoryDensityUpperBound MeasureDerivates CoveringRelationLimits.
From Federer Require Import WeakCaratheodoryDensityQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weak_caratheodory_finite_density_bound]: supporting
    weak-cost density estimate for 2.10.19(3)–(5), p. 181 This explicitly
    uses the corrected covering quotient and controlled containing
    generators. *)
Theorem weak_caratheodory_finite_density_bound (R : realType) (X : metricType R)
    (F : set (set X)) (c mu psi : set X -> \bar R)
    (E : set X -> set X) (k : R) (B : set X) (t : R) :
  is_weak_caratheodory_enlargement F c E k -> is_measure mu -> is_borel_regular_measure mu ->
  mu setT < +oo ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall S, F S -> closed S) -> (forall S, F S -> measure_measurable mu S) ->
  (0<t)%R ->
  (forall x, B x -> t%:E<covering_upper_limit (caratheodory_family_relation F)
    (caratheodory_measure_cost_ratio mu c) x) -> t%:E*psi B<=mu B.
Proof.
move=> hE hm hr hfin hpsi hclosed hmeas ht hlim.
apply: (finite_borel_regular_open_infimum hm hr hfin)=> V ho hBV.
exact: weak_caratheodory_enlargement_density_bound hE hm hpsi hclosed hmeas ho hBV ht hlim.
Qed.
