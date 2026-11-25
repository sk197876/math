(** Finite Borel regular refinement of Federer (1969), 2.10.18(1), used in
    (3), p. 181: take the infimum over open neighbourhoods of B. The
    globally finite case suffices here. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP BorelRegularMeasureUP CaratheodoryLimitUP
  CaratheodoryEnlargementUP CaratheodoryEnlargementDensityBound FiniteBorelOpenInfimum
  CaratheodoryDensityUpperBound MeasureDerivates CoveringRelationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_finite_density_bound]: supporting open-infimum
    step in 2.10.18(3), p. 181 The set B need not be measurable. *)
Theorem caratheodory_finite_density_bound (R : realType) (X : metricType R)
    (F : set (set X)) (c mu psi : set X -> \bar R)
    (E : set X -> set X) (k : R) (B : set X) (t : R) :
  is_caratheodory_enlargement F c E k -> is_measure mu -> is_borel_regular_measure mu ->
  mu setT < +oo ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall S, F S -> closed S) -> (forall S, F S -> measure_measurable mu S) ->
  (0<t)%R ->
  (forall x, B x -> t%:E<covering_upper_limit (caratheodory_family_relation F)
    (measure_ratio_function mu c) x) -> t%:E*psi B<=mu B.
Proof.
move=> hE hm hr hfin hpsi hclosed hmeas ht hlim.
apply: (finite_borel_regular_open_infimum hm hr hfin)=> V ho hBV.
exact: caratheodory_enlargement_density_bound hE hm hpsi hclosed hmeas ho hBV ht hlim.
Qed.
