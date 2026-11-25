(** Federer (1969), 2.2.12, pp. 68–69: closed inner approximation relative
    to any finite-measure test set, followed by Caratheodory measurability
    of every Suslin set. The restriction in the first line of the printed
    proof is retained and the test set need not be measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import SuslinSetUP MeasureUP MeasureRestriction
  SuslinClosedApproximationFinite MeasurableInnerApproximationCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [suslin_closed_inner_approximation]: direct first
    assertion of Federer 2.2.12, p. 68. For any finite
    test set T and positive delta, S contains a closed C with
    mu((T intersection S) minus C) at most delta. The ambient
    space is arbitrary topological, exactly as in the book. *)
Theorem suslin_closed_inner_approximation (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (S T : set X) (delta : R) :
  (forall C : set X, closed C -> measure_measurable mu C) ->
  is_suslin_set R S -> mu T < +oo -> (0 < delta)%R ->
  exists C, closed C /\ C `<=` S /\ mu ((T `&` S) `\` C) <= delta%:E.
Proof.
move=> hc hS hT hd.
pose nu := measure_restrict mu T.
have hn : is_measure nu := measure_restrict_is_measure hm T.
have hnc C : closed C -> measure_measurable nu C.
  move=> hC; exact: (@measure_restrict_measurable R X mu T C (hc C hC)).
have hnt : nu setT < +oo by rewrite /nu /measure_restrict setIT.
have [C [hC [hCS herr]]] :=
  @suslin_closed_approximation_finite_measure R X nu hn S delta hnc hnt hS hd.
exists C; split=> //; split=> //.
by move: herr; rewrite /nu /measure_restrict setIDA.
Qed.

(** Source for [suslin_set_measurable]: direct final assertion
    of Federer 2.2.12, p. 68: every Suslin set is
    measurable for any measure making all closed sets measurable.
    The finite-test splitting criterion turns the closed inner
    approximants into measurability without assuming it in advance. *)
Theorem suslin_set_measurable (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (S : set X) :
  (forall C : set X, closed C -> measure_measurable mu C) ->
  is_suslin_set R S -> measure_measurable mu S.
Proof.
move=> hc hS; apply: (@measurable_inner_approximation_criterion R X mu hm S)=> T hT delta hd.
have [C [hC [hCS herr]]] := @suslin_closed_inner_approximation R X mu hm S T delta hc hS hT hd.
exists C; split; first exact: hc C hC.
by split.
Qed.
