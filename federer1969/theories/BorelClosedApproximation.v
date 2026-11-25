(** Federer (1969), 2.2.2(1), pp. 60-61: finite-measure Borel sets admit
    closed inner approximation in a metric space whose open sets are
    measurable. Restricting to the target set makes the whole measure finite
    without changing the relevant differences. Source context:
    ClosedApproximationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology pseudometric_structure.
From Federer Require Import MeasureUP MeasureRestriction MeasureRestrictionSupport
  TopologicalBorel MeasurableBorelFamily MetricBorelGeneration ClosedApproximationUP
  ClosedApproximationFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_borel_closed_approximation]: Federer
    2.2.2(1), pp. 60-61, direct statement using the abstract
    approximation predicate: every positive tolerance has a closed
    subset C of B with mu(B minus C) below that tolerance. Only
    the measure of B, not of the whole space, is assumed finite. *)
Theorem metric_borel_closed_approximation (R : realType) (T : pseudoMetricType R)
    (mu : set T -> \bar R) (hm : is_measure mu) (B : set T) :
  (forall U, open U -> measure_measurable mu U) ->
  borel_set B -> mu B < +oo -> is_closed_approximable mu B.
Proof.
move=> ho hB hf; pose nu := measure_restrict mu B.
have hn : is_measure nu := measure_restrict_is_measure hm B.
have hnf : nu setT < +oo by rewrite /nu /measure_restrict setIT.
have hc K : closed K -> measure_measurable nu K.
  move=> hK; apply: (@measure_restrict_measurable R _ mu B K).
  apply: (@open_measurable_implies_borel_measurable R T mu hm ho K).
  exact: closed_borel_set hK.
have happ := @finite_measure_borel_closed_approximable R T nu hn
  (@metric_has_closed_sequence_covers R T) hnf hc B hB.
move=> epsilon he; have [C [hC [hCB herror]]] := happ epsilon he.
exists C; split=> //; split=> //.
have hsub : B `\` C `<=` B by move=> x [hx _].
by rewrite /nu (@measure_restrict_subset_value R _ mu B (B `\` C) hsub) in herror.
Qed.
