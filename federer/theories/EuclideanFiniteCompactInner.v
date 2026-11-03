(** Federer (1969), 3.2.41, printed p. 278: pass from
    compact sets to measurable sets by compact inner approximation.
    Actual finite-measure Lebesgue sets use the earlier Radon
    approximation theorem of 2.2.5, p. 63. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueCompactInner RadonFiniteInnerRegularity MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_finite_measurable_compact_inner_strict]:
    supporting compact inner step in Federer 3.2.41, p. 278.
    Any finite measurable original set contains a compact subset
    whose actual mass exceeds a prescribed strict lower threshold.
    No Borel or bounded-source hypothesis is added. *)
Lemma euclidean_finite_measurable_compact_inner_strict (R:realType) n
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (q:R):
  measure_measurable (@euclidean_lebesgue_measure R n) A ->
  (@euclidean_lebesgue_measure R n A < +oo)%E ->
  (q%:E<@euclidean_lebesgue_measure R n A)%E ->
  exists K,compact K /\K `<=` A /\(q%:E<@euclidean_lebesgue_measure R n K)%E.
Proof.
move=> hA hFinite hBelow.
apply:contrapT=> hNone.
have hUpper:(@euclidean_lebesgue_measure R n A<=q%:E)%E.
  apply:(@radon_finite_measurable_inner_least R
    (inner_metric_space (@euclidean_inner_productP R n))
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
    (euclidean_lebesgue_radon R n) A q%:E hA hFinite)=> K hK hKA.
  rewrite leNgt; apply/negP=> hQK; apply:hNone; exists K; split=>//; by split.
have hBad:=lt_le_trans hBelow hUpper; by rewrite ltxx in hBad.
Qed.
