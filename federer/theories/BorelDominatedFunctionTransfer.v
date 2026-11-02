(** Federer (1969), 2.5.10, p. 101: passing summable functions from H^1 to
    the dominated projected counting measure. This supporting measurability
    lemma retains the countably measurable nonzero-locus condition of 2.3.4,
    p. 76. It uses the finite Borel sandwich in 2.2.3, p. 61, and its
    countable extension. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPreimages
  MeasureUP MeasureFiniteClosure MeasureAlmostUP MeasurableFunctionUP MeasurableFunctionBorel
  BorelRegularMeasureUP TopologicalBorel CountablyMeasurableUP CountablyMeasurableBasic
  CountablyMeasurableSubsets BorelDominatedMeasureTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_dominated_function_measurable]: supporting
    transfer for the functional in Federer 2.5.10,
    p. 101. No global sigma-finiteness is assumed:
    preimages avoiding zero lie in the countably measurable
    nonzero locus; the other preimages use complements
    inside the conull domain. Partial domains are retained. *)
Lemma borel_dominated_function_measurable (R : realType)
    (X Y : topologicalType) (mu nu : set X -> \bar R)
    (hm : is_measure mu) (hn : is_measure nu) (hr : is_borel_regular_measure mu)
    (zero : Y) (f : partial_function X Y) :
  (forall B, borel_set B -> measure_measurable nu B) ->
  (forall B, nu B<=mu B) ->
  is_countably_measure_measurable_function mu zero f ->
  is_countably_measure_measurable_function nu zero f.
Proof.
move=> hb hd [hf hs].
have hdom : measure_almost_everywhere nu (partial_function_domain f).
  exact (@dominated_measure_null R X mu nu hn hd _ (measurable_function_domain hf)).
have hsmall : forall B : set Y, borel_set B -> ~ B zero ->
    measure_measurable nu (partial_function_preimage f B).
  move=> B hB hz.
  have hc : measure_countably_measurable mu (partial_function_preimage f B).
    apply: (@measurable_subset_countably_measurable R X mu hm _
      (partial_function_nonzero_locus zero f)
      (@measurable_function_borel_preimage R X Y mu hm f hf B hB) _ hs).
    move=> x [y [hy hBy]]; exists y; split=> //.
    by move=> ey; apply: hz; rewrite -ey.
  apply: (countably_measurable_set_measurable hn).
  exact (@borel_dominated_countably_measurable R X mu nu hm hn hr hb hd _ hc).
constructor.
- constructor=> // U hU.
  case: (pselect (U zero))=> hz.
  + rewrite -[U]setCK partial_function_preimage_complement.
    apply: (@measure_measurable_difference R X nu hn).
    * exact (@conull_partial_function_domain_measurable R X Y nu hn f hdom).
    * apply: hsmall; first exact: borel_set_complement (open_borel_set hU).
      by move=> h; exact: h hz.
  + exact: hsmall (open_borel_set hU) hz.
- exact (@borel_dominated_countably_measurable R X mu nu hm hn hr hb hd _ hs).
Qed.
