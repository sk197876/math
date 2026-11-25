(** Federer (1969), 2.4.19, p. 91: measurable cutoffs in the
    sublevel-exhaustion argument This supporting closure property retains
    the essential separability required in Federer's A(phi,Y), 2.3.8, p. 78. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostBasic MeasurableNormedFunctionUP MeasurableTotalPiecewise EssentialSeparableEnvelope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_normed_total_piecewise]: supporting closure of
    A(phi,Y) under measurable pasting for Federer 2.4.19, p. 91 The same
    separable linear envelope contains both branches. *)
Lemma measurable_normed_total_piecewise (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (f g : X -> real_norm_metric_space hN) :
  measure_measurable mu A ->
  is_measurable_normed_function mu (partial_function_total f) ->
  is_measurable_normed_function mu (partial_function_total g) ->
  is_measurable_normed_function mu (partial_function_total (fun x => if pselect (A x) then f x else g x)).
Proof.
move=> hA hf hg; split; first exact: measurable_total_piecewise hA hf.1 hg.1.
have [Z [hc [hd [hZf hZg]]]] := @essential_separable_pair_envelope R X V N hN mu hm
  (partial_function_total f) (partial_function_total g) hf.2 hg.2.
exists Z; split=> //.
apply: (@measure_null_subset R X mu hm _ _ _ (@measure_null_union R X mu hm _ _ hZf hZg)).
move=> x [y [hy hn]]; have hy' : (if pselect (A x) then f x else g x)=y := hy.
case: (pselect (A x)) hy'=> hx hy'.
- left; exists y; by split.
- right; exists y; by split.
Qed.
