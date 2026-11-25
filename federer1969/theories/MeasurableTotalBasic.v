(** Federer (1969), 2.3.3, p. 76: elementary total-map bookkeeping for the
    measurable greedy partial sums, using 2.3.2(4), p. 73. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  PartialFunctionPostcomposition MeasureUP MeasureSplit MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurablePostcomposition MeasurableGraphEquivalence BorelFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [measurable_total_constant]: supporting initial zero function
    and constant weights in the recursion of Federer 2.3.3, p. 76 *)
Lemma measurable_total_constant (R : realType) (X : choiceType) (Y : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : Y) :
  is_measure_measurable_function mu (partial_function_total (fun _ : X => c)).
Proof.
constructor.
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
- move=> U ho; rewrite partial_function_total_preimage.
  case: (pselect (U c))=> hc.
  + have he : (fun _ : X => c) @^-1` U = setT by apply/seteqP; split=> x // _.
    rewrite he; exact: measure_measurable_whole hm.
  + have he : (fun _ : X => c) @^-1` U = set0 by apply/seteqP; split=> x // hx; exact: hc hx.
    rewrite he; exact: measure_measurable_empty hm.
Qed.

(** Source for [measurable_total_borel_postcomposition]: supporting
    total-map form of Federer 2.3.2(4), p. 73, used
    for the partial-sum induction in 2.3.3, p. 76. *)
Lemma measurable_total_borel_postcomposition (R : realType) (X : choiceType)
    (Y Z : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> Y) (g : Y -> Z) :
  is_measure_measurable_function mu (partial_function_total f) -> is_borel_function g ->
  is_measure_measurable_function mu (partial_function_total (fun x => g (f x))).
Proof.
move=> hf hg; apply: (@measurable_function_graph_equivalent R X Z mu
  (partial_function_postcompose (partial_function_total f) g)).
- move=> x z; split.
  + by move=> [y [<- he]].
  + by move=> he; exists (f x).
- exact: (@measurable_function_borel_postcomposition R X Y Z mu hm _ g hf hg).
Qed.
