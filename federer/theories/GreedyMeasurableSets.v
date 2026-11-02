(** Federer (1969), 2.3.3, p. 76: measurability of the inductively selected
    sets and partial sums. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasurableFunctionUP GreedyScalarExpansionUP MeasurableTotalBasic
  MeasurableTotalPiecewise MeasurableTotalRealAddition MeasurableRealEmbedding MeasurableNumericalComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [greedy_expansion_set]: supporting threshold
    set in the inductive formula of Federer 2.3.3, p. 76.
    The partial sum s is arbitrary until its recursion laws are assumed. *)
Definition greedy_expansion_set (R : realType) (X : Type)
    (r : nat -> R) (f : X -> \bar R) (s : nat -> X -> R) n : set X :=
  [set x | (s n x + r n)%R%:E <= f x].

(** Source for [greedy_expansion_set_measurable]: supporting
    measurable-comparison step for Federer 2.3.3, p. 76 *)
Lemma greedy_expansion_set_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (r : nat -> R)
    (f : X -> extended_real_line R) (s : nat -> X -> real_line_metric R) n :
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total (s n)) ->
  measure_measurable mu (greedy_expansion_set r f s n).
Proof.
move=> hf hs; apply: (@measurable_total_extended_comparison R X mu hm _ f _ hf).
apply: (@measurable_total_real_embedding R X mu hm).
apply: (@measurable_total_real_add R X mu hm _ _ hs).
exact (@measurable_total_constant R X [the topologicalType of real_line_metric R] mu hm (r n)).
Qed.

(** Source for [greedy_partial_sums_measurable]: direct induction behind the
    measurable sets in Federer 2.3.3, p. 76. Only the abstract scalar
    recursion is used, independently of its implementation. *)
Lemma greedy_partial_sums_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (r : nat -> R)
    (f : X -> extended_real_line R) (s : nat -> X -> real_line_metric R) :
  is_measure_measurable_function mu (partial_function_total f) ->
  (forall x, is_greedy_scalar_expansion r (f x) (fun n => s n x)) ->
  forall n, is_measure_measurable_function mu (partial_function_total (s n)).
Proof.
move=> hf hs; elim=> [|n IH].
- have he : s 0%N = (fun _ : X => (0%R : real_line_metric R)).
    apply: funext=> x; exact: greedy_scalar_initial (hs x).
  rewrite he; exact (@measurable_total_constant R X [the topologicalType of real_line_metric R] mu hm 0%R).
- have hA := @greedy_expansion_set_measurable R X mu hm r f s n hf IH.
  have hsum := @measurable_total_real_add R X mu hm (s n)
    (fun _ : X => (r n : real_line_metric R)) IH
    (@measurable_total_constant R X [the topologicalType of real_line_metric R] mu hm (r n)).
  have he : s n.+1 = (fun x => if pselect (greedy_expansion_set r f s n x)
      then (s n x+r n)%R else s n x).
    apply: funext=> x; rewrite (greedy_scalar_step (hs x)).
    case: (pselect (greedy_expansion_set r f s n x))=> hA'.
    + have hc : (s n x+r n)%R%:E <= f x := hA'.
      by rewrite hc.
    + have hc : ~~ ((s n x+r n)%R%:E <= f x) by apply/negP; exact hA'.
      by rewrite (negPf hc).
  rewrite he; exact: (@measurable_total_piecewise R X [the topologicalType of real_line_metric R]
    mu hm _ _ _ hA hsum IH).
Qed.

(** Source for [greedy_all_sets_measurable]: the measurable-set clause of
    Federer 2.3.3, p. 76, for every abstract pointwise greedy partial-sum
    family *)
Theorem greedy_all_sets_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (r : nat -> R)
    (f : X -> extended_real_line R) (s : nat -> X -> real_line_metric R) :
  is_measure_measurable_function mu (partial_function_total f) ->
  (forall x, is_greedy_scalar_expansion r (f x) (fun n => s n x)) ->
  forall n, measure_measurable mu (greedy_expansion_set r f s n).
Proof.
move=> hf hs n; exact: (@greedy_expansion_set_measurable R X mu hm r f s n hf
  (@greedy_partial_sums_measurable R X mu hm r f s hf hs n)).
Qed.
