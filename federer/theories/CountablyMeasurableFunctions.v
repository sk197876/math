(** Federer (1969), 2.3.4, p. 76: consequences for functions, including the
    zero function and a countably measurable source. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic MeasureUP MeasurableFunctionUP
  MeasurableFunctionBorel MeasurableTotalBasic TopologicalBorel CountablyMeasurableUP
  CountablyMeasurableBasic CountablyMeasurableSubsets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [total_zero_function_nonzero_locus]: supporting
    empty nonzero locus of the zero function in Federer 2.3.4,
    p. 76. No separation hypothesis on the target is needed. *)
Lemma total_zero_function_nonzero_locus (X Y : Type) (zero : Y) :
  partial_function_nonzero_locus zero (partial_function_total (fun _ : X => zero)) = set0.
Proof.
apply/seteqP; split=> x; last by [].
by move=> [y [<- hn]]; apply: hn.
Qed.

(** Source for [countably_measurable_zero_function]: supporting
    zero-function case of Federer 2.3.4, p. 76 The source need not have
    finite or countably finite measure. *)
Lemma countably_measurable_zero_function (R : realType) (X : choiceType) (Y : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (zero : Y) :
  is_countably_measure_measurable_function mu zero (partial_function_total (fun _ : X => zero)).
Proof.
constructor.
- exact: (@measurable_total_constant R X Y mu hm zero).
- rewrite total_zero_function_nonzero_locus; exact: empty_set_countably_measurable.
Qed.

(** Source for [measurable_function_nonzero_locus]: supporting
    measurability of the nonzero locus used in Federer 2.3.4,
    p. 76, by 2.3.2(1), p. 73. Closedness of zero
    is explicit for the general pointed target; it holds in Hausdorff
    topological vector spaces, in particular the later Banach targets. *)
Lemma measurable_function_nonzero_locus (R : realType) (X : choiceType) (Y : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (zero : Y) (f : partial_function X Y) :
  closed [set y | y = zero] -> is_measure_measurable_function mu f ->
  measure_measurable mu (partial_function_nonzero_locus zero f).
Proof.
move=> hz hf; apply: (@measurable_function_borel_preimage R X Y mu hm f hf).
exact: borel_set_complement (closed_borel_set hz).
Qed.

(** Source for [countably_measurable_function_on_countable_source]:
    supporting source restriction consequence of Federer 2.3.4,
    p. 76. A measurable function with closed distinguished zero
    is countably measurable when the whole source is countably measurable. *)
Lemma countably_measurable_function_on_countable_source (R : realType)
    (X : choiceType) (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (zero : Y) (f : partial_function X Y) :
  closed [set y | y = zero] -> measure_countably_measurable mu setT ->
  is_measure_measurable_function mu f -> is_countably_measure_measurable_function mu zero f.
Proof.
move=> hz hX hf; constructor=> //.
apply: (@measurable_subset_countably_measurable R X mu hm _ setT _ _ hX).
- exact: (@measurable_function_nonzero_locus R X Y mu hm zero f hz hf).
- by move=> x _.
Qed.
