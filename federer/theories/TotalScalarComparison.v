(** Federer (1969), 2.5.7, p. 98: the measurable comparison set {u>=v}
    defining the maximum decomposition. This supporting measurability fact
    applies the rational comparison argument from 2.3.2–2.3.3, pp. 73–76,
    through the proved finite embedding. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasurableFunctionUP MeasurablePostcomposition MeasurableTotalBasic MeasurableNumericalComparison BorelFunctionBasic
  ScalarNormExtendedEmbedding TotalScalarLpUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_scalar_measurable_comparison]: the comparison set used
    in Federer 2.5.7, p. 98 Measurability alone suffices. *)
Lemma total_scalar_measurable_comparison (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> R) :
  is_measure_measurable_function mu (total_scalar_function f) ->
  is_measure_measurable_function mu (total_scalar_function g) ->
  measure_measurable mu [set x | (f x <= g x)%R].
Proof.
move=> hf hg.
have emb (u : X -> R) : is_measure_measurable_function mu (total_scalar_function u) ->
    is_measure_measurable_function mu (partial_function_total (fun x => ((u x)%:E : extended_real_line R))).
  move=> hu; exact: (@measurable_total_borel_postcomposition R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] (extended_real_line R)
    mu hm u (fun y => (y%:E : extended_real_line R)) hu
    (continuous_borel_function (@scalar_norm_extended_embedding_continuous R))).
have hh := @measurable_total_extended_comparison R X mu hm
  (fun x => ((f x)%:E : extended_real_line R)) (fun x => ((g x)%:E : extended_real_line R))
  (emb f hf) (emb g hg).
have he : [set x | (f x)%:E <= (g x)%:E]=[set x | (f x <= g x)%R].
  by apply/seteqP; split=> x; rewrite /= lee_fin.
by rewrite he in hh.
Qed.
