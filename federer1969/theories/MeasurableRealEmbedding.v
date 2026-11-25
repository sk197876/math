(** Federer (1969), 2.3.3, p. 76: finite real partial sums are regarded as
    extended-real measurable functions when compared with a possibly
    infinite target. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology ereal ereal_normedtype.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedArithmeticContinuity
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasurableTotalBasic BorelFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

(** Source for [real_extended_embedding_continuous]: scalar topological
    inclusion supporting Federer 2.3.3, p. 76 The explicit neighborhood
    adapter identifies the native finite neighborhoods with the order
    topology. *)
Lemma real_extended_embedding_continuous (R : realType) :
  continuous (fun x : real_line_metric R => (x%:E : extended_real_line R)).
Proof.
move=> x; change (@cvg_to _ (fmap (fun r : real_line_metric R => r%:E) (nbhs x))
  (@nbhs _ (extended_real_line R) x%:E)).
rewrite extended_real_native_neighborhoods; by [].
Qed.

(** Source for [measurable_total_real_embedding]: supporting
    measurable inclusion of the real partial sums into the extended
    real line in Federer 2.3.3, p. 76. *)
Lemma measurable_total_real_embedding (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> real_line_metric R) :
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total (fun x => ((f x)%:E : extended_real_line R))).
Proof.
move=> hf; apply: (@measurable_total_borel_postcomposition R X _ _ mu hm _ _ hf).
apply: continuous_borel_function; exact: real_extended_embedding_continuous.
Qed.
