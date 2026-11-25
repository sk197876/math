(** Federer (1969), 2.6.4, p. 118: supporting conversion from scalar L1
    functions to the extended-real integral convention. The countably
    measurable nonzero locus is unchanged. The definitions are 2.3.4, p. 76,
    and 2.4.12, p. 86. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionBasic PartialFunctionPreimages MeasureUP MeasurableFunctionUP MeasurableGraphEquivalence
  CountablyMeasurableUP TotalScalarLpUP TotalScalarMeasurability MeasurableRealEmbedding SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_real_integrand_measurable]: supporting
    finite embedding of the total-domain product in Federer
    2.6.4, p. 118. Function values and domains are unchanged. *)
Lemma scalar_real_integrand_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) :
  is_measure_measurable_function mu (total_scalar_function f) ->
  is_measure_measurable_function mu (real_total_integrand f).
Proof.
move=> hf.
have hi := measurable_total_real_embedding hm (total_scalar_real_measurable hm hf).
apply: (@measurable_function_graph_equivalent R X (extended_real_line R) mu _ _ _ hi)=> x z.
by rewrite real_total_integrand_graph.
Qed.

(** Source for [scalar_real_integrand_nonzero_locus]: supporting
    exact nonzero-locus preservation for Federer 2.6.4, p. 118,
    under the definition in 2.3.4, p. 76. *)
Lemma scalar_real_integrand_nonzero_locus (R : realType) (X : Type) (f : X -> R) :
  partial_function_nonzero_locus (0%E : extended_real_line R) (real_total_integrand f) =
  partial_function_nonzero_locus (0 : real_norm_metric_space (scalar_absolute_value_norm R))
    (total_scalar_function f).
Proof.
rewrite /partial_function_nonzero_locus /total_scalar_function partial_function_total_preimage.
apply/seteqP; split=> x.
- move=> [z [hz hn]] he; apply: hn; move: hz; rewrite real_total_integrand_graph he; by move=> <-.
- move=> hn; exists (f x)%:E; split; first by apply/real_total_integrand_graph.
  move=> he; apply: hn; exact: EFin_inj he.
Qed.

(** Source for [scalar_real_integrand_countably_measurable]:
    supporting countable measurability needed by the Fubini step
    in Federer 2.6.4, p. 118. No ambient sigma-finiteness
    is introduced by the finite embedding. *)
Lemma scalar_real_integrand_countably_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) :
  is_countably_measure_measurable_function mu
    (0 : real_norm_metric_space (scalar_absolute_value_norm R)) (total_scalar_function f) ->
  is_countably_measure_measurable_function mu (0%E : extended_real_line R) (real_total_integrand f).
Proof.
move=> hf; constructor.
- exact (@scalar_real_integrand_measurable R X mu hm f (countably_measurable_function_measurable hf)).
- rewrite scalar_real_integrand_nonzero_locus; exact: countably_measurable_function_locus hf.
Qed.
