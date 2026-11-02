(** Federer (1969), 2.4.4(1), p. 82: a step function is integrable and its
    integral is its assigned numerical sum. The inclusion of real into
    extended real values is explicit but preserves the partial domain.
    Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurablePostcomposition
  MeasurableRealEmbedding BorelFunctionBasic MeasureStepFunctionUP MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralSqueeze MeasureIntegralUniqueness MeasureIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_real_function_embed]: explicit real-to-
    extended-real inclusion for step functions in Federer 2.4.4(1),
    p. 82, with their partial graphs preserved. *)
Definition partial_real_function_embed (R : realType) (X : Type)
    (u : partial_function X (real_line_metric R)) :=
  partial_function_postcompose u (fun y => (y%:E : extended_real_line R)).

(** Source for [measurable_partial_real_embedding]: supporting
    measurability of the same function with the extended-real
    target in Federer 2.4.4(1), p. 82. *)
Lemma measurable_partial_real_embedding (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : partial_function X (real_line_metric R)) :
  is_measure_measurable_function mu u ->
  is_measure_measurable_function mu (partial_real_function_embed u).
Proof.
move=> hu; apply: (@measurable_function_borel_postcomposition R X _ _ mu hm u _ hu).
apply: continuous_borel_function; exact: real_extended_embedding_continuous.
Qed.

(** Source for [step_function_self_upper_lower]: the observation
    starting Federer's proof of 2.4.4(1), p. 82: a
    step function is both an upper and lower function for itself. *)
Lemma step_function_self_upper_lower (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : partial_function X (real_line_metric R)) :
  is_measure_step_function mu u ->
  is_measure_upper_function mu (partial_real_function_embed u) u /\
  is_measure_lower_function mu (partial_real_function_embed u) u.
Proof.
move=> hu; have hd := measurable_function_domain (step_function_measurable hu).
split; split=> //.
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hd)=> x [y hy].
  exists y,y%:E; split=> //; split; last exact: lexx.
  exists y; by split.
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hd)=> x [y hy].
  exists y,y%:E; split=> //; split; last exact: lexx.
  exists y; by split.
Qed.

(** Source for [measure_step_function_integral]: direct Federer
    2.4.4(1), p. 82; it includes integrability and the
    assigned-sum formula, with infinite sums allowed. *)
Theorem measure_step_function_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : partial_function X (real_line_metric R)) a :
  is_measure_step_function mu u -> is_measure_step_integral mu u a ->
  is_measure_integral mu (partial_real_function_embed u) a.
Proof.
move=> hu ha; have [hup hlo] := @step_function_self_upper_lower R X mu hm u hu.
apply: (@measure_integral_squeeze R X mu hm _ a).
- exact (@measurable_partial_real_embedding R X mu hm u (step_function_measurable hu)).
- exact: measure_upper_integral_bound hup ha.
- exact: measure_lower_integral_bound hlo ha.
Qed.

(** Source for [measure_step_integral_value]: public integral
    value form of Federer 2.4.4(1), p. 82, independent
    of the chosen proof of integrability. *)
Lemma measure_step_integral_value (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : partial_function X (real_line_metric R)) a
    (hi : is_measure_integrable mu (partial_real_function_embed u)) :
  is_measure_step_function mu u -> is_measure_step_integral mu u a -> measure_integral hi = a.
Proof.
move=> hu ha; exact: measure_integral_unique (measure_integral_specification hi)
  (@measure_step_function_integral R X mu hm u a hu ha).
Qed.
