(** Characteristic functions in the space of Federer (1969), 2.3.8, p. 78.
    Source context: MeasurableNormedFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP CharacteristicFunctionUP
  CharacteristicVectorPiece MeasurableNormedFunctionUP MeasurableNormedBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_normed_characteristic]: a measurable set's
    characteristic function belongs to A(mu,R), supporting Federer 2.3.8, p.
    78 The characteristic map is supplied through its laws. *)
Lemma measurable_normed_characteristic (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) (s : X -> R) :
  is_characteristic_function A s -> measure_measurable mu A ->
  @is_measurable_normed_function R X R^o _ (scalar_absolute_value_norm R) mu (partial_function_total s).
Proof.
move=> hs hA.
pose M := real_norm_metric_space (scalar_absolute_value_norm R).
have hc := @measurable_normed_total_constant R X R^o _ (scalar_absolute_value_norm R) mu hm (1%R : M).
have hp := @measurable_normed_characteristic_piece R X R^o _ (scalar_absolute_value_norm R)
  mu hm A s (fun _ => (1%R : M)) hs hA hc.
have he : characteristic_vector_piece s (fun _ : X => (1%R : M)) = s.
  apply: funext=> x; change ((s x * 1)%R = s x); by rewrite mulr1.
by rewrite he in hp.
Qed.
