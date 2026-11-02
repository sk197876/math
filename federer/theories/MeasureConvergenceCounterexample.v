(** Federer (1969), 2.3.8, p. 78: convergence in measure need not imply
    almost-everywhere convergence, even on a finite measure space. Here a
    locally constructed binary-cylinder measure supplies an unconditional
    witness; its total mass, cylinder measurability, the Banach target, and
    both convergence assertions have all been proved. Source context:
    BinaryTypewriter.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP ScalarNormMetricCompleteness
  PartialFunctionUP PartialFunctionBasic PartialFunctionLimitUP MeasureUP MeasureAlmostUP
  MeasurableNormedFunctionUP MeasurableNormedBasic MeasureConvergenceUP
  BinarySequenceCylinders BinaryCylinderEnvelope BinaryTypewriter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convergence_in_measure_not_almost_everywhere]:
    existential counterexample to the false converse in Federer
    2.3.8, p. 78, with a complete normed real target
    and total source measure one. Neither an unconstructed
    non-atomic measure nor an unproved example hypothesis is assumed. *)
Theorem convergence_in_measure_not_almost_everywhere (R : realType) :
  let M := real_norm_metric_space (scalar_absolute_value_norm R) in
  is_complete_metric_space [the metricType R of M] /\
  exists (mu : set binary_sequence_space -> \bar R)
    (f : nat -> partial_function binary_sequence_space M)
    (g : partial_function binary_sequence_space M),
    is_measure mu /\ mu setT = 1 /\
    (forall n, @is_measurable_normed_function R [the choiceType of binary_sequence_space] R^o _
      (scalar_absolute_value_norm R) mu (f n)) /\
    @is_measurable_normed_function R [the choiceType of binary_sequence_space] R^o _
      (scalar_absolute_value_norm R) mu g /\
    @converges_in_measure R [the choiceType of binary_sequence_space] R^o mu (fun y : R => `|y|%R) f g /\
    ~ measure_almost_everywhere mu (partial_function_limit_locus f g).
Proof.
move=> M; split; first exact: scalar_norm_metric_complete.
exists (@binary_cylinder_measure R),
  (fun n => partial_function_total (@binary_typewriter R n)),
  (partial_function_total (fun _ : binary_sequence_space => (0%R : M))).
split; first exact: binary_cylinder_measure_is_measure.
split; first exact: binary_cylinder_measure_whole.
split; first exact: binary_typewriter_measurable_normed.
split.
- exact (@measurable_normed_total_constant R [the choiceType of binary_sequence_space] R^o _
    (scalar_absolute_value_norm R) _ (binary_cylinder_measure_is_measure R) (0%R : M)).
split.
- exact: binary_typewriter_converges_in_measure.
- exact: binary_typewriter_not_almost_zero.
Qed.
