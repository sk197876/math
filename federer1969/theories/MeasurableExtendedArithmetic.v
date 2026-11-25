(** Federer (1969), 2.3.2, p. 74: arithmetic closure for extended-real
    measurable functions, when the resulting operation has conull domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology MeasureUP MeasureAlmostUP
  MeasurableFunctionUP MeasurableExtendedPairs MeasurableExtendedParts
  PartialExtendedArithmetic MeasurablePartialBinaryOperation ExtendedArithmeticDomains
  ExtendedArithmeticContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_extended_function_add]: direct sum assertion of
    Federer 2.3.2, p. 74 *)
Theorem measurable_extended_function_add (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_almost_everywhere mu (partial_function_domain (partial_extended_function_add f g)) ->
  is_measure_measurable_function mu (partial_extended_function_add f g).
Proof.
move=> hf hg hd; apply: (@measurable_partial_binary_operation R X
  (extended_real_line R) (extended_real_line R) (extended_real_line R) mu hm f g _ _ 0 _ _ _ hd).
- exact (@measurable_extended_function_pair R X mu hm f g hf hg).
- exact: extended_add_domain_borel.
- move=> p hp; exact: extended_add_continuous_at_defined hp.
Qed.

(** Source for [measurable_extended_function_multiply]: direct product
    assertion of Federer 2.3.2, p. 74 The conull-domain hypothesis is for
    the ordinary partial product, including its zero/infinity exclusions. *)
Theorem measurable_extended_function_multiply (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_almost_everywhere mu (partial_function_domain (partial_extended_function_multiply f g)) ->
  is_measure_measurable_function mu (partial_extended_function_multiply f g).
Proof.
move=> hf hg hd; apply: (@measurable_partial_binary_operation R X
  (extended_real_line R) (extended_real_line R) (extended_real_line R) mu hm f g _ _ 0 _ _ _ hd).
- exact (@measurable_extended_function_pair R X mu hm f g hf hg).
- exact: extended_multiply_domain_borel.
- move=> p hp; exact: extended_multiply_continuous_at_defined hp.
Qed.

(** Source for [measurable_extended_function_subtract]: direct difference
    assertion of Federer 2.3.2, p. 74, obtained by addition and negation. *)
Theorem measurable_extended_function_subtract (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_almost_everywhere mu (partial_function_domain (partial_extended_function_subtract f g)) ->
  is_measure_measurable_function mu (partial_extended_function_subtract f g).
Proof.
move=> hf hg hd; apply: (@measurable_extended_function_add R X mu hm f _ hf _ hd).
exact (@measurable_extended_negation R X mu hm g hg).
Qed.
