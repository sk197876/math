(** Federer (1969), 2.4.6, p. 84: Fatou's lemma. The proof here follows that
    reduction, the increasing tail sets, continuity of measures, and the
    final scalar squeeze. Partial domains and infinite integral values are
    preserved. We allow nonnegativity almost everywhere, a null-set
    extension of Federer's printed hypothesis. The limit is specified by its
    abstract laws on the eventual common domain, which contains the conull
    common domain used in the proof. No relevant correction occurs in the
    local erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionLimitExtremaUP
  PartialFunctionLowerLimitSealed MeasureUP MeasureAlmostUP MeasurableFunctionUP
  PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralBounds MeasureNonnegativeIntegral
  MeasureLowerLimitNonnegative ExtendedLowerLimit MeasureFatouLowerStep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_fatou_integral_values]: direct inequality
    of Federer 2.4.6, p. 84, with integral values and
    the pointwise lower limit specified abstractly. *)
Theorem measure_fatou_integral_values (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) (a : nat -> \bar R) b :
  is_partial_function_lower_limit f g ->
  (forall n, measure_almost_everywhere mu (partial_extended_nonnegative_locus (f n))) ->
  (forall n, is_measure_integral mu (f n) (a n)) ->
  is_measure_integral mu g b -> b <= extended_lower_limit a.
Proof.
move=> hg hp hi hgi; apply: hgi.2.2.2=> c [u [hu hc]].
exact (@measure_fatou_lower_step_bound R X mu hm f g a u c hg hp hi hu hc).
Qed.

(** Source for [measure_fatou]: complete Federer 2.4.6,
    p. 84, including integrability of the lower-limit function
    from 2.4.4(2); no finite-integral hypothesis is imposed. *)
Theorem measure_fatou (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  is_partial_function_lower_limit f g ->
  (forall n, is_measure_measurable_function mu (f n)) ->
  (forall n, measure_almost_everywhere mu (partial_extended_nonnegative_locus (f n))) ->
  is_measure_integral mu g (measure_lower_integral mu g) /\
  measure_lower_integral mu g <= extended_lower_limit (fun n => measure_lower_integral mu (f n)).
Proof.
move=> hg hf hp.
have hgi := (@measure_lower_limit_nonnegative_integral R X mu hm f g hg hf hp).1.
split=> //; apply: (@measure_fatou_integral_values R X mu hm f g
  (fun n => measure_lower_integral mu (f n)) _ hg hp _ hgi)=> n.
exact (@nonnegative_measurable_function_integral R X mu hm (f n) (hf n) (hp n)).1.
Qed.

(** Source for [measure_sealed_lower_limit_fatou]: usable sealed
    lower-limit instance of Federer 2.4.6, p. 84;
    the proof uses only the lower-limit interface. *)
Corollary measure_sealed_lower_limit_fatou (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R)) :
  (forall n, is_measure_measurable_function mu (f n)) ->
  (forall n, measure_almost_everywhere mu (partial_extended_nonnegative_locus (f n))) ->
  is_measure_integral mu (@PartialFunctionLowerLimit.value R X f)
    (measure_lower_integral mu (@PartialFunctionLowerLimit.value R X f)) /\
  measure_lower_integral mu (@PartialFunctionLowerLimit.value R X f) <=
    extended_lower_limit (fun n => measure_lower_integral mu (f n)).
Proof.
exact (@measure_fatou R X mu hm f _ (@PartialFunctionLowerLimit.laws R X f)).
Qed.
