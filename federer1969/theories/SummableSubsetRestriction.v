(** Federer (1969), 2.9.25, p. 169: restrict the summable joint function and
    its summable inner integral to prefix intervals. This supporting
    consequence of the subset convention in 2.4.10, p. 85, uses absolute
    domination by the original summable function. The local Federer erratum
    has no entry for this step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  PartialAbsolutePartsGraph PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableZeroExtension MeasureIntegralUP MeasureIntegralAbsolute
  MeasureAbsoluteSummability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [summable_measurable_zero_extension]: supporting
    summability after a measurable restriction in Federer 2.9.25,
    p. 169, by 2.4.9–2.4.10, p. 85. The
    integrand can be partial, signed and infinite on a null
    exceptional set; no finiteness of the ambient measure is used. *)
Lemma summable_measurable_zero_extension (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (f : partial_function X (extended_real_line R)) :
  measure_measurable mu A -> is_measure_summable mu f ->
  is_measure_summable mu (partial_function_zero_extension (0 : extended_real_line R) A f).
Proof.
move=> hA hf; have [a hi] := hf.
have hgm := @measurable_zero_extension R X (extended_real_line R) mu hm 0 A f hA hi.1.
have hAbs := @measure_summable_absolute_value R X mu hm f hf.
have hdom : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_absolute_value (partial_function_zero_extension (0 : extended_real_line R) A f))
    (partial_extended_function_absolute_value f)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hi.1))=> x [z hz].
  case: (pselect (A x))=> hx.
  - exists `|z|,`|z|; split.
    + exists z; split; last by [].
      exact: (partial_function_zero_extension_on _ _ _ hx).2 hz.
    + split; first by exists z; split.
      exact: lexx.
  - exists 0,`|z|; split.
    + exists 0; split; last exact: abse0.
      by apply/(partial_function_zero_extension_off _ _ _ hx).
    + split; first by exists z; split.
      exact: abse_ge0.
exact: (@measure_dominated_summable R X mu hm _ _ hgm hAbs hdom).1.
Qed.
