(** Federer (1969), proof of 2.5.2, p. 93: comparison of the middle layer
    integral with epsilon times the measure of a level set, using 2.4.4(5)
    and 2.4.5. These supporting adapters retain infinite measures and exact
    total real-valued domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP SummableRealFunctionUP PartialFunctionUP
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralComparison CharacteristicFunctionUP CharacteristicFunctionSealed MeasureFiniteCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_total_pointwise_order_almost]: graph adapter for the
    pointwise layer comparisons in Federer 2.5.2, p. 93 *)
Lemma real_total_pointwise_order_almost (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> R) :
  function_le f g -> measure_almost_everywhere mu
    (partial_extended_le_locus (real_total_integrand f) (real_total_integrand g)).
Proof.
move=> hfg; apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
exists (f x)%:E,(g x)%:E; split; first by apply/real_total_integrand_graph.
split; first by apply/real_total_integrand_graph.
by rewrite lee_fin; exact: hfg.
Qed.

(** Source for [real_total_nonnegative_almost]: graph adapter for the
    nonnegative layers in Federer 2.5.2, p. 93 *)
Lemma real_total_nonnegative_almost (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) :
  function_nonnegative f -> measure_almost_everywhere mu
    (partial_extended_nonnegative_locus (real_total_integrand f)).
Proof.
move=> hf; apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
exists (f x)%:E; split; first by apply/real_total_integrand_graph.
by rewrite lee_fin; exact: hf.
Qed.

(** Source for [real_total_integral_supported_upper_bound]: middle layer
    bounded above by a weighted characteristic function in Federer 2.5.2, p.
    93 No finiteness of the set's measure is assumed. *)
Lemma real_total_integral_supported_upper_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (S : set X)
    (f : X -> R) (a : \bar R) (c : R) :
  measure_measurable mu S -> (0 < c)%R -> is_measure_integral mu (real_total_integrand f) a ->
  (forall x, S x -> (f x <= c)%R) -> (forall x, ~ S x -> f x=0%R) -> a <= c%:E * mu S.
Proof.
move=> hS hc hi hon hoff.
pose s := @CharacteristicFunction.value R X S.
have hs := @CharacteristicFunction.laws R X S.
have hchar := @measure_positive_characteristic_integral R X mu hm S s c hs hS hc.
apply: (@measure_integral_monotone R X mu hm _ _ a (c%:E * mu S) hi hchar).
apply: (@real_total_pointwise_order_almost R X mu hm f (fun x => (c*s x)%R))=> x.
case: (pselect (S x))=> hx.
- by rewrite /s (characteristic_on_set hs hx) mulr1; exact: hon.
- by rewrite /s (characteristic_off_set hs hx) (hoff x hx) mulr0.
Qed.

(** Source for [real_total_integral_level_lower_bound]: middle layer bounded
    below by a weighted characteristic function in Federer 2.5.2, p. 93
    Nonnegativity is needed outside the chosen level set. *)
Lemma real_total_integral_level_lower_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (S : set X)
    (f : X -> R) (a : \bar R) (c : R) :
  measure_measurable mu S -> (0 < c)%R -> is_measure_integral mu (real_total_integrand f) a ->
  function_nonnegative f -> (forall x, S x -> (c <= f x)%R) -> c%:E * mu S <= a.
Proof.
move=> hS hc hi hp hon.
pose s := @CharacteristicFunction.value R X S.
have hs := @CharacteristicFunction.laws R X S.
have hchar := @measure_positive_characteristic_integral R X mu hm S s c hs hS hc.
apply: (@measure_integral_monotone R X mu hm _ _ (c%:E * mu S) a hchar hi).
apply: (@real_total_pointwise_order_almost R X mu hm (fun x => (c*s x)%R) f)=> x.
case: (pselect (S x))=> hx.
- by rewrite /s (characteristic_on_set hs hx) mulr1; exact: hon.
- by rewrite /s (characteristic_off_set hs hx) mulr0; exact: hp.
Qed.
