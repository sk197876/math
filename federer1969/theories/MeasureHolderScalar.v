(** Federer (1969), 2.4.14, p. 88: Holder's inequality for the signed real
    product. The theorem below proves the inequality and summability for
    finite conjugate exponents; the equality criterion and infinity
    endpoints require separate statements. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialScalarProduct PartialNormProduct
  PartialAbsolutePartsGraph MeasureHolderNormProduct MeasureLpNorm
  MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence MeasureIntegralAbsolute MeasureAbsoluteSummability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_holder_scalar_finite]: the principal inequality of
    Federer 2.4.14, p. 88 The explicitly supplied finite Lp and Lq values
    may vanish. The conclusion proves product summability and bounds the
    absolute integral value. It does not yet express the equality criterion. *)
Theorem measure_holder_scalar_finite (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q a b : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (1 <= p)%R -> (1 <= q)%R -> (p^-1 + q^-1 = 1)%R ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  measure_lp_norm mu (fun x : R => `|x|%R) p f = a%:E ->
  measure_lp_norm mu (fun x : R => `|x|%R) q g = b%:E ->
  exists c : R, is_measure_integral mu (partial_scalar_product f g) c%:E /\ (`|c| <= a*b)%R.
Proof.
move=> hp hq hpq hf hg hfa hgb.
have [d [hd [hdi hbound]]] := @measure_holder_finite_norms R X R^o R^o
  (fun x : R => `|x|%R) (fun x : R => `|x|%R)
  (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)
  mu hm p q a b f g hp hq hpq hf hg hfa hgb.
have habs : is_measure_integral mu (partial_extended_function_absolute_value (partial_scalar_product f g)) d%:E.
  apply: (@measure_integral_graph_equivalent R X mu _ _ d%:E _ hdi)=> x z.
  exact (iff_sym (partial_scalar_absolute_product_graph f g x z)).
have hmeas := @measurable_scalar_product R X mu hm f g hf hg.
have hs : is_measure_summable mu (partial_extended_function_absolute_value (partial_scalar_product f g)).
  by exists d.
have [c hci] := @measure_absolute_summable_implies_summable R X mu hm _ hmeas hs.
have [e [hei hce]] := @measure_integral_absolute_bound R X mu hm _ c%:E hci.
have he := @measure_integral_unique R X mu _ e d%:E hei habs.
rewrite he abse_EFin lee_fin in hce.
exists c; split=> //; exact: le_trans hce hbound.
Qed.
