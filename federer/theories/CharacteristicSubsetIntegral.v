(** Characteristic subset integrals in Federer (1969), 2.9.11, p. 158: apply
    2.9.8 to the characteristic function of a measurable hull. The
    calculation uses 2.4.5, p. 83, and the subset convention of 2.4.10, p.
    85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  PartialZeroExtension MeasureUP MeasureFiniteClosure MeasureSubsetIntegral MeasureIntegralUP
  MeasureIntegralGraphEquivalence SummableRealFunctionUP CharacteristicFunctionUP
  CharacteristicFunctionSealed MeasureCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [characteristic_subset_integral]: supporting identity
    integral_S chi_B=phi(S intersection B) for Federer 2.9.11, p. 158 The
    two sets are measurable but their measures may be infinite. The
    characteristic function is given solely by its abstract laws. *)
Lemma characteristic_subset_integral (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (S B : set X) (s : X -> R) :
  is_measure phi -> measure_measurable phi S -> measure_measurable phi B ->
  is_characteristic_function B s ->
  is_measure_subset_integral phi S (real_total_integrand s) (phi (S `&` B)).
Proof.
move=> hm hS hB hs.
pose t := @CharacteristicFunction.value R X (S `&` B).
have ht := @CharacteristicFunction.laws R X (S `&` B).
have hSB := @measure_measurable_intersection R X phi hm S B hS hB.
have hi := @measure_characteristic_integral R X phi hm (S `&` B) t ht hSB.
have heon x : S x -> t x=s x.
  move=> hx; case: (pselect (B x))=> hb.
  - have hxSB : (S `&` B) x by split.
    by rewrite /t (characteristic_on_set ht hxSB) (characteristic_on_set hs hb).
  - have hnSB : ~ (S `&` B) x by move=> [_ h]; exact: hb h.
    by rewrite /t (characteristic_off_set ht hnSB) (characteristic_off_set hs hb).
have heoff x : ~ S x -> t x=0%R.
  move=> hx; rewrite /t; apply: (@characteristic_off_set R X (S `&` B) _ ht x).
  by move=> [h _]; exact: hx h.
apply: (@measure_integral_graph_equivalent R X phi (real_total_integrand t) _ _ _ hi)=> x y.
case: (pselect (S x))=> hx.
- rewrite (@partial_function_zero_extension_on X (extended_real_line R) 0 S
    (real_total_integrand s) x y hx) !real_total_integrand_graph.
  by rewrite (heon x hx).
- rewrite (@partial_function_zero_extension_off X (extended_real_line R) 0 S
    (real_total_integrand s) x y hx) real_total_integrand_graph (heoff x hx).
  split; move=> hy; symmetry; exact hy.
Qed.
