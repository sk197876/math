(** Federer (1969), 3.2.20, p. 257: auxiliary total
    representatives preserve weighted integrands on their actual conull
    domains. The subset and zero-product conventions are 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPostcomposition PartialFunctionExtensionUP PartialZeroExtension PartialDensityProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_extended_density_weight_agreement]: supporting
    almost equality for the two integral transformations in Federer
    3.2.20, p. 257. The arbitrary weight need not be
    measurable or finite. The graph domain of the original density
    is retained on A, with zero extension only outside A. *)
Lemma zero_extended_density_weight_agreement (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (d : partial_function X (real_line_metric R)) (p : X -> R)
    (w : X -> extended_real_line R) :
  measure_almost_everywhere mu
    (partial_function_domain (partial_function_zero_extension (0%R:real_line_metric R) A d)) ->
  is_partial_function_total_extension (partial_function_zero_extension (0%R:real_line_metric R) A d) p ->
  measure_almost_equal mu
    (partial_function_zero_extension (0:extended_real_line R) A
      (partial_density_product (partial_function_total w)
        (partial_function_postcompose d (fun j=>(j%:E : extended_real_line R)))))
    (partial_function_total (fun x=>w x* (p x)%:E : extended_real_line R)).
Proof.
move=> hd hExt.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hd)=> x [j hj].
have hp : p x=j := hExt x j hj.
exists (w x* (p x)%:E); split; last reflexivity.
case: (pselect (A x))=> hA.
- apply: (partial_function_zero_extension_on _ _ _ hA).2.
  apply/partial_density_product_graph; exists (w x),j%:E.
  split; first reflexivity.
  split; last by rewrite hp.
  exists j; split; last reflexivity.
  exact: (partial_function_zero_extension_on _ _ _ hA).1 hj.
- apply: (partial_function_zero_extension_off _ _ _ hA).2.
  have hj0 : j=0%R := (partial_function_zero_extension_off _ _ _ hA).1 hj.
  by rewrite hp hj0 mule0.
Qed.
