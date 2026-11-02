(** Federer (1969), 2.4.4(3), p. 82: supporting measurability of nonzero
    real scalar multiples. The operation agrees with the already formalised
    partial product of 2.3.2, p. 74, whose domain is conull for a finite
    nonzero scalar. Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionUP PartialFunctionBasic
  PartialFunctionPostcomposition PartialExtendedArithmetic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableTotalBasic MeasurableExtendedArithmetic MeasurableGraphEquivalence
  MeasureUpperIntegralScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonzero_real_extended_product_defined]: scalar
    domain fact supporting Federer 2.4.4(3), p. 82:
    a finite nonzero factor can multiply either infinite value. *)
Lemma nonzero_real_extended_product_defined (R : realType) (c : R) (z : \bar R) :
  c != 0%R -> mule_def c%:E z.
Proof. move=> hc; by case: z=> [z| |]; rewrite /mule_def. Qed.

(** Source for [nonzero_scale_product_graph]: exact graph
    comparison with ordinary partial multiplication supporting
    Federer 2.4.4(3), p. 82. *)
Lemma nonzero_scale_product_graph (R : realType) (X : Type) (c : R)
    (f : partial_function X (extended_real_line R)) :
  c != 0%R -> forall x y,
  partial_function_graph (partial_extended_function_multiply
    (partial_function_total (fun _ : X => (c%:E : extended_real_line R))) f) x y <->
  partial_function_graph (partial_extended_function_scale c f) x y.
Proof.
move=> hc x y; rewrite partial_extended_function_multiply_graph; split.
- move=> [a [b [ha [hb he]]]].
  rewrite -ha /extended_multiply (@nonzero_real_extended_product_defined R c b hc) in he.
  case: he=> he; exists b; by split.
- move=> [b [hb he]]; exists c%:E,b; split=> //; split=> //.
  by rewrite /extended_multiply nonzero_real_extended_product_defined // he.
Qed.

(** Source for [measurable_extended_nonzero_scale]: supporting
    measurable-function closure used in Federer 2.4.4(3),
    pp. 82–83, preserving the exact domain. *)
Lemma measurable_extended_nonzero_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R)
    (f : partial_function X (extended_real_line R)) :
  c != 0%R -> is_measure_measurable_function mu f ->
  is_measure_measurable_function mu (partial_extended_function_scale c f).
Proof.
move=> hc hf; pose g := partial_function_total (fun _ : X => (c%:E : extended_real_line R)).
have he := @nonzero_scale_product_graph R X c f hc.
have hd : measure_almost_everywhere mu (partial_function_domain (partial_extended_function_multiply g f)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain hf)).
  move=> x [y hy]; exists (c%:E*y); apply: (he x _).2; exists y; by split.
have hmul := @measurable_extended_function_multiply R X mu hm g f
  (@measurable_total_constant R X (extended_real_line R) mu hm c%:E) hf hd.
exact: measurable_function_graph_equivalent he hmul.
Qed.
