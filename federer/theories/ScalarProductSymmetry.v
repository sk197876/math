(** Federer (1969), 2.4.14, p. 88: symmetry in the two factors of Holder's
    inequality and equality condition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialScalarProduct
  MeasureIntegralUP MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_scalar_product_commute_graph]: supporting
    symmetry of the product in Federer 2.4.14, p. 88.
    The common domain is unchanged by exchanging the factors. *)
Lemma partial_scalar_product_commute_graph (R : realType) (X : Type)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) x z :
  partial_function_graph (partial_scalar_product f g) x z <->
  partial_function_graph (partial_scalar_product g f) x z.
Proof.
rewrite !partial_scalar_product_graph; split;
  move=> [a [b [ha [hb hab]]]]; exists b,a; split=> //; split=> //;
  by rewrite mulrC.
Qed.

(** Source for [measure_scalar_product_commute]: supporting integral
    symmetry for the either-direction dependence condition in Federer
    2.4.14, p. 88 *)
Lemma measure_scalar_product_commute (R : realType) (X : choiceType)
    (mu : set X -> \bar R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) c :
  is_measure_integral mu (partial_scalar_product f g) c ->
  is_measure_integral mu (partial_scalar_product g f) c.
Proof.
move=> hi; apply: (@measure_integral_graph_equivalent R X mu _ _ c _ hi).
exact: partial_scalar_product_commute_graph.
Qed.
