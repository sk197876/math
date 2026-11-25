(** Federer (1969), 2.4.14, p. 88: the signed real product fg and its
    absolute value. These supporting graph laws identify the signed
    integrand with the norm product after taking absolute values. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP
  ScalarNormExtendedEmbedding PartialDensityProduct PartialNormProduct PartialAbsolutePartsGraph
  MeasureUP MeasurableFunctionUP MeasurableDensityProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_scalar_product]: the signed real
    integrand fg of Federer 2.4.14, p. 88,
    represented in the extended-real integral interface with
    exactly the common domain of f and g. *)
Definition partial_scalar_product (R : realType) (X : Type)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :=
  partial_density_product (partial_scalar_extended_embedding f) (partial_scalar_extended_embedding g).

(** Source for [partial_scalar_product_graph]: supporting graph
    interpretation of the integrand in Federer 2.4.14,
    p. 88. Both factors have finite real values. *)
Lemma partial_scalar_product_graph (R : realType) (X : Type)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) x z :
  partial_function_graph (partial_scalar_product f g) x z <->
  exists a b, partial_function_graph f x a /\ partial_function_graph g x b /\ (a*b)%:E=z.
Proof.
rewrite /partial_scalar_product partial_density_product_graph; split.
- move=> [u [v [[a [ha hau]] [[b [hb hbv]] huv]]]].
  exists a,b; split=> //; split=> //; by rewrite EFinM hau hbv.
- move=> [a [b [ha [hb hab]]]]; exists a%:E,b%:E; split; first by exists a; split.
  split; first by exists b; split.
  by rewrite -EFinM.
Qed.

(** Source for [partial_scalar_absolute_product_graph]: the identity
    |fg|=|f||g| in the proof of Federer 2.4.14, p. 88 *)
Lemma partial_scalar_absolute_product_graph (R : realType) (X : Type)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) x z :
  partial_function_graph (partial_extended_function_absolute_value (partial_scalar_product f g)) x z <->
  partial_function_graph (partial_norm_product (fun a : R => `|a|%R) (fun a : R => `|a|%R) f g) x z.
Proof.
rewrite (@partial_norm_product_graph R X R^o R^o _ _
  (scalar_absolute_value_norm R) (scalar_absolute_value_norm R)); split.
- move=> [w [hw hwz]].
  have [a [b [ha [hb hab]]]] := (partial_scalar_product_graph f g x w).1 hw.
  exists a,b; split=> //; split=> //.
  by rewrite -hab abse_EFin normrM in hwz.
- move=> [a [b [ha [hb hab]]]]; exists (a*b)%:E; split.
  + apply/partial_scalar_product_graph; exists a,b; by split=> //; split.
  + by rewrite abse_EFin normrM.
Qed.

(** Source for [measurable_scalar_product]: supporting
    measurability of fg in Federer 2.4.14, p. 88,
    using the already proved measurable product operation. *)
Lemma measurable_scalar_product (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  is_measure_measurable_function mu (partial_scalar_product f g).
Proof.
move=> hf hg; apply: (@measurable_density_product R X mu hm).
- exact (@measurable_scalar_extended_embedding R X mu hm f hf).
- exact (@measurable_scalar_extended_embedding R X mu hm g hg).
Qed.
