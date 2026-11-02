(** Federer (1969), 2.4.14, p. 88: normalising the signed real product by
    the two positive finite norms. Supporting graph and integral identities
    use the common partial domain throughout. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  PartialScalarProduct MeasureUpperIntegralScale MeasureUP MeasureIntegralUP
  MeasureIntegralScaleLaw MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_scalar_product_scaled_graph]: supporting
    scalar cancellation for the normalised signed integral in
    Federer 2.4.14, p. 88. This graph identity
    holds for arbitrary real scalars, including zero. *)
Lemma partial_scalar_product_scaled_graph (R : realType) (X : Type)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) (c d : R) x z :
  partial_function_graph (partial_scalar_product (partial_vector_scale c f) (partial_vector_scale d g)) x z <->
  partial_function_graph (partial_extended_function_scale (c*d)%R (partial_scalar_product f g)) x z.
Proof.
have he a b : ((c*a)*(d*b))%:E = (c*d)%:E*(a*b)%:E by rewrite mulrACA EFinM.
rewrite partial_scalar_product_graph; split.
- move=> [a [b [[u [hu hua]] [[v [hv hvb]] hab]]]].
  change ((c*u)%R=a) in hua.
  change ((d*v)%R=b) in hvb.
  exists (u*v)%:E; split.
  + apply/partial_scalar_product_graph; exists u,v; by split=> //; split.
  + by rewrite -he hua hvb.
- move=> [w [hw hwz]].
  have [u [v [hu [hv huv]]]] := (partial_scalar_product_graph f g x w).1 hw.
  exists (c*u)%R,(d*v)%R; split; first by exists u; split.
  split; first by exists v; split.
  by rewrite he huv.
Qed.

(** Source for [measure_scalar_product_positive_scale]: integral rescaling
    in Federer 2.4.14, proof p. 88 The two scalars are positive, while the
    integral value may have either sign. *)
Lemma measure_scalar_product_positive_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) (c d : R) a :
  (0 < c)%R -> (0 < d)%R -> is_measure_integral mu (partial_scalar_product f g) a ->
  is_measure_integral mu (partial_scalar_product (partial_vector_scale c f) (partial_vector_scale d g)) ((c*d)%:E*a).
Proof.
move=> hc hd hi; have hcd : (0 < c*d)%R := mulr_gt0 hc hd.
have hs := @measure_integral_positive_scale R X mu hm (c*d)%R _ a hcd hi.
apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hs)=> x z.
exact (iff_sym (partial_scalar_product_scaled_graph f g c d x z)).
Qed.
