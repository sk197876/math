(** Federer (1969), 2.4.14, p. 88: normalising the absolute product by the
    two norms. Supporting graph and integral identities preserve the common
    partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  PartialNormProduct MeasureUpperIntegralScale MeasureUP MeasureIntegralUP
  MeasureIntegralScaleLaw MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_norm_product_scaled_graph]: supporting
    cancellation of the two normalising scalars in Federer
    2.4.14, p. 88. This graph identity also permits
    zero and negative scalars, using their absolute values. *)
Lemma partial_norm_product_scaled_graph (R : realType) (X : Type)
    (V W : lmodType R) (N : V -> R) (M : W -> R)
    (hN : is_real_norm N) (hM : is_real_norm M)
    (f : partial_function X V) (g : partial_function X W) (c d : R) x z :
  partial_function_graph (partial_norm_product N M (partial_vector_scale c f)
    (partial_vector_scale d g)) x z <->
  partial_function_graph (partial_extended_function_scale (`|c| * `|d|)
    (partial_norm_product N M f g)) x z.
Proof.
have he a b : (N (c *: a) * M (d *: b))%:E =
    (`|c| * `|d|)%:E * (N a * M b)%:E.
  by rewrite (real_seminorm_scale hN.1) (real_seminorm_scale hM.1) mulrACA EFinM.
rewrite (@partial_norm_product_graph R X V W N M hN hM); split.
- move=> [a [b [[u [hu hua]] [[v [hv hvb]] hab]]]].
  exists (N u * M v)%:E; split.
  + apply/(@partial_norm_product_graph R X V W N M hN hM).
    exists u,v; by split=> //; split.
  + by rewrite -he hua hvb.
- move=> [w [hw hwz]].
  have [u [v [hu [hv huv]]]] := (@partial_norm_product_graph R X V W N M hN hM f g x w).1 hw.
  exists (c *: u)%R,(d *: v)%R; split; first by exists u; split.
  split; first by exists v; split.
  by rewrite he huv.
Qed.

(** Source for [measure_norm_product_positive_scale]: supporting integral
    normalisation in Federer 2.4.14, p. 88 It follows from the graph
    identity and the previously proved scalar integral law. *)
Lemma measure_norm_product_positive_scale (R : realType) (X : choiceType)
    (V W : lmodType R) (N : V -> R) (M : W -> R)
    (hN : is_real_norm N) (hM : is_real_norm M)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X V) (g : partial_function X W) (c d : R) a :
  (0 < c)%R -> (0 < d)%R -> is_measure_integral mu (partial_norm_product N M f g) a ->
  is_measure_integral mu (partial_norm_product N M (partial_vector_scale c f)
    (partial_vector_scale d g)) ((c*d)%:E*a).
Proof.
move=> hc hd hi.
have hcd : (0 < c*d)%R := mulr_gt0 hc hd.
have hs := @measure_integral_positive_scale R X mu hm (c*d)%R _ a hcd hi.
apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hs)=> x z.
rewrite (@partial_norm_product_scaled_graph R X V W N M hN hM).
by rewrite (ger0_norm (ltW hc)) (ger0_norm (ltW hd)).
Qed.
