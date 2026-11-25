(** Federer (1969), 2.4.4(3), p. 82, proof p. 83: a nonzero real scalar
    preserves integrability and scales the integral. The p. 185 scan
    confirms this source-number discrepancy, which is separate from
    Federer's erratum. Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralBounds MeasureIntegralSqueeze
  MeasureIntegralNegation MeasureIntegralNegationLaw MeasureUpperIntegralScale MeasurableExtendedScale
  MeasureIntegralGraphEquivalence MeasureBoundGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_scale_negation_graph]: supporting
    commutation of negation and scalar multiplication in the proof
    of Federer 2.4.4(3), p. 83. *)
Lemma extended_scale_negation_graph (R : realType) (X : Type) (c : R)
    (f : partial_function X (extended_real_line R)) x y :
  partial_function_graph (partial_extended_function_negate (partial_extended_function_scale c f)) x y <->
  partial_function_graph (partial_extended_function_scale c (partial_extended_function_negate f)) x y.
Proof.
split.
- move=> [z [[w [hw hwz]] hzy]]; exists (-w); split; first by exists w; split.
  by rewrite muleN hwz.
- move=> [z [[w [hw hwz]] hzy]]; exists (c%:E*w); split; first by exists w; split.
  by move: hzy; rewrite -hwz muleN.
Qed.

(** Source for [measure_lower_integral_positive_scale]: lower-
    integral counterpart of 2.4.3(5), used in Federer
    2.4.4(3), proof p. 83. *)
Lemma measure_lower_integral_positive_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R)
    (f : partial_function X (extended_real_line R)) :
  (0 < c)%R -> measure_lower_integral mu (partial_extended_function_scale c f) = c%:E*measure_lower_integral mu f.
Proof.
move=> hc; rewrite (@measure_lower_integral_negation R X mu hm).
have he := @measure_upper_integral_graph_equivalent R X mu _ _ (extended_scale_negation_graph c f).
rewrite he (@measure_upper_integral_positive_scale R X mu hm c _ hc).
by rewrite (@measure_lower_integral_negation R X mu hm f) muleN.
Qed.

(** Source for [measure_integral_positive_scale]: positive-scalar
    case of Federer 2.4.4(3), p. 82, including integrability. *)
Lemma measure_integral_positive_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R)
    (f : partial_function X (extended_real_line R)) a :
  (0 < c)%R -> is_measure_integral mu f a ->
  is_measure_integral mu (partial_extended_function_scale c f) (c%:E*a).
Proof.
move=> hc [hf [hu hl]].
have eu := @measure_upper_integral_unique R X mu f _ a (measure_upper_integral_specification mu f) hu.
have el := @measure_lower_integral_unique R X mu f _ a (measure_lower_integral_specification mu f) hl.
have hc0 : c != 0%R by rewrite gt_eqF.
apply: (@measure_integral_squeeze R X mu hm).
- exact (@measurable_extended_nonzero_scale R X mu hm c f hc0 hf).
- by rewrite (@measure_upper_integral_positive_scale R X mu hm c f hc) eu.
- by rewrite (@measure_lower_integral_positive_scale R X mu hm c f hc) el.
Qed.

(** Source for [negative_scale_factorisation_graph]: supporting
    reduction of a negative scalar to positive scaling and negation
    in Federer 2.4.4(3), proof p. 83. *)
Lemma negative_scale_factorisation_graph (R : realType) (X : Type) (c : R)
    (f : partial_function X (extended_real_line R)) x y :
  partial_function_graph (partial_extended_function_scale (-c)%R (partial_extended_function_negate f)) x y <->
  partial_function_graph (partial_extended_function_scale c f) x y.
Proof.
split.
- move=> [z [[w [hw hwz]] hzy]]; exists w; split=> //.
  by move: hzy; rewrite -hwz EFinN muleNN.
- move=> [w [hw hwy]]; exists (-w); split; first by exists w; split.
  by rewrite EFinN muleNN.
Qed.

(** Source for [measure_integral_nonzero_scale]: direct Federer
    2.4.4(3), p. 82, for arbitrary nonzero real c
    and either finite or infinite integral value. *)
Theorem measure_integral_nonzero_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R)
    (f : partial_function X (extended_real_line R)) a :
  c != 0%R -> is_measure_integral mu f a ->
  is_measure_integral mu (partial_extended_function_scale c f) (c%:E*a).
Proof.
move=> hc hf; have [hp|hp] := ltP 0%R c.
- exact (@measure_integral_positive_scale R X mu hm c f a hp hf).
- have hn : (c < 0)%R by rewrite lt_neqAle hc hp.
  have hnc : (0 < -c)%R by rewrite oppr_gt0.
  have hi := @measure_integral_positive_scale R X mu hm (-c)%R
    (partial_extended_function_negate f) (-a) hnc (@measure_integral_negation R X mu hm f a hf).
  rewrite EFinN muleNN in hi.
  exact: measure_integral_graph_equivalent (negative_scale_factorisation_graph c f) hi.
Qed.

(** Source for [inverse_scale_graph]: supporting inverse
    operation for the integrability equivalence in Federer
    2.4.4(3), pp. 82–83; c is finite and nonzero. *)
Lemma inverse_scale_graph (R : realType) (X : Type) (c : R)
    (f : partial_function X (extended_real_line R)) :
  c != 0%R -> forall x y,
  partial_function_graph (partial_extended_function_scale c^-1 (partial_extended_function_scale c f)) x y <->
  partial_function_graph f x y.
Proof.
move=> hc x y; split.
- move=> [z [[w [hw hwz]] hzy]].
  rewrite -hwz muleA -EFinM mulVf // mul1e in hzy; by rewrite -hzy.
- move=> hy; exists (c%:E*y); split; first by exists y; split.
  by rewrite muleA -EFinM mulVf // mul1e.
Qed.

(** Source for [measure_integral_nonzero_scale_iff]: domain- sensitive form
    of the equality in Federer 2.4.4(3), p. 82 *)
Theorem measure_integral_nonzero_scale_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R)
    (f : partial_function X (extended_real_line R)) a :
  c != 0%R -> (is_measure_integral mu (partial_extended_function_scale c f) (c%:E*a) <->
    is_measure_integral mu f a).
Proof.
move=> hc; split; last exact: measure_integral_nonzero_scale hc.
move=> hf; have hci : (c^-1)%R != 0%R by rewrite invr_eq0.
have hi := @measure_integral_nonzero_scale R X mu hm c^-1 _ (c%:E*a) hci hf.
rewrite muleA -EFinM mulVf // mul1e in hi.
exact: measure_integral_graph_equivalent (inverse_scale_graph f hc) hi.
Qed.
