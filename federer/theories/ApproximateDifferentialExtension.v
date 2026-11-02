(** Federer (1969), 3.1.8, p. 218, last paragraph, and
    3.1.9, p. 218: approximate differentiability of a restriction
    passes to the original function. The original values on the
    smaller domain are retained exactly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric RealNormUP RealMetricBackground PartialFunctionUP
  MeasureDerivationContext MeasureApproximateLimitUP LocalZeroDensity
  EuclideanApproximateContext ApproximateDifferentialUP ApproximateDifferentialRemainder
  ApproximateDifferentialLocal ApproximatePartialDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [measure_approximate_limit_graph_extension]:
    supporting inverse-image comparison for the inference
    "hence also f" in Federer 3.1.8, p. 218.
    Extending a partial graph can only decrease the complement
    of the inverse image of each neighborhood. *)
Theorem measure_approximate_limit_graph_extension (R : realType)
    (X : metricType R) (Y : topologicalType) (phi : set X->\bar R)
    (V : X->set X->Prop) (f g : partial_function X Y) a b :
  is_measure_derivation_context phi V ->
  (forall x y, partial_function_graph f x y -> partial_function_graph g x y) ->
  is_measure_approximate_limit phi V f a b ->
  is_measure_approximate_limit phi V g a b.
Proof.
move=> hc hfg hf W hW.
apply: (@local_zero_density_mono R X phi V
  (~` partial_function_preimage g W) (~` partial_function_preimage f W)
  setT a hc openT I _ (hf W hW)).
move=> x _ hnot [y [hy hWy]]; apply: hnot; exists y; split=> //.
exact: hfg x y hy.
Qed.

(** Source for [approximate_differential_enlarge_domain]:
    Federer 3.1.8, p. 218, last paragraph, and 3.1.9,
    p. 218. An approximate differential on a subset is the
    same approximate differential on a larger domain where the
    values agree. No conullness assumption on either whole domain
    is inserted. *)
Theorem approximate_differential_enlarge_domain (R : realType) m
    (Y : lmodType R) (NY : Y->R)
    (A B : set (R_n R m)) (f g : R_n R m->Y) a L :
  A `<=` B -> (forall x, A x -> f x=g x) ->
  has_approximate_differential NY A f a L ->
  has_approximate_differential NY B g a L.
Proof.
move=> hAB hfg [ha hf]; split; first exact: hAB a ha.
apply: (measure_approximate_limit_graph_extension
  (euclidean_approximate_context R m) _ hf).
move=> x y hy; apply: (approximate_remainder_quotient_graph NY B g a L x y).2.
have [hx [hne hyv]] := (approximate_remainder_quotient_graph NY A f a L x y).1 hy.
split; first exact: hAB x hx.
split=> //; by rewrite -(hfg x hx) -(hfg a ha).
Qed.

(** Source for [approximate_partial_enlarge_domain]:
    the same actual-domain principle for approximate partial
    derivatives, supporting Federer 3.1.8, pp. 217–218.
    The one-dimensional exceptional sets include undefined inputs,
    as prescribed in 3.1.2, p. 212. *)
Theorem approximate_partial_enlarge_domain (R : realType) m
    (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (A B : set (R_n R m)) (f g : R_n R m->Y) a i v :
  A `<=` B -> (forall x, A x -> f x=g x) ->
  has_approximate_partial_derivative hNY A f a i v ->
  has_approximate_partial_derivative hNY B g a i v.
Proof.
move=> hAB hfg [ha hf]; split; first exact: hAB a ha.
apply: (measure_approximate_limit_graph_extension
  (scalar_approximate_context R) _ hf).
move=> t y hy; apply: (@approximate_partial_quotient_graph R m Y NY hNY B g a i t y).2.
have [ht [hx hyv]] := (@approximate_partial_quotient_graph R m Y NY hNY A f a i t y).1 hy.
split=> //; split; first exact: hAB _ hx.
by rewrite -(hfg _ hx) -(hfg a ha).
Qed.
