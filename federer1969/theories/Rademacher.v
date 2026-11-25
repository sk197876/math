(** Federer (1969), 3.1.6, pp. 216–217: Rademacher's
    theorem. The proof follows the book through the one-dimensional
    bounded-variation theorem, Fubini, 3.1.4, and 3.1.5. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  EuclideanLebesgueDimensions EuclideanFiniteZeroDensity
  NormDifferentialUP NormDifferentialLinear ApproximateDifferential
  ApproximatePartialDerivative LipschitzUP LipschitzApproximatePartials
  EuclideanApproximateDifferentiability ApproximateToOrdinaryDifferential
  PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [federer_3_1_6]: Rademacher's theorem in
    Federer 3.1.6, pp. 216–217. Every Lipschitz map
    R^m -> R^n is differentiable at Lebesgue almost every
    point. The theorem includes the constant map on R^0;
    no hypothesis about existence of partial derivatives remains. *)
Theorem federer_3_1_6 (R : realType) m n
    (f : inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) :
  is_metric_lipschitz setT f ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    [set a | norm_differentiable_at
      (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f a].
Proof.
case: m f=> [f hLip|m f hLip].
- apply: (measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R 0)
    _ (measure_almost_everywhere_true (euclidean_lebesgue_is_measure R 0)))=> a _.
  exists 0.
  have he : f=(fun _=>f 0) by apply: funext=> x; rewrite (coordinate_zero x).
  rewrite he.
  apply: (norm_differential_constant
    (inner_norm_real_norm (@euclidean_inner_productP R 0))
    (inner_norm_real_norm (@euclidean_inner_productP R n))).
  exists 1; split; [exact: ltr01|by []].
- pose mu := @euclidean_lebesgue_measure R m.+1.
  pose hm := euclidean_lebesgue_is_measure R m.+1.
  pose hN := inner_norm_real_norm (@euclidean_inner_productP R n).
  pose A := \bigcap_i partial_function_domain
    (approximate_partial_derivative hN setT f i).
  have hA : measure_almost_everywhere mu A.
    apply: (measure_almost_everywhere_countable hm); first exact: countableP.
    move=> i _; exact: euclidean_lipschitz_approximate_partial_conull i hLip.
  have happ := euclidean_approximate_differentiability_from_partials
    (euclidean_lipschitz_measurable hLip).
  have hboth := measure_almost_everywhere_and hm hA
    ((measure_almost_everywhere_on_implication _ _ _).1 happ).
  apply: (measure_almost_everywhere_mono hm _ hboth)=> a [ha hd].
  have [L [v [hL _]]] := hd ha.
  exists L.
  have [M [hM [hM0 hbound]]] := hLip.
  apply: (@federer_3_1_5 R m.+1 n setT setT f 1 M a L).
  + by [].
  + exact: ltr01.
  + exact hM.
  + move=> z _ x _; split=> //.
    have hh := hbound x z Logic.I Logic.I.
    by rewrite !inner_metric_distanceE in hh.
  + exact Logic.I.
  + rewrite setCT; exact: euclidean_empty_set_density_zero.
  + exact: (approximate_differential_graph hN setT f a L).1 hL.
Qed.
