(** Federer (1969), 3.1.9, p. 218: Stepanoff's
    theorem, with the ordinary local limsup from 2.2.7.
    The exceptional source set A need not be measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  EuclideanLebesgueDimensions MetricSlopeLimsup MetricFiniteGrowthCover
  MetricLocalLipschitzCenters LipschitzCentersDifferentiability
  NormDifferentialUP NormDifferentialLinear NormDifferentialLocal
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [federer_3_1_9]: Stepanoff's theorem,
    Federer 3.1.9, p. 218. Finite upper growth at
    every point of A inside the open domain B implies
    ordinary differentiability at Lebesgue almost all points
    of A. All source and target dimensions are included;
    the singleton source is handled by the constant-map law. *)
Theorem federer_3_1_9 (R : realType) m n
    (A B : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) :
  A `<=` B -> open B ->
  (forall a, A a -> (metric_local_slope_limsup B f a< +oo)%E) ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A
    [set a | norm_differentiable_at
      (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) B f a].
Proof.
case: m A B f=> [A B f hAB hB hlim|m A B f hAB hB hlim].
- apply: (measure_almost_everywhere_on_implication _ _ _).2.
  apply: (measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R 0)
    _ (measure_almost_everywhere_true (euclidean_lebesgue_is_measure R 0)))=> a _ ha.
  have heq (x : R_n R 0) : x=a by rewrite (coordinate_zero x) (coordinate_zero a).
  have hint : norm_domain_interior
      (inner_norm (@euclidean_inner_productP R 0)) B a.
    exists 1; split; first exact: ltr01.
    move=> h _; rewrite (heq (a+h)); exact: hAB a ha.
  exists 0.
  apply: (norm_differential_domain_agreement
    (inner_norm_real_norm (@euclidean_inner_productP R 0)) _
    (norm_differential_constant
      (inner_norm_real_norm (@euclidean_inner_productP R 0))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) (f a) hint)).
  by move=> x _; rewrite (heq x).
- pose mu := @euclidean_lebesgue_measure R m.+1.
  pose hm := euclidean_lebesgue_is_measure R m.+1.
  pose P := [set a | norm_differentiable_at
    (inner_norm (@euclidean_inner_productP R m.+1))
    (inner_norm (@euclidean_inner_productP R n)) B f a].
  pose C j := metric_local_lipschitz_centers B f
    (j.+1%:R : R) ((j.+1%:R)^-1).
  have hall : measure_almost_everywhere mu
      (\bigcap_j [set a | C j a -> P a]).
    apply: (measure_almost_everywhere_countable hm); first exact: countableP.
    move=> j _; apply: (measure_almost_everywhere_on_implication _ _ _).1.
    apply: lipschitz_centers_differentiable_almost.
    + by rewrite ltr0n.
    + by rewrite invr_gt0 ltr0n.
  apply: (measure_almost_everywhere_on_implication _ _ _).2.
  apply: (measure_almost_everywhere_mono hm _ hall)=> a hall0 ha.
  have [j hj] := finite_metric_slope_natural_center hB (hAB a ha) (hlim a ha).
  exact: hall0 j Logic.I hj.
Qed.
