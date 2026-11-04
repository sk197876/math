(** Federer (1969), 3.2.46, pp. 281–282:
    the same actual local source isometry compares every
    whole complementary fibre measure. This supporting
    geometric step retains arbitrary original sources
    before any coarea integral is considered. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff RiemannianLocalHausdorffComparison
  PositiveSymmetricNormFactor RealPower RealPowerNaturalHausdorff RealHausdorffMeasure
  MappingMultiplicity HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_local_fibre_mass_comparison]:
    local lambda^k comparison of the actual whole
    H_rho^k fibre and its frozen Euclidean image,
    supporting 3.2.46, p. 282. One local
    factor and radius work for every natural k,
    every original source subset and every map f;
    finite mass, measurability and rank are not assumed. *)
Theorem riemannian_local_fibre_mass_comparison (R : realType) m A g
    (hg : @is_continuous_riemannian_tensor R m A g) a (ha : A a) (lambda : R) :
  1<lambda -> exists L : {linear R_n R m -> R_n R m}, exists r : R,
    0<r /\ is_positive_symmetric_norm_factor (riemannian_tensor_inner hg ha) L /\
    forall (Y : Type) (f : riemannian_metric_space hg -> Y)
      (S : set (riemannian_metric_space hg)) k (hp : 0<=k%:R :> R),
      (forall x, S x -> inner_norm (@euclidean_inner_productP R m) (L (val x-a))<=r) ->
      forall y,
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) k
        ((fun x : riemannian_metric_space hg=>L (val x)) @` mapping_fibre f S y)<=
        (lambda^+k)%:E*riemannian_hausdorff_measure hg k%:R hp (mapping_fibre f S y))%E /\
      (riemannian_hausdorff_measure hg k%:R hp (mapping_fibre f S y)<=
        (lambda^+k)%:E*@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) k
        ((fun x : riemannian_metric_space hg=>L (val x)) @` mapping_fibre f S y))%E.
Proof.
move=> hLambda.
have [L [r [hr [hL [hDomain hComparison]]]]] :=
  @riemannian_local_hausdorff_comparison R m A g hg a ha lambda hLambda.
exists L,r; split; first exact hr; split; first exact hL.
move=> Y f S k hp hNear y.
have hBounds := hComparison k%:R hp (mapping_fibre f S y)
  (fun x hx=>hNear x hx.1).
by rewrite real_hausdorff_measure_natural real_power_natural_exponent in hBounds;
  last exact:ltW (lt_trans ltr01 hLambda).
Qed.
