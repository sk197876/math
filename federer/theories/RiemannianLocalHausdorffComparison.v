(** Federer (1969), 3.2.46, p. 281: lambda^(-p) H^p(L(S))
    <= H_rho^p(S) <= lambda^p H^p(L(S)). The equivalent
    two-sided positive-factor bounds below retain all p>=0,
    arbitrary original subsets and infinite Hausdorff masses. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric PositiveSymmetricNormFactor RiemannianTensorUP
  RiemannianMetricCarrier RiemannianLocalMetricComparison RiemannianHausdorff
  RealHausdorffMeasure RealPower LipschitzUP MetricBiLipschitzUP RealPowerBiLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_local_hausdorff_comparison]: the
    real-dimensional Hausdorff comparison in 3.2.46, p. 281,
    follows from actual local metric bounds and original-rho
    covering compatibility. The same local L and radius work
    for every nonnegative real degree, with no measurable-set
    or finite-mass premise. *)
Theorem riemannian_local_hausdorff_comparison (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) o (ho : A o) (lambda : R) :
  1<lambda -> exists L : {linear R_n R n -> R_n R n}, exists r : R,
    0<r /\ is_positive_symmetric_norm_factor (riemannian_tensor_inner hg ho) L /\
    (forall z, inner_norm (@euclidean_inner_productP R n) (L (z-o))<=r -> A z) /\
    forall (p : R) (hp : 0<=p) (S : set (riemannian_metric_space hg)),
      (forall x, S x -> inner_norm (@euclidean_inner_productP R n) (L (val x-o))<=r) ->
      (@real_hausdorff_measure R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] p hp
        ((fun x : riemannian_metric_space hg=>L (val x)) @` S) <=
        (real_power lambda p)%:E * riemannian_hausdorff_measure hg p hp S)%E /\
      (riemannian_hausdorff_measure hg p hp S <= (real_power lambda p)%:E *
        @real_hausdorff_measure R
          [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] p hp
          ((fun x : riemannian_metric_space hg=>L (val x)) @` S))%E.
Proof.
move=> hLambda.
have hLambda0 : 0<lambda := lt_trans ltr01 hLambda.
have hLambdaNe : lambda!=0 := lt0r_neq0 hLambda0.
have [L [r [hr [hL [hPatch hControl]]]]] :=
  @riemannian_local_metric_comparison R n A g hg o ho lambda hLambda.
exists L,r; split; first exact hr; split; first exact hL; split; first exact hPatch.
move=> p hp S hS.
pose M := [the metricType R of riemannian_metric_space hg].
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose K : set M := [set x | inner_norm (@euclidean_inner_productP R n) (L (val x-o))<=r].
pose f := fun x : M=>(L (val x) : E).
pose x0 : M := @exist E (fun x=>x \in (A : set E)) o (mem_set ho).
have hBi : is_metric_bilipschitz_bound K f lambda.
  split.
  - split; first exact: ltW hLambda0.
    move=> x y hx hy.
    have hLower := (hControl y x hy hx).1.
    rewrite (metric_sym y x) in hLower.
    have hScale := ler_wpM2l (ltW hLambda0) hLower.
    rewrite mulrA (mulfV hLambdaNe) mul1r in hScale.
    rewrite /f inner_metric_distanceE -linearB; exact hScale.
  - move=> x y hx hy.
    have hUpper := (hControl y x hy hx).2.
    rewrite (metric_sym y x) in hUpper.
    rewrite /f inner_metric_distanceE -linearB; exact hUpper.
have hBounds := @real_hausdorff_bilipschitz_bounds R M E K f lambda p hp x0 S hLambda0 hBi hS.
rewrite /f /M in hBounds.
by rewrite !riemannian_hausdorff_carrier.
Qed.
