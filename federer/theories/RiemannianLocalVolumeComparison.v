(** Federer (1969), 3.2.46, p. 281: in top degree
    the local Hausdorff comparison has coefficient
    det(L)=sqrt(discr g(a)). The source is arbitrary;
    no measurability or finite-mass assumption is added. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanLinearMaps EuclideanLebesgueUP
  EuclideanLebesgue EuclideanLebesgueDimensions EuclideanLebesgueDeterminant EuclideanHausdorffLebesgue
  PositiveSymmetricNormFactor PositiveNormFactorDiscriminant RiemannianTensorUP
  RiemannianMetricCarrier RiemannianHausdorff RiemannianLocalHausdorffComparison
  RealHausdorffMeasure RealPowerNaturalHausdorff RiemannianVolumeDensity
  PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_local_volume_comparison]: the
    penultimate display on p. 281 in 3.2.46, in equivalent
    positive-factor form. Its coefficient is an actual value
    of the original volume-density graph, not an assumed
    or globally selected determinant field. *)
Theorem riemannian_local_volume_comparison (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) o (ho : A o) (lambda : R)
    (hp : 0<=n%:R :> R) :
  1<lambda -> exists L : {linear R_n R n -> R_n R n}, exists r : R,
    0<r /\ 0<euclidean_det L /\
    partial_function_graph (riemannian_volume_density hg) o (euclidean_det L) /\
    (forall z, inner_norm (@euclidean_inner_productP R n) (L (z-o))<=r -> A z) /\
    forall S : set (riemannian_metric_space hg),
      (forall x, S x -> inner_norm (@euclidean_inner_productP R n) (L (val x-o))<=r) ->
      ((euclidean_det L)%:E * euclidean_lebesgue_measure n
        ((fun x : riemannian_metric_space hg=>val x) @` S) <=
        (lambda^+n)%:E * riemannian_hausdorff_measure hg n%:R hp S)%E /\
      (riemannian_hausdorff_measure hg n%:R hp S <=
        (lambda^+n)%:E * (euclidean_det L)%:E * euclidean_lebesgue_measure n
          ((fun x : riemannian_metric_space hg=>val x) @` S))%E.
Proof.
move=> hLambda.
have [L [r [hr [hL [hPatch hBounds]]]]] :=
  @riemannian_local_hausdorff_comparison R n A g hg o ho lambda hLambda.
have hDet0 := positive_norm_factor_det_positive hL.
exists L,r; split; first exact hr; split; first exact hDet0; split.
- exact: riemannian_volume_density_factor_value hL.
- split; first exact hPatch.
  move=> S hS.
  have h := hBounds n%:R hp S hS.
  pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
  pose V : set E := (fun x : riemannian_metric_space hg=>(val x : E)) @` S.
  have hImage : ((fun x : riemannian_metric_space hg=>L (val x)) @` S) =
      (L : E -> E) @` V.
    apply/seteqP; split=> y.
    * move=> [x hx <-]; exists (val x); first by exists x.
      by [].
    * move=> [z [x hx <-] <-]; by exists x.
  rewrite real_hausdorff_measure_natural (euclidean_hausdorff_spherical_lebesgue _).1
    hImage euclidean_lebesgue_linear_image (ger0_norm (ltW hDet0))
    real_power_natural_exponent in h; last exact: ltW (lt_trans ltr01 hLambda).
  split; first exact h.1.
  rewrite muleA in h; exact h.2.
Qed.
