(** Federer (1969), 3.2.46, pp. 281–282:
    continuous actual volume densities are arbitrarily
    close to the determinant of each frozen local
    isometry. The neighbourhood is independent of a
    chosen factor; no global frame is selected. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology.
From Federer Require Import GrassmannAbbreviations RiemannianTensorUP RiemannianMetricCarrier
  RiemannianChartVolumeDensity ContinuousPositiveRelativeControl
  PositiveSymmetricNormFactor PositiveNormFactorDiscriminant EuclideanLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_local_volume_density_bounds]:
    on a proved open neighbourhood of a, j(x)<=lambda
    det L and det L<=lambda j(x) for every actual
    frozen factor L, supporting 3.2.46, p. 282.
    The determinant is the genuine sqrt(discr g(a));
    zero-dimensional volume remains the positive unit atom. *)
Lemma riemannian_local_volume_density_bounds (R : realType) m A g
    (hg : @is_continuous_riemannian_tensor R m A g)
    (a : riemannian_metric_space hg) (lambda : R) :
  1<lambda -> exists V : set (riemannian_metric_space hg), open V /\ V a /\
    forall L : {linear R_n R m -> R_n R m},
      is_positive_symmetric_norm_factor (riemannian_tensor_inner hg (set_valP a)) L ->
      forall x, V x -> riemannian_chart_volume_density hg x<=lambda*euclidean_det L /\
        euclidean_det L<=lambda*riemannian_chart_volume_density hg x.
Proof.
move=> hLambda.
have hLambda0 : 0<lambda := lt_trans ltr01 hLambda.
have hLambdaNe := lt0r_neq0 hLambda0.
have [V [hV [ha hControl]]] := @continuous_positive_relative_neighbourhood R
  [the topologicalType of riemannian_metric_space hg] (riemannian_chart_volume_density hg) a lambda
  (@riemannian_chart_volume_density_continuous R m A g hg)
  (@riemannian_chart_volume_density_positive R m A g hg a) hLambda.
exists V; split; first exact hV; split; first exact ha.
move=> L hL x hx.
have hDet : euclidean_det L=riemannian_chart_volume_density hg a := positive_norm_factor_discriminant hL.
rewrite hDet; split; first exact:(hControl x hx).2.
have hScaled := ler_wpM2r (ltW hLambda0) (hControl x hx).1.
by rewrite (divfK hLambdaNe) [riemannian_chart_volume_density hg x*lambda]mulrC in hScaled.
Qed.
