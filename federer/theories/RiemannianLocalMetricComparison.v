(** Federer (1969), 3.2.46, p. 281: local comparison
    in the technical finite metric carrier. Shrinking the
    proved neighbourhood ensures every original pair distance
    is at most one, so the cap changes none of these distances.
    The local factor remains an existential proof witness. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerNormInequalities InnerMetric PositiveSymmetricNormFactor
  RiemannianTensorUP RiemannianDistance RiemannianMetricCarrier
  RiemannianLocalDistanceComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [frozen_ellipsoid_pair_bound]: the ordinary
    norm triangle estimate on a local ellipsoid, supporting
    Federer 3.2.46, p. 281. No nonsingularity is needed
    for this elementary supporting bound. *)
Lemma frozen_ellipsoid_pair_bound (R : realType) n
    (L : {linear R_n R n -> R_n R n}) o x y (r : R) :
  inner_norm (@euclidean_inner_productP R n) (L (x-o)) <= r ->
  inner_norm (@euclidean_inner_productP R n) (L (y-o)) <= r ->
  inner_norm (@euclidean_inner_productP R n) (L (y-x)) <= 2*r.
Proof.
move=> hx hy.
have hDiff : y-x = (y-o)-(x-o) by rewrite opprB addrA addrNK.
rewrite hDiff linearB.
have h := inner_norm_triangle (@euclidean_inner_productP R n) (L (y-o)) (-L (x-o)).
rewrite inner_normN in h.
clear -h hx hy; lra.
Qed.

(** Source for [riemannian_local_metric_comparison]: at
    every original point and every lambda>1 there is an
    actual local linear comparison chart with the two
    finite-metric bounds of 3.2.46, p. 281. Its whole
    ellipsoid lies in A, all natural dimensions included. *)
Theorem riemannian_local_metric_comparison (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) o (ho : A o) (lambda : R) :
  1 < lambda -> exists L : {linear R_n R n -> R_n R n}, exists r : R,
    0 < r /\ is_positive_symmetric_norm_factor (riemannian_tensor_inner hg ho) L /\
    (forall z, inner_norm (@euclidean_inner_productP R n) (L (z-o)) <= r -> A z) /\
    forall x y : riemannian_metric_space hg,
      inner_norm (@euclidean_inner_productP R n) (L (val x-o)) <= r ->
      inner_norm (@euclidean_inner_productP R n) (L (val y-o)) <= r ->
      lambda^-1*inner_norm (@euclidean_inner_productP R n) (L (val y-val x)) <= mdist x y /\
      mdist x y <= lambda*inner_norm (@euclidean_inner_productP R n) (L (val y-val x)).
Proof.
move=> hLambda.
have hLambda0 : 0<lambda := lt_trans ltr01 hLambda.
have hFourLambda : 0<4*lambda by rewrite mulr_gt0 // ltr0n.
have [L [d [hd [hL hComparison]]]] :=
  @riemannian_local_distance_comparison R n A g hg o ho lambda hLambda.
pose hE := @euclidean_inner_productP R n.
pose r := Order.min (d/2) (1/(4*lambda)).
have hr0 : 0<r by rewrite /r lt_min !divr_gt0 // ltr0n.
have hrD : r<=d/2 by rewrite /r ge_min lexx.
have hrCap : r<=1/(4*lambda) by rewrite /r ge_min lexx orbT.
have hCapScale : (4*lambda)*r<=1 by rewrite mulrC -ler_pdivlMr.
have hCentre : inner_norm hE (L (o-o))<=d/2.
  rewrite subrr linear0 inner_norm0; clear -hd; lra.
exists L,r; split; first exact hr0; split; first exact hL; split.
- move=> z hz; exact: (hComparison o z hCentre (le_trans hz hrD)).2.1.
- move=> x y hx hy.
  have hLocal := hComparison (val x) (val y) (le_trans hx hrD) (le_trans hy hrD).
  have hPair := frozen_ellipsoid_pair_bound hx hy.
  have hPairScale : lambda*inner_norm hE (L (val y-val x))<=1.
    clear -hPair hCapScale hLambda0; nra.
  have hOriginalSmall : (@riemannian_distance R n A g (val x) (val y)<=1)%E.
    apply: le_trans hLocal.2.2.2 _; by rewrite -[1%E]/((1 : R)%:E) lee_fin.
  have hValue := @riemannian_metric_small_distance R n A g hg x y hOriginalSmall.
  split.
  + have hLower := hLocal.2.2.1.
    by rewrite -hValue lee_fin in hLower.
  + have hUpper := hLocal.2.2.2.
    by rewrite -hValue lee_fin in hUpper.
Qed.
