(** Federer (1969), 3.2.46, p. 281: rho separates
    distinct points. Nearby points use the proved local
    comparison; reaching outside that neighbourhood incurs
    its proved positive departure cost. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP
  PositiveSymmetricNormFactor RiemannianTensorUP RiemannianLocalDistanceComparison
  RiemannianDistance RiemannianDistanceBasic RiemannianDistanceDeparture.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_distance_separates]: the
    separation part of the metric assertion in Federer
    3.2.46, p. 281. Disconnected domains and infinite
    distances are retained; dimension zero is included. *)
Theorem riemannian_distance_separates (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x y :
  A x -> @riemannian_distance R n A g x y = 0%E -> x = y.
Proof.
move=> hx hZero.
have hTwo : (1 < 2 :> R) by rewrite ltr1n.
have hTwo0 : (0 < 2 :> R) by rewrite ltr0n.
have hTwoNe : (2 : R) != 0 by rewrite pnatr_eq0.
have [L [d [hd [hL hComparison]]]] := @riemannian_local_distance_comparison R n A g hg x hx 2 hTwo.
have hr : (0 < d/2)%R by rewrite divr_gt0.
have hCentre : inner_norm (@euclidean_inner_productP R n) (L (x-x)) <= d/2.
  rewrite subrr linear0 inner_norm0; exact: ltW hr.
have hLocal z : inner_norm (@euclidean_inner_productP R n) (L (z-x)) <= d/2 ->
    ((((2 : R)^-1*inner_norm (@euclidean_inner_productP R n) (L (z-x)))%R)%:E <=
      @riemannian_distance R n A g x z)%E.
  move=> hz; exact: (hComparison x z hCentre hz).2.2.1.
case: (leP (inner_norm (@euclidean_inner_productP R n) (L (y-x))) (d/2))=> hy.
- have hLower := hLocal y hy.
  rewrite hZero lee_fin in hLower.
  have hScaled := ler_wpM2l (ltW hTwo0) hLower.
  rewrite mulrA (mulfV hTwoNe) mul1r mulr0 in hScaled.
  have hNormZero : inner_norm (@euclidean_inner_productP R n) (L (y-x)) = 0.
    by apply/eqP; rewrite eq_le hScaled inner_norm_nonnegative.
  have hImage := (inner_norm_real_norm (@euclidean_inner_productP R n)).2 (L (y-x)) hNormZero.
  have hImage' : L (y-x) = L 0 by rewrite linear0.
  have hDiff := positive_norm_factor_injective hL hImage'.
  have hyx : y = x by apply/eqP; rewrite -subr_eq0 hDiff eqxx.
  exact: esym hyx.
- have hBarrier := @riemannian_distance_departure_lower R n A g hg L x y (d/2) ((2 : R)^-1)
    hr hLocal hy.
  rewrite hZero lee_fin in hBarrier.
  have hInversePositive : (0 < (2 : R)^-1)%R by rewrite invr_gt0.
  have hPositive : (0 < (2 : R)^-1*(d/2))%R := mulr_gt0 hInversePositive hr.
  by have hBad := lt_le_trans hPositive hBarrier; rewrite ltxx in hBad.
Qed.

(** Source for [riemannian_distance_zero_iff]: rho(x,y)=0
    exactly when x=y, the metric identity in Federer 3.2.46,
    p. 281, from actual separation and the constant curve. *)
Lemma riemannian_distance_zero_iff (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x y :
  A x -> (@riemannian_distance R n A g x y = 0%E <-> x = y).
Proof.
move=> hx; split.
- exact (@riemannian_distance_separates R n A g hg x y hx).
- move=> <-; exact (@riemannian_distance_self R n A g hg x hx).
Qed.
