(** Federer (1969), 3.2.46, p. 281: the path distance
    induces the original topology of A. These explicit local
    neighbourhood bounds use the actual comparison and exit cost;
    no connectedness or global finiteness is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric OperatorNorm
  PositiveSymmetricNormFactor PositiveNormFactorBound RiemannianTensorUP
  RiemannianLocalDistanceComparison RiemannianDistanceDeparture
  RiemannianDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_euclidean_to_distance_neighbourhood]:
    the local upper comparison in Federer 3.2.46, p. 281,
    gives a Euclidean neighbourhood lying in each rho ball.
    Membership in A is derived, including dimension zero. *)
Lemma riemannian_euclidean_to_distance_neighbourhood (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) o (ho : A o) (e : R) :
  0 < e -> exists r : R, 0 < r /\ forall y,
    inner_norm (@euclidean_inner_productP R n) (y-o) < r ->
    A y /\ (@riemannian_distance R n A g o y < e%:E)%E.
Proof.
move=> he.
have hTwo : (1 < 2 :> R) by rewrite ltr1n.
have [L [d [hd [hL hComparison]]]] :=
  @riemannian_local_distance_comparison R n A g hg o ho 2 hTwo.
pose hE := @euclidean_inner_productP R n.
pose M := linear_operator_norm hE hE (@coordinate_basisP R n) L + 1.
have hM0 : 0 < M.
  have hOp := linear_operator_norm_nonnegative hE hE (@coordinate_basisP R n) L.
  rewrite /M; clear -hOp; lra.
have hFourM : 0 < 4*M by rewrite mulr_gt0 // ltr0n.
pose r := Order.min (d/(4*M)) (e/(4*M)).
have hr : 0 < r by rewrite /r lt_min !divr_gt0.
exists r; split; first exact hr.
move=> y hy.
have hNorm := inner_norm_nonnegative hE (y-o).
have hOpBound := linear_operator_norm_bound hE hE (@coordinate_basisP R n) L (y-o).
have hBound : inner_norm hE (L (y-o)) <= M * inner_norm hE (y-o).
  apply: le_trans hOpBound _; apply: ler_wpM2r; first exact hNorm.
  by rewrite /M lerDl ler01.
have hyD : inner_norm hE (y-o) < d/(4*M).
  apply: lt_le_trans hy _; by rewrite /r ge_min lexx.
have hyE : inner_norm hE (y-o) < e/(4*M).
  apply: lt_le_trans hy _; by rewrite /r ge_min lexx orbT.
have hScaleD : (4*M)*inner_norm hE (y-o) < d.
  by rewrite mulrC -ltr_pdivlMr.
have hScaleE : (4*M)*inner_norm hE (y-o) < e.
  by rewrite mulrC -ltr_pdivlMr.
have hNear : inner_norm hE (L (y-o)) <= d/2.
  clear -hBound hScaleD hd; nra.
have hCentre : inner_norm hE (L (o-o)) <= d/2.
  rewrite subrr linear0 inner_norm0; clear -hd; lra.
have hLocal := hComparison o y hCentre hNear.
split; first exact hLocal.2.1.
apply: le_lt_trans hLocal.2.2.2 _.
rewrite lte_fin; clear -hBound hScaleE he; nra.
Qed.

(** Source for [riemannian_distance_to_euclidean_neighbourhood]:
    the local lower comparison and positive first-exit cost prove
    that a small rho ball lies in each Euclidean neighbourhood,
    Federer 3.2.46, p. 281. The other endpoint is not assumed
    to lie in the comparison neighbourhood. *)
Lemma riemannian_distance_to_euclidean_neighbourhood (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) o (ho : A o) (e : R) :
  0 < e -> exists r : R, (0 < r < 1) /\ forall y,
    (@riemannian_distance R n A g o y < r%:E)%E ->
    inner_norm (@euclidean_inner_productP R n) (y-o) < e.
Proof.
move=> he.
have hTwo : (1 < 2 :> R) by rewrite ltr1n.
have hTwo0 : (0 < 2 :> R) by rewrite ltr0n.
have [L [d [hd [hL hComparison]]]] :=
  @riemannian_local_distance_comparison R n A g hg o ho 2 hTwo.
have [K [hK hInverse]] := positive_norm_factor_inverse_bound hL.
pose hE := @euclidean_inner_productP R n.
pose r := Order.min (1/2) (Order.min (d/4) (e/(2*K))).
have hTwoK : 0 < 2*K by rewrite mulr_gt0 // ltr0n.
have hr0 : 0 < r.
  by rewrite /r !lt_min !divr_gt0 // !ltr0n.
have hrHalf : r <= 1/2 by rewrite /r ge_min lexx.
have hr1 : r < 1 by apply: le_lt_trans hrHalf _; clear; lra.
have hrD : r <= d/4 by rewrite /r ge_min ge_min lexx orbT.
have hrE : r <= e/(2*K) by rewrite /r ge_min ge_min lexx !orbT.
exists r; split; first by apply/andP; split.
move=> y hSmall.
have hCentre : inner_norm hE (L (o-o)) <= d/2.
  rewrite subrr linear0 inner_norm0; clear -hd; lra.
have hLocal z : inner_norm hE (L (z-o)) <= d/2 ->
    ((((2 : R)^-1*inner_norm hE (L (z-o)))%R)%:E <=
      @riemannian_distance R n A g o z)%E.
  move=> hz; exact: (hComparison o z hCentre hz).2.2.1.
have hNear : inner_norm hE (L (y-o)) <= d/2.
  case: (leP (inner_norm hE (L (y-o))) (d/2))=> hy; first by [].
  have hHalf0 : 0 < d/2 by rewrite divr_gt0 // ltr0n.
  have hBarrier := @riemannian_distance_departure_lower R n A g hg L o y
    (d/2) ((2 : R)^-1) hHalf0 hLocal hy.
  have hContradiction := le_lt_trans hBarrier hSmall.
  rewrite lte_fin in hContradiction.
  clear -hContradiction hrD; lra.
have hLower := le_lt_trans (hLocal y hNear) hSmall.
rewrite lte_fin in hLower.
have hScale : (2*K)*r <= e by rewrite mulrC -ler_pdivlMr.
have hInv := hInverse (y-o).
clear -hLower hScale hInv hK; nra.
Qed.
