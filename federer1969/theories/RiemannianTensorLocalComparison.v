(** Federer (1969), 3.2.46, printed p. 281: the actual tensor
    norm near a is uniformly comparable to |L(v)|. State the radius
    in L-coordinates, so the entire closed comparison ellipsoid lies
    in A. The axes, inverse and radius are local existence witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm RiemannianTensorUP PositiveSymmetricNormFactor
  PositiveNormFactorBound RiemannianScalarComparison NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_tensor_local_comparison]: the first
    lambda estimate in Federer 3.2.46, p. 281. Every direction v
    is controlled on one actual closed ellipsoid contained in A;
    L is proved to be the positive symmetric frozen norm factor.
    This includes dimension zero and the zero vector. *)
Theorem riemannian_tensor_local_comparison (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) a (ha : A a) (l : R) :
  1 < l -> exists L : {linear R_n R n -> R_n R n}, exists d : R,
    0 < d /\ is_positive_symmetric_norm_factor (riemannian_tensor_inner hg ha) L /\
    forall x, inner_norm (@euclidean_inner_productP R n) (L (x-a)) <= d ->
      A x /\ forall v,
        l^-1 * inner_norm (@euclidean_inner_productP R n) (L v) <=
          riemannian_tensor_speed g x v /\
        riemannian_tensor_speed g x v <=
          l * inner_norm (@euclidean_inner_productP R n) (L v).
Proof.
move=> hl.
pose hE := @euclidean_inner_productP R n.
pose N := inner_norm hE.
pose hB := riemannian_tensor_inner hg ha.
have [L hL] := positive_symmetric_norm_factor_exists hB.
have [K [hK hInv]] := positive_norm_factor_inverse_bound hL.
pose eta := Order.min (l^+2-1) (1-l^-1^+2).
have hEta : 0 < eta := riemannian_comparison_error_positive hl.
pose e := eta/(K^+2).
have he : 0 < e by rewrite /e divr_gt0 // exprn_gt0.
have hKsq : 0 < K^+2 by nra.
have hKsqne : K^+2 != 0 := lt0r_neq0 hKsq.
have hBudget : e*K^+2 = eta by rewrite /e (divfK hKsqne).
have [rG [hrG hControl]] := (@riemannian_tensor_continuous R n A g hg a ha e he).
have [rA [hrA hDomain]] := (@riemannian_tensor_domain_open R n A g hg a ha).
pose r := Order.min rG rA.
have hr : 0 < r by rewrite /r lt_min hrG hrA.
have h2 : (0 < 2 :> R) by rewrite ltr0n.
pose d := r/(2*K).
have hd : 0 < d by rewrite /d divr_gt0 // mulr_gt0.
have hDenNe : 2*K != 0 := lt0r_neq0 (mulr_gt0 h2 hK).
have hDen : d*(2*K) = r by rewrite /d (divfK hDenNe).
exists L,d; split=> //; split=> //.
move=> x hx.
have hOrd : N (x-a) < r.
  have hBound := hInv (x-a).
  have hScaled := ler_wpM2l (ltW hK) hx.
  have hStrict : K*d < r by nra.
  exact: le_lt_trans (le_trans hBound hScaled) hStrict.
have hRG : r <= rG by rewrite /r ge_min lexx.
have hRA : r <= rA by rewrite /r ge_min lexx orbT.
have hEq : a+(x-a) = x by rewrite addrC subrK.
have hxA : A x.
  rewrite -hEq; exact: hDomain (x-a) (lt_le_trans hOrd hRA).
split=> // v.
have hNE : 0 <= N v := inner_norm_nonnegative hE v.
have hNL : 0 <= N (L v) := inner_norm_nonnegative hE (L v).
have hIv := hInv v.
have hSq : (N v)^+2 <= K^+2*(N (L v))^+2.
  rewrite -exprMn (ler_sqr hNE (mulr_ge0 (ltW hK) hNL)).
  exact hIv.
have hScaled := ler_wpM2l (ltW he) hSq.
rewrite (mulrA e (K^+2) ((N (L v))^+2)) hBudget in hScaled.
have hControlX := hControl (x-a) ltac:(by rewrite hEq)
  (lt_le_trans hOrd hRG) v v.
rewrite hEq -(mulrA e (N v) (N v)) -(expr2 (N v)) in hControlX.
have hRaw : `|g x v v-g a v v| <= eta*(N (L v))^+2 :=
  le_trans hControlX hScaled.
have hSourceSquare : (N (L v))^+2 = g a v v.
  by rewrite /N /hE (positive_norm_factor_norm hL) inner_norm_sqr.
have hTargetSquare : (riemannian_tensor_speed g x v)^+2 = g x v v.
  by rewrite (riemannian_tensor_speed_inner_norm hg hxA) inner_norm_sqr.
have hError : `|(riemannian_tensor_speed g x v)^+2-(N (L v))^+2| <=
    eta*(N (L v))^+2.
  rewrite hTargetSquare {1}hSourceSquare; exact hRaw.
exact: riemannian_quadratic_error_comparison hl hNL
  (riemannian_tensor_speed_nonnegative g x v) hError.
Qed.
