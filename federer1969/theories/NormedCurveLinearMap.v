(** Federer (1969), 3.1.1(2), p. 210, and the norm derivative
    of 2.9.22, p. 167: applying a continuous linear map commutes
    with the actual curve derivative. This supports the frozen
    maps L composed with C in 3.2.46, p. 281. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [punctured_norm_limit_bounded_linear]: continuous
    linear maps preserve the actual norm limits of 2.9.22,
    p. 167, supporting the length comparison in Federer 3.2.46,
    p. 281. Zero operator bounds are included. *)
Lemma punctured_norm_limit_bounded_linear (R : realType)
    (E F : lmodType R) (NX : E -> R) (NY : F -> R)
    (hNX : is_real_norm NX) (L : Hom E F) (u : R -> E) v :
  norm_bounded_linear NX NY L -> punctured_norm_limit NX u v ->
  punctured_norm_limit NY (fun h=>L (u h)) (L v).
Proof.
move=> [K [hK hBound]] hLimit e he.
have hK1 : 0 < K+1 by lra.
have hE : 0 < e/(K+1) by rewrite divr_gt0.
have [d [hd hControl]] := hLimit (e/(K+1)) hE.
exists d; split=> // h hh.
have hUpper := hBound (u h-v); rewrite linearB in hUpper.
have hInc : K <= K+1 by lra.
have hUpper' := le_trans hUpper
  (ler_wpM2r (real_seminorm_nonnegative hNX.1 (u h-v)) hInc).
have hSmall : (K+1)*NX (u h-v) < (K+1)*(e/(K+1)).
  by rewrite (ltr_pM2l hK1); exact: hControl.
have hCancel : (K+1)*(e/(K+1)) = e.
  by rewrite mulrC (divfK (lt0r_neq0 hK1)).
rewrite hCancel in hSmall; exact: le_lt_trans hUpper' hSmall.
Qed.

(** Source for [normed_curve_derivative_linear_image]: the
    actual derivative of L composed with C is L(C'), used to
    compare the integrals with Euclidean length in Federer
    3.2.46, p. 281. This implication needs no invertibility. *)
Lemma normed_curve_derivative_linear_image (R : realType)
    (E F : lmodType R) (NX : E -> R) (NY : F -> R)
    (hNX : is_real_norm NX) (L : Hom E F) (C : R -> E) x v :
  norm_bounded_linear NX NY L -> has_normed_curve_derivative NX C x v ->
  has_normed_curve_derivative NY (fun t=>L (C t)) x (L v).
Proof.
move=> hL hC.
have hLimit := punctured_norm_limit_bounded_linear hNX hL hC.
have he : (fun h=>L (h^-1 *: (C (x+h)-C x))) =
    (fun h=>h^-1 *: (L (C (x+h))-L (C x))).
  by apply: funext=> h; rewrite linearZ linearB.
by rewrite he in hLimit.
Qed.
