(** Federer (1969), 3.4.12, p. 339, extending the
    ideal-closedness argument of 3.4.8(5), p. 328: radial
    Taylor quotients retain factorial growth for arbitrary normed
    targets. Reuse the original contraction bound and already proved
    scalar factorial cancellation; add only the normed target connection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP SymmetricForms PolynomialTaylorTerms PolynomialTaylorTermContinuity
  SymmetricOperatorNorm WhitneyPolynomialDifferenceBound RadialTaylorFormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_radial_taylor_form_factorial_bound]: the
    original bound S*T^m*m! gives the quotient bound
    S*T*|v|*T^m*m!, extending the supporting Taylor estimate
    for 3.4.8(5), p. 328. No scalar-valued target restriction remains. *)
Theorem norm_radial_taylor_form_factorial_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (phi:forall m,S_m X Y m) (S T:R) (v:X):
  0<=S ->0<=T ->
  (forall m,(symmetric_operator_norm hNX.1 NY (phi m)<=(S*T^+m*(m`!)%:R)%:E)%E) ->
  forall m,(symmetric_operator_norm hNX.1 NY
    (((m.+1)%:R:R)^-1*:symmetric_taylor_term m (phi m.+1) v)<=
      ((S*T*NX v)*T^+m*(m`!)%:R)%:E)%E.
Proof.
move=>hS hT hBound m.
pose L:=S*T^+m.+1*((m.+1)`!)%:R.
have hContraction:=@symmetric_taylor_term_operator_bound R X Y NX NY hNX hNY
  m.+1 m (leqnSn m) (phi m.+1) v L (hBound m.+1).
have hSmall:(m.+1-m)%N = 1%N by rewrite subSn // subnn.
rewrite hSmall expr1 /= divr1 in hContraction.
apply:(symmetric_operator_norm_bound hNX.1 NY _ _).2=>u hu.
rewrite sform_scaleE (real_seminorm_scale hNY.1) normfV normr_nat.
have hInv:0<=((m.+1)%:R:R)^-1 by rewrite invr_ge0 ler0n.
have hPoint:=(symmetric_operator_norm_bound hNX.1 NY _ _).1 hContraction u hu.
have hFinal:=ler_wpM2l hInv hPoint.
by rewrite /L radial_taylor_factorial_cancellation in hFinal.
Qed.
