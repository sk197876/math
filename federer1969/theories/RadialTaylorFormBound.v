(** Supporting Federer (1969), 3.4.8(5), p. 328:
    the radial Taylor quotient retains an analytic
    factorial-growth bound. The original contraction
    estimate of 3.1.14, p. 226, is used with
    one contracted argument, as in 1.10.4, p. 46. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal ring.
From Federer Require Import Hom RealNormUP SymmetricForms PolynomialTaylorTerms
  PolynomialTaylorTermContinuity SymmetricOperatorNorm WhitneyPolynomialDifferenceBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [radial_taylor_factorial_cancellation]: the
    divisor m+1 cancels the successor factorial in
    the Taylor-growth estimate, supporting the expanded
    closedness proof for 3.4.8(5), p. 328. *)
Lemma radial_taylor_factorial_cancellation (R:realType) (S T V:R) m:
  ((m.+1)%:R:R)^-1*(S*T^+m.+1*((m.+1)`!)%:R*V) =
    (S*T*V)*T^+m*(m`!)%:R.
Proof.
have hNonzero:((m.+1)%:R:R)!=0 by rewrite pnatr_eq0.
rewrite factS natrM exprS.
transitivity ((((m.+1)%:R:R)^-1*(m.+1)%:R)*((S*T*V)*T^+m*(m`!)%:R));first ring.
by rewrite mulVf // mul1r.
Qed.

(** Source for [radial_taylor_form_factorial_bound]: an
    original all-order bound S T^m m! gives the
    quotient bound S T |v| T^m m!. This
    proves the analytic-growth condition for the actual
    radial quotient, supporting 3.4.8(5), p. 328. *)
Theorem radial_taylor_form_factorial_bound (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) (phi:forall m,S_m X R^o m) (S T:R) (v:X):
  0<=S ->0<=T ->
  (forall m,(symmetric_operator_norm hNX.1 (fun z:R^o=>`|z|%R) (phi m)
    <=(S*T^+m*(m`!)%:R)%:E)%E) ->
  forall m,(symmetric_operator_norm hNX.1 (fun z:R^o=>`|z|%R)
    (((m.+1)%:R:R)^-1*:symmetric_taylor_term m (phi m.+1) v)
    <=((S*T*NX v)*T^+m*(m`!)%:R)%:E)%E.
Proof.
move=>hS hT hBound m.
pose NS:=fun z:R^o=>`|z|%R.
pose hNS:=@scalar_absolute_value_norm R.
pose L:=S*T^+m.+1*((m.+1)`!)%:R.
have hContraction:=@symmetric_taylor_term_operator_bound R X R^o NX NS hNX hNS
  m.+1 m (leqnSn m) (phi m.+1) v L (hBound m.+1).
have hSmall:(m.+1-m)%N = 1%N by rewrite subSn // subnn.
rewrite hSmall expr1 /= divr1 in hContraction.
apply:(symmetric_operator_norm_bound hNX.1 NS _ _).2=>u hu.
rewrite sform_scaleE.
change (`|((m.+1)%:R:R)^-1*(symmetric_taylor_term m (phi m.+1) v u)|%R
  <=(S*T*NX v)*T^+m*(m`!)%:R).
rewrite normrM normfV normr_nat.
have hInv:0<=((m.+1)%:R:R)^-1 by rewrite invr_ge0 ler0n.
have hPoint:=(symmetric_operator_norm_bound hNX.1 NS _ _).1 hContraction u hu.
have hFinal:=ler_wpM2l hInv hPoint.
by rewrite /L radial_taylor_factorial_cancellation in hFinal.
Qed.
