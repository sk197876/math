(** Federer (1969), 3.2.7, p. 246, third
    example: rewrite the printed curve through the
    signed square root. The auxiliary parameter
    F(t)=t^3 sin((t^2)^-1) has bounded derivatives
    on bounded intervals, including actual derivative zero
    at zero. All scalar trigonometry remains opaque. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import RealCurveDerivativeUP RealCurveDerivativeAlgebra RealCurvePolynomialDerivatives
  RealTrigonometryUP RealTrigonometrySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [cubic_oscillation_parameter]: supporting
    change of parameter F in the third example of
    Federer 3.2.7, p. 246. Its formula
    defines zero at zero without any derivative default. *)
Definition cubic_oscillation_parameter (R:realType) (t:R):R:=
  t^+3*RealTrigonometry.sine ((t^+2)^-1).

(** Source for [cubic_oscillation_zero]: supporting centre
    value in the third example of Federer 3.2.7, p. 246. *)
Lemma cubic_oscillation_zero (R:realType):@cubic_oscillation_parameter R 0= 0.
Proof. by rewrite /cubic_oscillation_parameter expr0n mul0r. Qed.

(** Source for [cubic_oscillation_derivative_zero]: the
    reparameterized curve has actual derivative zero
    at zero, supporting Federer 3.2.7, p. 246.
    The bounded sine gives a quotient of order t^2. *)
Lemma cubic_oscillation_derivative_zero (R:realType):
  has_real_curve_derivative (@cubic_oscillation_parameter R) 0 0.
Proof.
move=>e he; exists (Num.min 1 e); split; first by rewrite lt_min ltr01 he.
move=>h /andP[hh hSmall].
have h0:h!= 0 by rewrite -normr_gt0.
have hh1:`|h|<= 1 by apply:le_trans (ltW hSmall) _; rewrite ge_min lexx.
have hhe:`|h|<e by apply:lt_le_trans hSmall _; rewrite ge_min lexx orbT.
have hEq:(cubic_oscillation_parameter h-cubic_oscillation_parameter 0)/h=
    h^+2*RealTrigonometry.sine ((h^+2)^-1).
  rewrite cubic_oscillation_zero /cubic_oscillation_parameter subr0 !exprS expr0.
  by field; rewrite (negbTE h0).
rewrite add0r subr0 hEq normrM normrX.
have hS:=real_sine_bound (@RealTrigonometry.laws R) ((h^+2)^-1).
have hB:=ler_wpM2l (exprn_ge0 2 (normr_ge0 h)) hS.
rewrite mulr1 in hB.
have hSquare:`|h|^+2<=`|h|.
  rewrite expr2; have hhB:=ler_wpM2l (normr_ge0 h) hh1; by rewrite mulr1 in hhB.
exact (le_lt_trans hB (le_lt_trans hSquare hhe)).
Qed.

(** Source for [cubic_oscillation_derivative_nonzero]: the
    actual derivative 3t^2 sin(t^-2)-2cos(t^-2),
    supporting the third example of Federer 3.2.7,
    p. 246. Nonzero t is used only to
    simplify the reciprocal coefficient algebraically. *)
Theorem cubic_oscillation_derivative_nonzero (R:realType) (t:R):
  t!= 0 -> has_real_curve_derivative (@cubic_oscillation_parameter R) t
    (3*t^+2*RealTrigonometry.sine ((t^+2)^-1)-2*RealTrigonometry.cosine ((t^+2)^-1)).
Proof.
move=>ht.
have hSquare:=@real_curve_power_actual_derivative R t 2.
have hT2:t^+2!= 0 by rewrite expf_neq0.
have hInverse:=real_curve_reciprocal_actual_derivative hT2.
have hArg:=real_curve_derivative_compose hSquare hInverse.
have hSine:=real_curve_derivative_compose hArg
  (real_sine_derivative (@RealTrigonometry.laws R) ((t^+2)^-1)).
have hCube:=@real_curve_power_actual_derivative R t 3.
have hProduct:=real_curve_derivative_product hCube hSine.
change (has_real_curve_derivative (@cubic_oscillation_parameter R) t
  ((3%:R*t^+2)*RealTrigonometry.sine ((t^+2)^-1)+
    t^+3*(((2%:R*t^+1)*(-(((t^+2)^-1)^+2)))*RealTrigonometry.cosine ((t^+2)^-1)))) in hProduct.
have hCoeff:(3%:R*t^+2)*RealTrigonometry.sine ((t^+2)^-1)+
    t^+3*(((2%:R*t^+1)*(-(((t^+2)^-1)^+2)))*RealTrigonometry.cosine ((t^+2)^-1))=
    3*t^+2*RealTrigonometry.sine ((t^+2)^-1)-2*RealTrigonometry.cosine ((t^+2)^-1).
  rewrite !exprS expr0; by field; rewrite (negbTE ht).
by rewrite hCoeff in hProduct.
Qed.
