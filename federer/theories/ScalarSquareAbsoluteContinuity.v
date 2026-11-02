(** Federer (1969), 3.2.13, p. 250: the
    square change of variables for the defining
    Gamma integral. Local absolute continuity follows
    from an explicit interval Lipschitz bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra ring.
From Federer Require Import RealMetricBackground ScalarIntervalLipschitzAbsoluteContinuity LocallyAbsolutelyContinuousCurve
  RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_square_actual_derivative]: the
    derivative of y^2 used in the
    Gamma square substitution, Federer 3.2.13,
    p. 250, from its actual difference quotient. *)
Lemma scalar_square_actual_derivative (R:realType) (a:R):
  has_real_curve_derivative (fun x:R=>x^+2) a (2*a).
Proof.
move=>e he; exists e; split=>// h /andP[hPos hSmall].
have hNe:h!= 0 by rewrite -normr_gt0.
have hEq:((a+h)^+2-a^+2)/h-2*a=h by rewrite !expr2; field; rewrite (negbTE hNe).
by rewrite hEq.
Qed.

(** Source for [scalar_square_locally_absolutely_continuous]: the
    square map satisfies the local absolute-continuity
    hypothesis for the Gamma substitution, Federer
    3.2.13, p. 250. Its interval
    bound is proved directly from the factorization
    x^2-y^2=(x-y)(x+y). *)
Lemma scalar_square_locally_absolutely_continuous (R:realType):
  is_locally_absolutely_continuous_curve (fun x:real_line_metric R=>(x^+2:real_line_metric R)).
Proof.
move=>a b hab.
pose M:=`|a|+`|b|+1.
have hM:0<M by rewrite /M; have:=normr_ge0 a; have:=normr_ge0 b; lra.
apply:(@scalar_interval_lipschitz_absolute_continuity R (fun x=>x^+2) (2*M) a b).
- nra.
- move=>x y /andP[hax hxb] /andP[hay hyb].
  have hBound z:a<=z ->z<=b ->`|z|<=M.
    move=>haz hzb; rewrite ler_norml; apply/andP; split;
    have hA:=ler_norm (-a); rewrite normrN in hA;
    have hB:=ler_norm b; rewrite /M; have:=normr_ge0 a; have:=normr_ge0 b; lra.
  have hx:=hBound x hax hxb; have hy:=hBound y hay hyb.
  have hCoefficient:`|x|+`|y|<=2*M by lra.
  have hSum:`|x+y|<=2*M:=le_trans (ler_normD x y) hCoefficient.
  have hFactor:x^+2-y^+2=(x-y)*(x+y) by rewrite !expr2; ring.
  rewrite hFactor normrM [2*M*`|x-y|]mulrC.
  exact (ler_wpM2l (normr_ge0 (x-y)) hSum).
Qed.
