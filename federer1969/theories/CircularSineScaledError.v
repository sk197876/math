(** Federer (1969), 3.3.19, p. 302: actual
    small-angle approximation for the printed coefficient
    (n-1)sin(pi/n). Derive a uniform error bound
    from the actual sine derivative at zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import RealCurveDerivativeUP RealDerivativeIncrementBounds
  RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Error.
Variable R:realType.
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_sine_scaled_error]: for every
    positive error there is an actual positive angle
    cutoff controlling the printed coefficient, supporting
    the lambda choice in 3.3.19, p. 302.
    The actual derivative supplies the cutoff; no
    asymptotic trigonometric identity is assumed. *)
Theorem circular_sine_scaled_error (e:R):0<e ->exists d:R,0<d /\
  forall (v x:R),1<=v ->0<x ->x<d ->v* x=p ->
    `|(v-1)* S x-p|<e.
Proof.
move=>he.
have hp:=real_trigonometry_pi_positive hb.
have hpN:p!= 0 by rewrite gt_eqF.
pose eps:R:=e/(4* p).
have hDenominator:0<4* p by nra.
have hEps:0<eps by rewrite /eps divr_gt0.
have hD:=real_sine_derivative hb 0.
rewrite (real_cosine_zero hb) in hD.
have [d [hd hError]]:=@real_derivative_small_displacement_error R S 0 1 eps hD hEps.
pose eta:R:=Num.min d (e/4).
have hQuarter:0<e/4 by rewrite divr_gt0 // ltr0n.
have hEta:0<eta by rewrite /eta lt_min hd hQuarter.
exists eta;split=>//;move=>v x hv hx hxEta hBudget.
have hEtaD:eta<=d by rewrite /eta ge_min lexx.
have hEtaE:eta<=e/4 by rewrite /eta ge_min lexx orbT.
have hNorm:`|x|=x:=ger0_norm (ltW hx).
have hxD:`|x|<d by rewrite hNorm;exact:lt_le_trans hxEta hEtaD.
have hApprox:=hError x hxD.
rewrite add0r (real_sine_zero hb) subr0 mul1r (ger0_norm (ltW hx)) in hApprox.
have hNonnegative:0<=v-1 by lra.
have hScaled:=ler_wpM2l hNonnegative hApprox.
have hIdentity:(v-1)* S x-p=(v-1)*(S x-x)-x by nra.
have hTriangle:=ler_normB ((v-1)*(S x-x)) x.
rewrite normrM (ger0_norm hNonnegative) (ger0_norm (ltW hx)) in hTriangle.
have hBudget2:(v-1)* x=p-x by nra.
have hErrorBound:(v-1)*(eps* x)<=eps* p by nra.
have hNormalization:eps* p=e/4.
  rewrite /eps invfM.
  have hEq:e*(4^-1* p^-1)* p=(e/4)*(p* p^-1) by ring.
  by rewrite hEq mulfV // mulr1.
rewrite hNormalization in hErrorBound.
rewrite hIdentity;have hh:=le_trans hTriangle (lerD hScaled (lexx x));lra.
Qed.
End Error.
