(** Federer (1969), 3.2.13, p. 250: supporting
    logarithm calculus for real-power primitives in Euler's
    Gamma recurrence. Derive the remainder from the existing
    opaque exponential/logarithm tangent laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP RealExponentialUP RealExponentialSealed
  RealExponentialLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_logarithm_quadratic_remainder]:
    supporting real-power differentiation in the integration
    by parts of Federer 3.2.13, p. 250.
    Both bounds follow from log x<=x-1 applied to
    1+t and its reciprocal; no external calculus is used. *)
Lemma real_logarithm_quadratic_remainder (R:realType) (t:R):
  `|t|<= 1/2 ->
  `|RealExponential.logarithm (1+t)-t|<= 2*t^+2.
Proof.
move=>ht.
have hLo:-(1/2)<=t by move:ht; rewrite ler_norml=>/andP[].
have hHi:t<= 1/2 by exact:le_trans (ler_norm t) ht.
have hOne:0<1+t by lra.
have hDen:1/2<= 1+t by lra.
have hUpper:=@real_logarithm_tangent R (1+t) hOne.
have hInvPos:0<(1+t)^-1 by rewrite invr_gt0.
have hInverse:=@real_logarithm_tangent R ((1+t)^-1) hInvPos.
rewrite real_logarithm_inverse // in hInverse.
have hProduct:=ler_wpM2l (ltW hOne) hInverse.
rewrite mulrBr mulfV ?(gt_eqF hOne) // mulr1 mulrN in hProduct.
rewrite ler0_norm; last by lra.
have hError:0<=t-RealExponential.logarithm (1+t) by lra.
have hScaled:=ler_wpM2r hError hDen.
rewrite expr2; nra.
Qed.

(** Source for [real_logarithm_linear_term]: the linear
    logarithm derivative needed for the real-power primitive
    in Federer 3.2.13, p. 250; supporting calculus. *)
Definition real_logarithm_linear_term (R:realType) (a:R):Hom R^o R^o.
Proof.
apply:(@HomMap R R^o R^o (fun h=>a^-1*h)).
apply/asboolP=>c x y; change (a^-1*(c*x+y)=c*(a^-1*x)+a^-1*y); ring.
Defined.

(** Source for [real_logarithm_differential]: actual
    logarithm differentiation on the positive domain, supporting
    the real-power integration by parts in Federer
    3.2.13, p. 250. The opaque logarithm's
    unspecified nonpositive values are never used in the proof. *)
Theorem real_logarithm_differential (R:realType) (a:R):
  0<a ->has_norm_differential (fun r:R^o=>`|r|) (fun r:R^o=>`|r|) setT
    (@RealExponential.logarithm R) a (real_logarithm_linear_term a).
Proof.
move=>ha.
have haNe:a!= 0:=lt0r_neq0 ha.
have hi:0<a^-1 by rewrite invr_gt0.
constructor.
- exists 1; split; first exact:ltr01; by move=>h hh.
- exists a^-1; split; first exact:ltW hi.
  move=>h; change (`|a^-1*h|<=a^-1*`|h|).
  by rewrite normrM gtr0_norm.
- move=>e he; pose d:=Num.min (a/2) (e*a^+2/2).
  have hTwo:(0:R)<2 by lra.
  have hD:0<d by rewrite /d lt_min; apply/andP; split; apply:divr_gt0=> //; exact:mulr_gt0 he (exprn_gt0 2 ha).
  exists d; split=> //; move=>h _ hSmall.
  have hHalf:`|h|<=a/2.
    apply:le_trans (ltW hSmall) _; by rewrite /d ge_min lexx.
  have hEps:`|h|<=e*a^+2/2.
    apply:le_trans (ltW hSmall) _; by rewrite /d ge_min lexx orbT.
  pose t:=h/a.
  have hT:`|t|<= 1/2.
    rewrite /t normrM (gtr0_norm hi).
    change (`|h|/a<=1/2).
    by rewrite ler_pdivrMr // mul1r mulrC.
  have hTLower:-(1/2)<=t by move:hT; rewrite ler_norml=>/andP[].
  have hOne:0<1+t by lra.
  have hAt:a*t=h by rewrite /t mulrC divfK.
  have hFactor:a*(1+t)=a+h by rewrite mulrDr mulr1 hAt.
  have hLog:RealExponential.logarithm (a+h)=
      RealExponential.logarithm a+RealExponential.logarithm (1+t).
    by rewrite -hFactor real_logarithm_product.
  have hLinear:real_logarithm_linear_term a h=t by change (a^-1*h=h/a); rewrite mulrC.
  have hRem:RealExponential.logarithm (a+h)-RealExponential.logarithm a-
      real_logarithm_linear_term a h=RealExponential.logarithm (1+t)-t.
    rewrite hLog hLinear; ring.
  rewrite hRem.
  apply:le_trans (real_logarithm_quadratic_remainder hT) _.
  have hSquare:t^+2*a^+2=h^+2 by rewrite -exprMn /t divfK.
  have hProd:=ler_wpM2r (normr_ge0 h) hEps.
  have hNorm:`|h|^+2=h^+2 by rewrite -normrX ger0_norm ?sqr_ge0.
  rewrite -(ler_pM2r (exprn_gt0 2 ha)) -mulrA hSquare -hNorm.
  nra.
Qed.
