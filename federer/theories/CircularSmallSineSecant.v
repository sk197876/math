(** Federer (1969), 3.3.19, p. 306: local
    tangential coordinates of the original circular
    child centres have nearly unit scalar slope. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring.
From Federer Require Import RealCurveDerivativeUP RealDerivativeIncrementBounds RealTrigonometryUP
  CircularTrigonometryUP CircularTrigonometrySealed CircularScalarLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Secants.
Variable R:realType.
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_sine_difference_identity]: actual
    sine increments equal 2cos((a+b)/2)sin((b-a)/2),
    supporting the final circular child packing in
    3.3.19, p. 306. *)
Lemma circular_sine_difference_identity (a b:R):
  S b-S a= 2* C ((a+b)/2)* S ((b-a)/2).
Proof.
pose m:=(a+b)/2.
pose q:=(b-a)/2.
have hB:m+q= b by rewrite /m /q;field.
have hA:m-q= a by rewrite /m /q;field.
have hSB:S b= S m*C q+C m*S q by rewrite -hB (circular_trig_sine_add ht).
have hSA:S a= S m*C q-C m*S q.
  rewrite -hA (circular_trig_sine_add ht) (real_sine_odd hb) (circular_trig_cosine_even ht);ring.
rewrite hSB hSA -/m -/q;ring.
Qed.

(** Source for [circular_small_sine_secant]: for every
    0<kappa<1, a proved positive angular window gives
    S(b)-S(a)>=kappa(b-a) for all ordered a,b in
    that window. Actual sine derivative at zero and the
    proved cosine contraction give a uniform secant bound,
    supporting 3.3.19, p. 306 without an imported
    mean-value or numerical trigonometric theorem. *)
Theorem circular_small_sine_secant (kappa:R):
  0<kappa ->kappa<1 ->exists d:R,0<d /\forall a b:R,
    `|a|<=d ->`|b|<=d ->a<=b ->kappa*(b-a)<=S b-S a.
Proof.
move=>hk hk1.
pose e:=(1-kappa)/4.
have he:0<e by rewrite /e;lra.
have he1:e<1 by rewrite /e;lra.
have hOne:0<1-e by lra.
have hCoefficient:kappa<=(1-e)^+2 by rewrite /e;nra.
have hDerivative:= real_sine_derivative hb 0.
rewrite (real_cosine_zero hb) in hDerivative.
have [d0 [hd0 hApprox]]:= @real_derivative_small_displacement_error R S 0 1 e hDerivative he.
pose d:= Num.min (d0/2) e.
have hHalf:0<d0/2 by lra.
have hd:0<d by rewrite /d lt_min hHalf he.
have hWindowBound:d<=d0/2 by rewrite /d ge_min lexx.
have hde:d<=e by rewrite /d ge_min lexx orbT.
exists d;split=>// a b ha hbnd hab.
have /andP[hAL hAR]:(-d<=a<=d) by rewrite -ler_norml.
have /andP[hBL hBR]:(-d<=b<=d) by rewrite -ler_norml.
pose m:=(a+b)/2.
pose q:=(b-a)/2.
have hq:0<=q by rewrite /q;lra.
have hqd:q<=d by rewrite /q;lra.
have hm:`|m|<=d by rewrite ler_norml;apply/andP;split;rewrite /m;lra.
have hSmall:`|q|<d0 by rewrite (ger0_norm hq);lra.
have hApproxQ:= hApprox q hSmall.
rewrite add0r (real_sine_zero (circular_trig_basic ht)) subr0 mul1r
  (ger0_norm hq) ler_norml in hApproxQ.
have /andP[hApproxLower _]:= hApproxQ.
have hSine:(1-e)* q<=S q by nra.
have hCosBound:= @circular_cosine_nonexpanding R m 0.
rewrite (real_cosine_zero (circular_trig_basic ht)) subr0 in hCosBound.
have hCosNorm:`|C m-1|<=e:= le_trans hCosBound (le_trans hm hde).
have /andP[hCL _]:(-e<=C m-1<=e) by rewrite -ler_norml.
have hCos:1-e<=C m by lra.
have hCPositive:0<C m:= lt_le_trans hOne hCos.
have hProduct1:= ler_wpM2l (ltW hCPositive) hSine.
have hProduct2:= ler_wpM2r (mulr_ge0 (ltW hOne) hq) hCos.
have hProduct3:= ler_wpM2r hq hCoefficient.
rewrite circular_sine_difference_identity -/m -/q.
have hWidth:b-a= 2* q by rewrite /q;field.
rewrite hWidth;nra.
Qed.
End Secants.
