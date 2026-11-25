(** Federer (1969), 3.3.19, p. 305: a uniform
    positive cosine gap controls original cap half-angle
    perturbations independently of the original orientation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularUnitVectors CircularSineOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Gaps.
Variable R:realType.
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_sine_semicircle_reflection]: the
    exact sin(pi-x)= sin(x) identity supporting uniform
    cap comparison in 3.3.19, p. 305. *)
Lemma circular_sine_semicircle_reflection x:S (p-x)= S x.
Proof.
by rewrite (circular_trig_sine_add ht) (real_sine_odd hb)
  (circular_trig_sine_pi ht) (circular_trig_cosine_pi ht)
  mul0r add0r mulN1r opprK.
Qed.

(** Source for [circular_sine_symmetric_interval_lower]:
    sine on [h,pi-h] is at least sin(h), supporting
    the uniform cap perturbation in 3.3.19, p. 305. *)
Lemma circular_sine_symmetric_interval_lower (h x:R):
  0<=h ->h<=p/2 ->h<=x ->x<=p-h ->S h<=S x.
Proof.
move=>hh hhP hxLeft hxRight.
case:(leP x (p/2))=>hxHalf.
- exact:(@circular_sine_weak_increase R h x hh hxLeft hxHalf).
- have hReflection:S (p-x)= S x:= circular_sine_semicircle_reflection x.
  rewrite -hReflection.
  have hLower:h<=p-x by lra.
  have hUpper:p-x<=p/2 by lra.
  exact:(@circular_sine_weak_increase R h (p-x) hh hLower hUpper).
Qed.

(** Source for [circular_cosine_increment_identity]: exact
    difference of actual cosines, used in the uniform
    cap estimate in 3.3.19, p. 305. *)
Lemma circular_cosine_increment_identity (t e:R):
  C t-C (t+e)= 2* S (t+e/2)* S (e/2).
Proof.
have hLeft:(t+e/2)-e/2= t by field.
have hRight:(t+e/2)+e/2= t+e by field.
have hIdentity:C ((t+e/2)-e/2)-C ((t+e/2)+e/2)= 2* S (t+e/2)* S (e/2).
  rewrite (@circular_cosine_difference R (t+e/2) (e/2))
    (circular_trig_cosine_add ht (t+e/2) (e/2)).
  ring.
by rewrite hLeft hRight in hIdentity.
Qed.

(** Source for [circular_cosine_uniform_gap]: for a fixed
    positive half-angle increment e<pi, the original
    cosine drops by at least 2 sin(e/2)^2 uniformly
    for 0<=gamma<=pi-e. This proves uniform cap-angle
    control required in 3.3.19, p. 305 without
    assuming an inverse-cosine continuity modulus. *)
Theorem circular_cosine_uniform_gap (e gamma:R):
  0<e ->e<p ->0<=gamma ->gamma<=p-e ->
  0<2*(S (e/2))^+2 /\2*(S (e/2))^+2<=C gamma-C (gamma+e).
Proof.
move=>he hep hGamma hGammaP.
have hp:= real_trigonometry_pi_positive hb.
have hHalf:0<e/2 by lra.
have hHalfP:e/2<p by lra.
have hSine:= @circular_trig_sine_positive R S C (@CircularTrigonometry.arcsine R)
  (@CircularTrigonometry.arccosine R) p ht (e/2) hHalf hHalfP.
have hHalfUpper:e/2<=p/2 by lra.
have hInsideLeft:e/2<=gamma+e/2 by lra.
have hInsideRight:gamma+e/2<=p-e/2 by lra.
have hLower:= @circular_sine_symmetric_interval_lower (e/2) (gamma+e/2)
  (ltW hHalf) hHalfUpper hInsideLeft hInsideRight.
split;first by nra.
rewrite circular_cosine_increment_identity.
have hProduct:= ler_wpM2r (ltW hSine) hLower;nra.
Qed.
End Gaps.
