(** Federer (1969), 3.3.19, p. 305: supporting actual
    angular width of each original child disc, used in the
    late-direction count and uniform cap comparison. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularCosineReflection CircularSineOrder CircularSineEndpointChord.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Angle.
Variable R:realType.
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_radial_angle_bound]: after division by
    the actual child radius, an original child-disc point
    has positive radial coordinate d and squared distance
    at most one from (n-1) exp(i t). Its angular deviation
    from t is strictly less than pi/(2n). This supplies the
    finite angular count in 3.3.19, p. 305; the scalar
    premise is the literal expanded original disc inequality. *)
Theorem circular_radial_angle_bound n (d t:R):
  (4<=n)%N ->0<d -> -p<=t ->t<=p ->
  d^+2+(n%:R-1)^+2-2* d*(n%:R-1)* C t<=1 ->
  `|t|<p/(2* n%:R).
Proof.
move=>hn hd htLower htUpper hDistance.
have hp:= real_trigonometry_pi_positive hb.
have hN4:(4<=n%:R:>R) by rewrite ler_nat.
have hNP:(0<n%:R:>R) by lra.
pose v:R:= n%:R-1.
have hv:0<v by rewrite /v;lra.
have hvN:v!=0 by rewrite gt_eqF.
have hInverse:0<v^-1 by rewrite invr_gt0.
have hCancel:v* v^-1= 1 by rewrite mulfV.
change (is_true (d^+2+v^+2-2* d* v* C t<=1)) in hDistance.
have hCosPositive:0<C t.
  have hNonnegative:= sqr_ge0 d.
  have hv3:3<=v by rewrite /v;lra.
  case:(ltP 0 (C t))=>// hNotPositive.
  have hProduct:= ler_wpM2l (mulr_ge0 (ltW hd) (ltW hv)) hNotPositive.
  rewrite mulr0 in hProduct.
  nra.
have hAbsNonnegative:0<=`|t| := normr_ge0 t.
have hAbsBound:`|t|<=p by rewrite ler_norml;apply/andP;split;lra.
have hCosAbs:C `|t|= C t.
  case:(leP 0 t)=>ht0.
  - by rewrite ger0_norm.
  - by rewrite (ltr0_norm ht0) (circular_trig_cosine_even ht).
have hAbsHalf:`|t|<p/2.
  case:(ltP `|t| (p/2))=>// hNotHalf.
  have hHalfNonnegative:0<=p/2 by lra.
  have hCos:= @circular_cosine_weak_decrease R (p/2) `|t| hHalfNonnegative hNotHalf hAbsBound.
  rewrite circular_cosine_quarter_turn hCosAbs in hCos;exfalso;lra.
have hSquare:= sqr_ge0 (d-v* C t).
have hUnit:= congr1 (fun x:R=>v^+2* x) (circular_trig_unit ht t).
have hSinBudget:(v* S t)^+2<=1 by rewrite exprMn;nra.
have hSinAbs:(S `|t|)^+2=(S t)^+2.
  case:(leP 0 t)=>ht0.
  - by rewrite ger0_norm.
  - by rewrite (ltr0_norm ht0) (real_sine_odd hb) sqrrN.
have hSinAbsBudget:(v* S `|t|)^+2<=1 by rewrite exprMn hSinAbs -exprMn.
pose a:R:= p/(2* n%:R).
have ha:0<a by rewrite /a divr_gt0 // mulr_gt0 // ltr0n.
have haHalf:a<=p/2.
  have hInv:(0<(n%:R:R)^-1) by rewrite invr_gt0.
  have hNN:(n%:R:R)!=0 by rewrite gt_eqF.
  have hNCancel:(n%:R:R)* n%:R^-1= 1 by rewrite mulfV.
  have hInvBound:(n%:R:R)^-1<=1 by nra.
  rewrite /a invfM;nra.
case:(ltP `|t| a)=>// hNotSmall.
have hSine:= @circular_sine_weak_increase R a `|t| (ltW ha) hNotSmall (ltW hAbsHalf).
have hStrict:= @circular_sine_half_step_strict R n hn.
change (is_true (v^-1<S a)) in hStrict.
have hScaled:= ltr_pM2l hv.
have hProductStrict:1<v* S a by rewrite -hCancel hScaled.
have hProductWeak:= ler_wpM2l (ltW hv) hSine.
nra.
Qed.
End Angle.
