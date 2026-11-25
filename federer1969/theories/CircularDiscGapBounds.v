(** Federer (1969), 3.3.19, p. 302: elementary
    size bounds on the printed original sibling gap. These
    compare its attained value with separation inherited
    from different original parents. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularSineOrder CircularSineChordBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Bounds.
Variable R:realType.
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_disc_gap_coefficient_above_one]:
    the displayed minimum gap exceeds the common child
    radius, 3.3.19, p. 302. It follows strictly from
    the actual sine chord inequality. *)
Lemma circular_disc_gap_coefficient_above_one n:(4<=n)%N ->
  1<2*((n%:R-1)* S (p/n%:R)-1).
Proof.
move=>hn;have hp:=real_trigonometry_pi_positive hb.
have hN4:(4<=n%:R:>R) by rewrite ler_nat.
have hNP:(0<n%:R:>R) by lra.
have hNN:(n%:R:R)!= 0 by rewrite gt_eqF.
have hInv:(0<n%:R^-1:>R) by rewrite invr_gt0.
have hCancel:(n%:R:R)*n%:R^-1= 1 by rewrite mulfV.
have hQuarter:(4*n%:R^-1<= 1:>R) by have hScale:=ler_wpM2r (ltW hInv) hN4;rewrite hCancel in hScale.
have hx:0<p/n%:R by rewrite divr_gt0.
have hxHalf:p/n%:R<p/2 by change (is_true (p*n%:R^-1<p/2));nra.
have hS:=@circular_sine_strict_chord R (p/n%:R) hx hxHalf.
have hpN:p!= 0 by rewrite gt_eqF.
have hCancelAngle:(p/n%:R)/p=n%:R^-1 by rewrite mulrAC divff // mul1r.
have hAngle:2*(p/n%:R)/p= 2*n%:R^-1 by rewrite -mulrA hCancelAngle.
rewrite hAngle in hS.
have hLower:(n%:R-1)*(2*n%:R^-1)<(n%:R-1)* S (p/n%:R) by nra.
have hIdentity:((n%:R:R)-1)*(2*n%:R^-1)= 2-2*n%:R^-1 by nra.
rewrite hIdentity in hLower;nra.
Qed.

(** Source for [circular_disc_gap_coefficient_parent_bound]:
    the actual sibling gap is at most the parent radius,
    supporting the global minimum in 3.3.19, p. 302.
    The finitely small subdivisions and the asymptotic
    range are both proved from the public scalar laws. *)
Lemma circular_disc_gap_coefficient_parent_bound n:(4<=n)%N ->
  2*((n%:R-1)* S (p/n%:R)-1)<=n%:R.
Proof.
move=>hn;have hp:=real_trigonometry_pi_positive hb.
have hNP:(0<n%:R:>R) by rewrite ltr0n;exact:leq_trans (erefl true : (1<=4)%N) hn.
have hNN:(n%:R:R)!= 0 by rewrite gt_eqF.
have hInv:(0<n%:R^-1:>R) by rewrite invr_gt0.
have hCancel:(n%:R:R)*n%:R^-1= 1 by rewrite mulfV.
have hPositive:0<p/n%:R by rewrite divr_gt0.
have hx:0<=p/n%:R:=ltW hPositive.
case:(leqP 6 n)=>[h6|hSmall].
- have hN6:(6<=n%:R:>R) by rewrite ler_nat.
  have hSix:(6*n%:R^-1<= 1:>R) by have hScaled:=ler_wpM2r (ltW hInv) hN6;rewrite hCancel in hScaled.
  have hx6:p/n%:R<=p/6 by change (is_true (p*n%:R^-1<=p/6));nra.
  have hpHalf:p/6<=p/2 by lra.
  have hS:=@circular_sine_weak_increase R (p/n%:R) (p/6) hx hx6 hpHalf.
  rewrite (@circular_sine_twelfth_turn R) in hS;nra.
- have hN4:(4<=n%:R:>R) by rewrite ler_nat.
  have hN6:(n%:R<6:>R) by rewrite ltr_nat.
  have hQuarter:(4*n%:R^-1<= 1:>R) by have hScaled:=ler_wpM2r (ltW hInv) hN4;rewrite hCancel in hScaled.
  have hx4:p/n%:R<=p/4 by change (is_true (p*n%:R^-1<=p/4));nra.
  have hpHalf:p/4<=p/2 by lra.
  have hS:=@circular_sine_weak_increase R (p/n%:R) (p/4) hx hx4 hpHalf.
  have hBound:=@circular_sine_eighth_turn_upper R;nra.
Qed.
End Bounds.
