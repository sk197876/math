(** Federer (1969), 3.3.19, p. 306: strict
    elementary numerical margin needed for fine-scale
    child packing in the last density assertion. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularSineOrder CircularSineEndpointChord CircularSineChordBound CircularScalarLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Strict.
Variable R:realType.
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation hb:=(circular_trig_basic (@CircularTrigonometry.laws R)).

(** Source for [circular_half_period_strictly_above_three]:
    pi>3, supporting the actual tangential child
    separation used in the last density claim of
    3.3.19, p. 306. Strict sine chords and the
    proved sine contraction give the strict inequality. *)
Theorem circular_half_period_strictly_above_three:3<p.
Proof.
have hp:= real_trigonometry_pi_positive hb.
have hL:0<p/6 by lra.
have hLP:p/6<=p/2 by lra.
have hx:0<p/12 by lra.
have hxL:p/12<p/6 by lra.
have hChord:= @circular_sine_endpoint_chord R (p/6) (p/12) hL hLP hx hxL.
rewrite (@circular_sine_twelfth_turn R) in hChord.
have hSlope:(1/2)/(p/6)= 3/p.
  have hpN:p!=0 by rewrite gt_eqF.
  field;by rewrite hpN.
rewrite hSlope in hChord.
have hUpper:= @circular_sine_nonexpanding R (p/12) 0.
rewrite (real_sine_zero hb) !subr0 (ger0_norm (ltW hx)) in hUpper.
have hEnd:p/12<p by lra.
have hSinPositive:= @circular_trig_sine_positive R S (@CircularTrigonometry.cosine R)
  (@CircularTrigonometry.arcsine R) (@CircularTrigonometry.arccosine R) p
  (@CircularTrigonometry.laws R) (p/12) hx hEnd.
rewrite (ger0_norm (ltW hSinPositive)) in hUpper.
have hStrict:(3/p)*(p/12)<p/12:= lt_le_trans hChord hUpper.
have hRatio:3/p<1.
  have h: (3/p)*(p/12)<1*(p/12) by rewrite mul1r.
  by rewrite ltr_pM2r in h.
by move:hRatio;rewrite ltr_pdivrMr // mul1r.
Qed.
End Strict.
