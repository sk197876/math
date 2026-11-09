(** Federer (1969), 3.3.19, p. 306: circular
    arc mass is bounded by the original centered-ball
    radius, supporting the last upper-density assertion. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularSineChordBound CircularChordLengths.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Chord.
Variable R:realType.
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_cap_chord_budget]: for every
    original 0<=gamma<=pi, gamma/pi<=sin(gamma/2).
    This compares the limiting actual cap mass to the
    centered-ball radius in the last claim of 3.3.19,
    p. 306. Both endpoint caps are retained. *)
Lemma circular_cap_chord_budget (g:R):0<=g ->g<=p ->g/p<=S (g/2).
Proof.
move=>hg hgp.
have hp:= real_trigonometry_pi_positive hb.
case:(eqVneq g 0)=>[->|hgN].
- by rewrite !mul0r (real_sine_zero hb).
case:(eqVneq g p)=>[->|hgpN].
- by rewrite divff ?gt_eqF // (real_sine_peak hb).
have hgP:0<g by rewrite lt_neqAle eq_sym hgN hg.
have hgStrict:g<p by rewrite lt_neqAle hgpN hgp.
have hHalf:0<g/2 by lra.
have hHalfP:g/2<p/2 by lra.
have h:= @circular_sine_strict_chord R (g/2) hHalf hHalfP.
have hAngle:2*(g/2)/p= g/p.
  field;by rewrite gt_eqF.
rewrite hAngle in h;exact:ltW h.
Qed.

(** Source for [circular_ball_cap_angle_budget]: any
    normalized original ball radius U in [0,2] has
    an actual cap angle gamma with cos(gamma)= 1-U^2/2
    and gamma/pi<=U/2. Actual inverse cosine and
    sine-chord laws prove this local choice for
    3.3.19, p. 306. *)
Theorem circular_ball_cap_angle_budget (U:R):0<=U ->U<=2 ->
  exists g:R,0<=g /\g<=p /\C g= 1-U^+2/2 /\g/p<=U/2.
Proof.
move=>hU hU2.
pose y:= 1-U^+2/2.
have hyL:-1<=y by rewrite /y;nra.
have hyU:y<=1 by rewrite /y;nra.
pose g:= @CircularTrigonometry.arccosine R y.
have [hg hgp]:= @circular_trig_acos_range R S C (@CircularTrigonometry.arcsine R)
  (@CircularTrigonometry.arccosine R) p ht y hyL hyU.
have hCos:= @circular_trig_acos_cosine R S C (@CircularTrigonometry.arcsine R)
  (@CircularTrigonometry.arccosine R) p ht y hyL hyU.
change (is_true (0<=g)) in hg.
change (is_true (g<=p)) in hgp.
change (C g= y) in hCos.
have hAngle:g/2+g/2= g by field.
have hDouble:C g=(C (g/2))^+2-(S (g/2))^+2.
  rewrite -{1}hAngle (circular_trig_cosine_add ht);ring.
have hUnit:= circular_trig_unit ht (g/2).
have hHalf:0<=g/2 by lra.
have hHalfP:g/2<=p by have hp:= real_trigonometry_pi_positive hb;lra.
have hNonnegative:= @circular_sine_nonnegative_semicircle R (g/2) hHalf hHalfP.
have hSine:S (g/2)= U/2 by rewrite /y in hCos;nra.
have hBudget:= circular_cap_chord_budget hg hgp.
rewrite hSine in hBudget.
exists g;split=>//;split=>//;by split.
Qed.
End Chord.
