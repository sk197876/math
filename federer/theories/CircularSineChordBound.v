(** Federer (1969), 3.3.19, p. 302: the strict
    elementary estimate sin(x)>2x/pi on 0<x<pi/2,
    supporting actual separation of the circular discs. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  topology num_normedtype pseudometric_normed_Zmodule normed_module lra ring.
From Federer Require Import RealCurveDerivativeUP RealDerivativeContinuity
  RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed StrictMidpointChordPositive.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Chords.
Variable R:realType.
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_sine_continuous]: continuity of
    the actual circular parameter, supporting 3.3.19,
    p. 302. It follows from the actual derivative by the
    project's epsilon argument, not external calculus. *)
Lemma circular_sine_continuous:continuous (S:R^o->R^o).
Proof.
move=>a;exact:(real_derivative_continuous_at (real_sine_derivative hb a)).
Qed.

(** Source for [circular_sine_strict_midpoint]: strict
    scalar midpoint concavity on the first quadrant,
    supporting the printed chord inequality in 3.3.19,
    p. 302. Addition laws and strict cosine monotonicity
    prove it; no concavity premise is supplied. *)
Lemma circular_sine_strict_midpoint u v:
  0<=u ->u<v ->v<=p/2 ->(S u+S v)/2<S ((u+v)/2).
Proof.
move=>hu huv hv.
have hp:=real_trigonometry_pi_positive hb.
pose m:=(u+v)/2;pose d:=(v-u)/2.
have hm:0<m by rewrite /m;lra.
have hmp:m<p by rewrite /m;lra.
have hd:0<d by rewrite /d;lra.
have hdp:d<p by rewrite /d;lra.
have hSm:=circular_trig_sine_positive ht hm hmp.
have hCd:C d<1.
  have hC:=@circular_trig_cosine_decreases R S C
    (@CircularTrigonometry.arcsine R) (@CircularTrigonometry.arccosine R) p ht
    0 d (lexx 0) (ltW hp) (ltW hd) (ltW hdp) hd.
  by rewrite (real_cosine_zero hb) in hC.
have hU:u=m+(-d) by rewrite /m /d;field.
have hV:v=m+d by rewrite /m /d;field.
have hSum:S u+S v= 2*S m*C d.
  rewrite {1}hU {1}hV !(circular_trig_sine_add ht)
    (real_sine_odd hb) (circular_trig_cosine_even ht);ring.
have hStrict:2*S m*C d<2*S m by nra.
rewrite hSum; nra.
Qed.

(** Source for [circular_sine_strict_chord]: literal strict
    inequality sin(x)>2x/pi used in 3.3.19, p. 302.
    The project's compact-minimum proof turns the proved
    strict midpoint property into the full real chord bound. *)
Theorem circular_sine_strict_chord x:
  0<x ->x<p/2 ->2*x/p<S x.
Proof.
move=>hx hxp.
have hp:=real_trigonometry_pi_positive hb.
have hpN:p!= 0 by rewrite gt_eqF.
pose F:R^o->R^o:=fun t=>S t-2*t/p.
have hLinear:continuous (fun t:R^o=>(2*t/p:R^o)).
  move=>t;apply:continuousM;last exact:cst_continuous.
  apply:continuousM;first exact:cst_continuous.
  by move=>U hU.
have hF:continuous F.
  move=>t;exact (@continuousB R [the normedModType R of R^o]
    [the topologicalType of R^o] (S:R^o->R^o) (fun t:R^o=>(2*t/p:R^o)) t
    (@circular_sine_continuous t) (hLinear t)).
have hF0:F 0= 0 by rewrite /F (real_sine_zero hb) mulr0 mul0r subrr.
have hFEnd:F (p/2)= 0.
  rewrite /F (real_sine_peak hb);by field.
have hMid u v:0<=u ->u<v ->v<=p/2 ->(F u+F v)/2<F ((u+v)/2).
  move=>hu huv hv;have hS:=circular_sine_strict_midpoint hu huv hv.
  have hAffine:(2*u/p+2*v/p)/2= 2*((u+v)/2)/p by ring.
  rewrite /F;have hEq:(S u-2*u/p+(S v-2*v/p))/2=
      (S u+S v)/2-2*((u+v)/2)/p by rewrite -hAffine;ring.
  by rewrite hEq ltrD2r.
have hHalf:0<p/2 by rewrite divr_gt0 ?ltr0n.
have hPositive:=@strict_midpoint_chord_positive R F (p/2) hHalf hF hF0 hFEnd hMid x hx hxp.
by move:hPositive;rewrite /F subr_gt0.
Qed.
End Chords.
