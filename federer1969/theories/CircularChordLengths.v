(** Federer (1969), 3.3.19, p. 302: exact actual
    circular chord length, preceding the finite cyclic
    minimum-distance estimate for the original disc centres. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric CircularUnitVectors
  RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Chords.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_sine_nonnegative_semicircle]: scalar
    sign supporting exact chord lengths in 3.3.19, p. 302.
    Endpoints follow from the public normalization laws. *)
Lemma circular_sine_nonnegative_semicircle x:
  0<=x ->x<=p ->0<=S x.
Proof.
move=>hx hxp;case:(eqVneq x 0)=>[->|hxN].
- by rewrite (real_sine_zero hb).
- case:(eqVneq x p)=>[->|hxpN];first by rewrite (circular_trig_sine_pi ht).
  have hxP:0<x by rewrite lt_neqAle eq_sym hxN hx.
  have hxPi:x<p by rewrite lt_neqAle hxpN hxp.
  exact:(ltW (@circular_trig_sine_positive R S C (@CircularTrigonometry.arcsine R)
    (@CircularTrigonometry.arccosine R) p ht x hxP hxPi)).
Qed.

(** Source for [circular_unit_chord_length]: the actual
    chord has length 2 sin(x) for a positive half-angle
    x<=pi, supporting the displayed minimum centre distance
    in 3.3.19, p. 302. The base angle is arbitrary. *)
Lemma circular_unit_chord_length a x:
  0<=x ->x<=p ->
  mdist (circular_unit_vector (a+2*x):E) (circular_unit_vector a)= 2*S x.
Proof.
move=>hx hxp.
have hSin:=circular_sine_nonnegative_semicircle hx hxp.
have hD:=circular_unit_vector_distance_square (a+2*x) a.
have hDiff:(a+2*x)-a=x+x by ring.
rewrite hDiff (circular_trig_cosine_add ht) in hD.
have hUnit:=circular_trig_unit ht x.
have hNonnegative:=mdist_ge0 (circular_unit_vector (a+2*x):E) (circular_unit_vector a).
nra.
Qed.
End Chords.
