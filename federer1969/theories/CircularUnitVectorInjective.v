(** Federer (1969), 3.3.19, pp. 302–304:
    the actual circular parameter is one-to-one on
    its original half-open period. Exact chord lengths
    and strict sine positivity prove the assertion. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric RealTrigonometryUP
  CircularTrigonometryUP CircularTrigonometrySealed CircularUnitVectors CircularChordLengths.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Injectivity.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_unit_vector_short_period_distinct]:
    two actual circular parameters with positive difference
    less than a full period give distinct original
    directions, supporting the boundary parametrization in
    3.3.19, pp. 302–304. *)
Lemma circular_unit_vector_short_period_distinct (a b:R):
  a<b ->b-a<2* p ->circular_unit_vector a!=circular_unit_vector b.
Proof.
move=>hab hWidth.
have hx:0<(b-a)/2 by lra.
have hxp:(b-a)/2<p by lra.
have hSine:=@circular_trig_sine_positive R S C (@CircularTrigonometry.arcsine R)
  (@CircularTrigonometry.arccosine R) p ht ((b-a)/2) hx hxp.
have hAngle:a+2*((b-a)/2)=b by field.
have hChord:=@circular_unit_chord_length R a ((b-a)/2) (ltW hx) (ltW hxp).
rewrite hAngle in hChord.
apply/negP=>/eqP hEqual;rewrite -hEqual mdistxx in hChord.
nra.
Qed.

(** Source for [circular_unit_vector_principal_injective]:
    exact injectivity on the original interval [0,2pi),
    supporting a simple closed boundary curve in
    3.3.19, p. 304. The repeated full-period
    endpoint is explicitly excluded. *)
Theorem circular_unit_vector_principal_injective (a b:R):
  0<=a ->a<2* p ->0<=b ->b<2* p ->
  circular_unit_vector a=circular_unit_vector b ->a=b.
Proof.
move=>ha haP hb hbP hEqual.
case:(ltgtP a b)=>[hab|hba|h];last exact h.
- have hWidth:b-a<2* p by lra.
  have hDifferent:=@circular_unit_vector_short_period_distinct a b hab hWidth.
  by move:hDifferent;rewrite hEqual eqxx.
- have hWidth:a-b<2* p by lra.
  have hDifferent:=@circular_unit_vector_short_period_distinct b a hba hWidth.
  by move:hDifferent;rewrite hEqual eqxx.
Qed.
End Injectivity.
