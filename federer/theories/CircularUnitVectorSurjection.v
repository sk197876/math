(** Federer (1969), 3.3.19, pp. 302, 305:
    every actual unit direction in the original Euclidean
    plane is an actual circular direction. Angles remain
    existential; no auxiliary global angle is selected. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  PlanarCircleCapCoordinates RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularUnitVectors CircularChordLengths CircularCosineReflection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Directions.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation D:=(@CircularTrigonometry.arccosine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_sine_full_period]: actual sine
    period used to cover both semicircles in the
    original unit-circle geometry of 3.3.19, pp. 302, 305. *)
Lemma circular_sine_full_period x:S (x+(p+p))=S x.
Proof. by rewrite addrA !(real_sine_half_period hb) opprK. Qed.

(** Source for [circular_sine_reflected_period]: actual
    lower-semicircle sine used for the original unit
    directions in 3.3.19, pp. 302, 305. *)
Lemma circular_sine_reflected_period x:S (2* p-x)= -S x.
Proof.
have hEq:2* p-x=(-x)+(p+p) by ring.
by rewrite hEq circular_sine_full_period (real_sine_odd hb).
Qed.

(** Source for [planar_vector_two_coordinate_extensionality]:
    equality of the two original real coordinates is
    equality of the actual planar vectors, supporting
    circular geometry in 3.3.19, pp. 302, 305. *)
Lemma planar_vector_two_coordinate_extensionality (u v:E):
  u ord0=v ord0 ->u (@Ordinal 2 1 (erefl true))=v (@Ordinal 2 1 (erefl true)) ->u=v.
Proof.
move=>h0 h1;apply/ffunP=>i.
case:i=>[[|[|i]] hi].
- have heq:(@Ordinal 2 0 hi)=ord0 by apply:val_inj.
  by rewrite heq.
- have heq:(@Ordinal 2 1 hi)=(@Ordinal 2 1 (erefl true)) by apply:val_inj.
  by rewrite heq.
- exfalso;by move:hi;rewrite !ltnS ltn0.
Qed.

(** Source for [circular_unit_vector_surjective]: every
    original planar unit vector has a representative angle
    in [0,2pi], supporting every-direction halfplane,
    arc and cone claims in 3.3.19, pp. 302, 305.
    The actual norm supplies the coordinate equations;
    the independently sealed inverse cosine supplies the
    angle. No surjectivity or chosen-angle premise is added. *)
Theorem circular_unit_vector_surjective (u:E):
  inner_norm (@euclidean_inner_productP R 2) u= 1 ->
  exists t:R,0<=t /\t<=2* p /\circular_unit_vector t=u.
Proof.
move=>hu.
pose x:R:=u ord0.
pose y:R:=u (@Ordinal 2 1 (erefl true)).
have hUnit:x^+2+y^+2= 1.
  have hh:=inner_norm_sqr (@euclidean_inner_productP R 2) u.
  by rewrite hu expr1n planar_euclidean_inner_coordinates -!expr2 in hh.
have hx0:-1<=x by nra.
have hx1:x<= 1 by nra.
have [ht0 htp]:=@circular_trig_acos_range R S C (@CircularTrigonometry.arcsine R) D p ht x hx0 hx1.
have hCos:=@circular_trig_acos_cosine R S C (@CircularTrigonometry.arcsine R) D p ht x hx0 hx1.
have hSNonnegative:=@circular_sine_nonnegative_semicircle R (D x) ht0 htp.
have hTrig:=circular_trig_unit ht (D x);rewrite hCos in hTrig.
have hp:=real_trigonometry_pi_positive hb.
case:(leP 0 y)=>hy.
- have hS:S (D x)=y by nra.
  exists (D x);split=>//;split;first by lra.
  apply:planar_vector_two_coordinate_extensionality.
  + by rewrite circular_unit_vector_first.
  + by rewrite circular_unit_vector_second.
- have hS:S (D x)= -y by nra.
  exists (2* p-D x);split;first by lra.
  split;first by lra.
  apply:planar_vector_two_coordinate_extensionality.
  + by rewrite circular_unit_vector_first circular_cosine_reflected_period.
  + by rewrite circular_unit_vector_second circular_sine_reflected_period hS opprK.
Qed.
End Directions.
