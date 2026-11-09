(** Federer (1969), 3.3.19, p. 306: actual
    tangential coordinates of original circular directions,
    with the original cyclic cut lifted only locally. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct PlanarCircleCapCoordinates
  RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed CircularUnitVectors
  CircularUnitCurve CircularUnitVectorSurjection CircularAngleLift CyclicGridShiftSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Tangents.
Variable R:realType.
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_unit_vector_tangent_coordinate]:
    the original tangent at exp(i a) evaluates exp(i t)
    as sin(t-a), supporting the final density proof
    in 3.3.19, p. 306. *)
Lemma circular_unit_vector_tangent_coordinate (a t:R):
  euclidean_inner_product (circular_unit_vector t) (circular_unit_vector_velocity a)= S (t-a).
Proof.
rewrite planar_euclidean_inner_coordinates /circular_unit_vector_velocity !ffunE /=
  (circular_trig_sine_add ht) (real_sine_odd hb) (circular_trig_cosine_even ht).
ring.
Qed.

(** Source for [circular_angle_lift_sine]: the original
    cyclic angle's local full-period lift preserves its
    actual tangential coordinate, supporting 3.3.19,
    p. 306. The cut and original index stay local. *)
Lemma circular_angle_lift_sine n (a:R) (k:'I_n):(0<n)%N ->
  S (cyclic_grid_shifted_point (2* p/n%:R) (circular_angle_lift_branch a) k-a)=
    S (2* p* k%:R/n%:R-a).
Proof.
move=>hn.
have hNN:(n%:R:R)!=0 by rewrite pnatr_eq0 -lt0n.
pose q:= 2* p/n%:R.
have hBudget:q* n%:R= 2* p by rewrite /q divfK.
have hAngle:2* p* k%:R/n%:R= q* k%:R by rewrite /q;ring.
rewrite hAngle /cyclic_grid_shifted_point -/q.
case:(circular_angle_lift_branch a k)=>/=;last by rewrite addr0.
have hEq:q*(k%:R+n%:R)-a=(q* k%:R-a)+(p+p) by rewrite mulrDr hBudget;ring.
by rewrite hEq circular_sine_full_period.
Qed.
End Tangents.
