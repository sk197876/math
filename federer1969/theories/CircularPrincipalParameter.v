(** Federer (1969), 3.3.19, pp. 302–304:
    the original half-open circular period parametrizes
    the actual Euclidean unit circle bijectively. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric RealTrigonometryUP
  CircularTrigonometryUP CircularTrigonometrySealed CircularUnitVectors
  CircularUnitVectorSurjection CircularUnitVectorInjective PlanarUnitCircleGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Principal.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation p:=(@CircularTrigonometry.half_period R).

(** Source for [circular_principal_parameter_exists]:
    every original planar unit direction has a parameter
    in [0,2pi), supporting the boundary curve in
    3.3.19, p. 304. The full-period
    endpoint is replaced by zero using actual periodicity. *)
Theorem circular_principal_parameter_exists (u:E):planar_unit_circle u ->
  exists t:R,0<= t /\t<2* p /\circular_unit_vector t= u.
Proof.
move=>hu;have [t [ht0 [htP hValue]]]:= @circular_unit_vector_surjective R u hu.
case:(ltP t (2* p))=>hStrict;first by exists t;split=>//;split.
have hEnd:t= 2* p by lra.
exists 0;split;first exact:lexx.
split.
- have hp:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R));lra.
- have hPeriod:= @circular_unit_vector_period R 0.
  have hAngle:0+(p+p)= 2* p by ring.
  by rewrite hAngle -hEnd hValue in hPeriod.
Qed.

(** Source for [circular_principal_image]: the
    original half-open circular interval has exactly
    the actual Euclidean unit circle as its image,
    supporting 3.3.19, p. 304. *)
Lemma circular_principal_image:
  (@circular_unit_vector R) @` (`[0,2* p[:set R)= @planar_unit_circle R.
Proof.
apply/seteqP;split=>u.
- move=>[t _ <-];exact:circular_unit_vector_norm.
- move=>hu;have [t [ht0 [htP hValue]]]:= circular_principal_parameter_exists hu.
  exists t=>//;by rewrite /= in_itv /= ht0 htP.
Qed.
End Principal.
