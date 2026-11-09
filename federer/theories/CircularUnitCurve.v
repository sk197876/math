(** Federer (1969), 3.3.19, pp. 302–304: regularity
    and actual unit speed of the original circular parameter.
    All derivatives and bounds follow from the public scalar
    laws and the actual two-coordinate Euclidean norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  RealMetricBackground LipschitzUP LipschitzCurveAbsoluteContinuity LocallyAbsolutelyContinuousCurve
  RealCurveDerivativeUP NormedCurveDerivativeUP RealTrigonometryUP
  CircularTrigonometryUP CircularTrigonometrySealed CircularUnitVectors
  CircularScalarLipschitz PlanarCoordinateNormBound PlanarCircleCapCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Curve.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 2)).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation hb:=(circular_trig_basic (@CircularTrigonometry.laws R)).

(** Source for [circular_unit_vector_lipschitz]: a finite
    global Lipschitz bound for the original circular
    parameter in 3.3.19, pp. 302–304.
    This supporting bound need not be optimal. *)
Lemma circular_unit_vector_lipschitz (a b:R):
  mdist (circular_unit_vector a) (circular_unit_vector b)<= 2*`|a-b|.
Proof.
rewrite inner_metric_distanceE.
have hCoordinates:=@planar_coordinate_norm_upper R
  (circular_unit_vector a-circular_unit_vector b).
rewrite /circular_unit_vector !ffunE /= in hCoordinates.
have hC:=@circular_cosine_nonexpanding R a b.
have hS:=@circular_sine_nonexpanding R a b.
apply:(le_trans hCoordinates);lra.
Qed.

(** Source for [circular_unit_vector_locally_absolute_continuous]:
    the actual circular curve satisfies the curve-theory
    prerequisite for the perimeter argument in 3.3.19,
    p. 304, by the proved metric Lipschitz bound. *)
Lemma circular_unit_vector_locally_absolute_continuous:
  is_locally_absolutely_continuous_curve (@circular_unit_vector R).
Proof.
apply:(@metric_lipschitz_curve_locally_absolute_continuous R [the metricType R of E]
  (@circular_unit_vector R) 2);split;first by lra.
by move=>a b _ _;exact:circular_unit_vector_lipschitz.
Qed.

(** Source for [circular_unit_vector_velocity]: the actual
    velocity (-sin t,cos t) of the circular parameter,
    supporting the length normalization in 3.3.19,
    p. 304. This is a candidate vector before
    its derivative and unit norm are proved. *)
Definition circular_unit_vector_velocity (a:R):R_n R 2:=
  [ffun i=>if i== ord0 then -S a else C a].

(** Source for [circular_unit_vector_velocity_norm]: the
    actual velocity has norm one, supporting the circular
    boundary length used in 3.3.19, p. 304. *)
Lemma circular_unit_vector_velocity_norm a:N (circular_unit_vector_velocity a)= 1.
Proof.
apply:inner_norm_value;first exact:ler01.
rewrite expr1n planar_euclidean_inner_coordinates /circular_unit_vector_velocity !ffunE /=.
have hUnit:= circular_trig_unit (@CircularTrigonometry.laws R) a;nra.
Qed.

(** Source for [circular_unit_vector_derivative]: the
    original circular parameter has its actual vector
    derivative at every real parameter, supporting the
    boundary length in 3.3.19, p. 304.
    Both coordinate error bounds give the norm limit. *)
Theorem circular_unit_vector_derivative a:
  has_normed_curve_derivative N (@circular_unit_vector R) a
    (circular_unit_vector_velocity a).
Proof.
move=>e he.
have hQuarter:0<e/4 by lra.
have hCos:has_real_curve_derivative C a (-S a):=real_cosine_derivative hb a.
have hSin:has_real_curve_derivative S a (C a):=real_sine_derivative hb a.
have [dC [hdC hC]]:=@hCos (e/4) hQuarter.
have [dS [hdS hS]]:=@hSin (e/4) hQuarter.
exists (Num.min dC dS);split;first by rewrite lt_min hdC hdS.
move=>h /andP[hh0 hhSmall].
have hMinC:Num.min dC dS<= dC by rewrite ge_min lexx.
have hMinS:Num.min dC dS<= dS by rewrite ge_min lexx orbT.
have hhC:0<`|h|<dC by apply/andP;split=>//;exact:(lt_le_trans hhSmall hMinC).
have hhS:0<`|h|<dS by apply/andP;split=>//;exact:(lt_le_trans hhSmall hMinS).
have hCE:= hC h hhC;have hSE:= hS h hhS.
have hCoordinates:=@planar_coordinate_norm_upper R
  (h^-1 *: (circular_unit_vector (a+h)-circular_unit_vector a)-circular_unit_vector_velocity a).
rewrite /circular_unit_vector /circular_unit_vector_velocity !ffunE /= in hCoordinates.
have hComC:h^-1*(C (a+h)-C a)=(C (a+h)-C a)/h by rewrite mulrC.
have hComS:h^-1*(S (a+h)-S a)=(S (a+h)-S a)/h by rewrite mulrC.
change (is_true (N (h^-1 *: (circular_unit_vector (a+h)-circular_unit_vector a)-circular_unit_vector_velocity a)<=
  `|h^-1*(C (a+h)-C a)- -S a|+`|h^-1*(S (a+h)-S a)-C a|)) in hCoordinates.
rewrite hComC hComS in hCoordinates.
apply:(le_lt_trans hCoordinates);lra.
Qed.
End Curve.
