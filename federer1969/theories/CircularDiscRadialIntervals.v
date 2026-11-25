(** Federer (1969), 3.3.19, p. 305: whole original
    child discs whose centre angles lie inside a proper
    arc have every actual eta_n value in that arc. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws CircularTrigonometrySealed CircularUnitVectors
  CircularDiscRefinement CircularDiscTreeUP CircularDiscLimitUP CircularDiscRadialMapUP
  CircularDiscRadialMapLaws CircularDiscRadialParameter PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Arcs.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation p:=(@CircularTrigonometry.half_period R).

(** Source for [circular_parameter_arc]: the original
    circle arc parametrized by a<t<b, supporting the
    proper-arc test of 3.3.19, p. 305. Parameters
    and their representatives remain local. *)
Definition circular_parameter_arc (a b:R):set E:=
  (@circular_unit_vector R) @` [set t:R|a<t /\t<b].

Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable j:nat.
Variable eta:partial_function E E.
Hypothesis hEta:is_circular_disc_radial_map H j eta.

(** Source for [circular_disc_child_radial_interval]: if the
    original child centre angle lies in [a+e,b-e] and
    pi/(2n)<=e, its whole actual eta_n image is inside
    the original arc (a,b). This discharges the geometric
    input of the late-visit count in 3.3.19, p. 305,
    including closed child-disc boundary contacts. *)
Theorem circular_disc_child_radial_interval (a b e:R) (z:E) (k:'I_(j+4)):
  z \in H j ->p/(2*(j+4)%:R)<=e ->
  a+e<=2* p* k%:R/(j+4)%:R ->2* p* k%:R/(j+4)%:R<=b-e ->
  forall x v,metric_closed_ball (circular_disc_child_center z (rho j) k) (rho j.+1) x ->
    partial_function_graph eta x v ->circular_parameter_arc a b v.
Proof.
move=>hz hSmall hLeft hRight x v hx hGraph.
have hValue:=(@circular_disc_radial_map_child_value R H j eta hEta z x v k hz hx hGraph).1.
have hRadius:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho
  (@FactorialDiscScales.laws R) j.
have hSubdivision:(4<=j+4)%N:= leq_addl j 4.
rewrite (factorial_disc_radius_step (@FactorialDiscScales.laws R)) in hx.
have [t [hNear hAngle]]:= @circular_disc_radial_parameter_near_centre R z (rho j)
  (j+4)%N k x hRadius hSubdivision hx.
have /andP[hNearLower hNearUpper]:(-(p/(2*(j+4)%:R))<t-2* p* k%:R/(j+4)%:R<
  p/(2*(j+4)%:R)) by move:hNear;rewrite ltr_norml.
exists t;last by rewrite hValue hAngle.
split;lra.
Qed.
End Arcs.
