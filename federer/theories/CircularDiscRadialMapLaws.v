(** Federer (1969), 3.3.19, p. 305: consequences of
    the independently specified original radial-map laws. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscRefinement CircularDiscTreeUP CircularDiscTreeTopology CircularDiscLimitUP CircularDiscLevelPieces
  CircularDiscRadialDirection CircularDiscRadialMapUP PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Laws.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable j:nat.
Variable eta:partial_function E E.
Hypothesis hEta:is_circular_disc_radial_map H j eta.

(** Source for [circular_disc_radial_map_child_value]: the
    printed eta_n formula on each original child disc,
    3.3.19, p. 305, with positivity of its actual
    denominator and its unit-vector range both derived. *)
Lemma circular_disc_radial_map_child_value (z x v:E) (k:'I_(j+4)):
  z \in H j ->
  metric_closed_ball (circular_disc_child_center z (rho j) k) (rho j.+1) x ->
  partial_function_graph eta x v ->
  v= circular_disc_radial_direction z x /\
    inner_norm (@euclidean_inner_productP R 2) v= 1.
Proof.
move=>hz hx hGraph.
have hParent:= @circular_disc_child_containment R j z k x hx.
have hValue:= circular_radial_map_value hEta hz hParent hGraph.
split=>//;rewrite hValue.
rewrite (factorial_disc_radius_step (@FactorialDiscScales.laws R)) in hx.
apply:(@circular_disc_radial_direction_unit R z (rho j) (j+4)%N k x).
- exact:(@factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho
    (@FactorialDiscScales.laws R) j).
- exact:leq_addl.
- exact:hx.
Qed.

(** Source for [circular_disc_radial_map_unit]: every value
    of the actual original eta_n lies on S^1,
    3.3.19, p. 305. The exact original domain
    gives an actual child and parent; no chosen global
    direction or parent is used in the statement. *)
Theorem circular_disc_radial_map_unit (x v:E):
  partial_function_graph eta x v ->
  inner_norm (@euclidean_inner_productP R 2) v= 1.
Proof.
move=>hGraph.
have hxDomain:partial_function_domain eta x by exists v.
have [w [hw hx]]:=(circular_radial_map_domain hEta x).1 hxDomain.
rewrite (circular_disc_tree_step hH) in hw.
have [z [k [hz hW]]]:=(@circular_disc_refinement_membership R (H j) (rho j) (j+4)%N w).1 hw.
rewrite hW in hx.
exact:(@circular_disc_radial_map_child_value z x v k hz hx hGraph).2.
Qed.

(** Source for [circular_disc_radial_map_limit_domain]:
    every original a in A has a defined eta_n(a),
    3.3.19, p. 305. No extension value outside
    the printed union G_n is needed. *)
Theorem circular_disc_radial_map_limit_domain (A:set E):
  is_circular_disc_limit H A ->forall x,A x ->exists v,partial_function_graph eta x v.
Proof.
move=>hA x hx;apply:(circular_radial_map_domain hEta x).2.
exact:(hA x).1 hx j.+1.
Qed.
End Laws.
