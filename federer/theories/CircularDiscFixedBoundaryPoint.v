(** Federer (1969), 3.3.19, pp. 302 and 305: an
    actual boundary point of the unchanged example. It shows
    why the angular-visitation assertion is almost everywhere. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology ring.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls InnerUnitNormalization
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularTrigonometrySealed CircularUnitVectors CircularDiscRefinement CircularDiscTreeUP CircularDiscLimitUP
  CircularDiscRadialDirection CircularDiscRadialMapUP PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Point.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation hs:=(@FactorialDiscScales.laws R).
Local Notation u:=(@circular_unit_vector R 0).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_fixed_boundary_branch]: the
    actual point exp(0 i) belongs to a nested branch of
    original boundary circles, supporting the endpoint
    regression for 3.3.19, pp. 302 and 305. *)
Lemma circular_disc_fixed_boundary_branch j:
  exists z:E,z \in H j /\u= z+(rho j)*:u.
Proof.
elim:j=>[|j [z [hz hPoint]]].
- exists 0;split;first by rewrite (circular_disc_tree_root hH) in_fset1 eqxx.
  by rewrite (factorial_disc_radius_root hs) scale1r add0r.
- have hN:(0<j+4)%N by rewrite addn_gt0 orbT.
  pose k:'I_(j+4):= Ordinal hN.
  exists (circular_disc_child_center z (rho j) k);split.
  + rewrite (circular_disc_tree_step hH);apply/circular_disc_refinement_membership.
    by exists z,k;split.
  + have hAngle:2*(@CircularTrigonometry.half_period R)* k%:R/(j+4)%:R= 0.
      by rewrite /k /= mulr0 mul0r.
    rewrite /circular_disc_child_center hAngle (factorial_disc_radius_step hs) -addrA -scalerDl.
    have hScalar:(1-((j+4)%:R:R)^-1)* rho j+rho j/(j+4)%:R= rho j by ring.
    by rewrite hScalar.
Qed.

(** Source for [circular_disc_fixed_boundary_point_in_limit]:
    the actual point exp(0 i) belongs to the original
    A, including all closed boundary contacts in the
    construction of 3.3.19, p. 302. *)
Theorem circular_disc_fixed_boundary_point_in_limit (A:set E):
  is_circular_disc_limit H A ->A u.
Proof.
move=>hA;apply:(hA u).2=>j.
have [z [hz hPoint]]:= circular_disc_fixed_boundary_branch j.
exists z;split=>//.
have hPositive:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho hs j.
change (is_true (mdist z u<=rho j)).
rewrite {1}hPoint metric_sym inner_metric_distanceE addrAC subrr add0r
  inner_normZ circular_unit_vector_norm mulr1 ger0_norm //.
exact:ltW hPositive.
Qed.

(** Source for [circular_disc_fixed_boundary_radial_value]:
    all actual eta_n at exp(0 i) equal exp(0 i).
    This endpoint is an actual exceptional point for the
    almost-everywhere late-density statement of 3.3.19,
    p. 305, so that qualifier is essential. *)
Theorem circular_disc_fixed_boundary_radial_value j (eta:partial_function E E):
  is_circular_disc_radial_map H j eta ->forall v,
    partial_function_graph eta u v ->v= u.
Proof.
move=>hEta v hGraph.
have [z [hz hPoint]]:= circular_disc_fixed_boundary_branch j.
have hPositive:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho hs j.
have hNonzero:rho j!=0 by rewrite gt_eqF.
have hDifference:u-z= rho j*:u by rewrite {1}hPoint addrAC subrr add0r.
have hBall:metric_closed_ball z (rho j) u.
  change (is_true (mdist z u<=rho j)).
  rewrite metric_sym inner_metric_distanceE hDifference inner_normZ circular_unit_vector_norm mulr1
    (ger0_norm (ltW hPositive));exact:lexx.
by rewrite (circular_radial_map_value hEta hz hBall hGraph)
  /circular_disc_radial_direction /inner_unit_normalization hDifference
  inner_normZ circular_unit_vector_norm mulr1 (ger0_norm (ltW hPositive))
  scalerA mulVf // scale1r.
Qed.
End Point.
