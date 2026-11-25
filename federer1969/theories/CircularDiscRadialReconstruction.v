(** Federer (1969), 3.3.19, p. 305: recover the
    actual original vertex in the local radial coordinates
    of each original eta value. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerUnitNormalization
  MetricClosedBalls FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscRefinement CircularDiscTreeUP CircularDiscTreeTopology CircularDiscLimitUP CircularDiscLevelPieces
  CircularDiscRadialDirection CircularDiscRadialMapUP CircularDiscRadialMapLaws PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Reconstruction.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation N:=(inner_norm (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation hS:=(@FactorialDiscScales.laws R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_radial_vertex_reconstruction]:
    every actual eta_j(a) at a in original A has an
    original parent z and a positive radius d with
    a= z+d eta_j(a), rho_j-2rho_j/(j+4)<=d<=rho_j.
    These original pointwise bounds discharge the geometry
    hypotheses in the cone comparison of 3.3.19, p. 305. *)
Theorem circular_disc_radial_vertex_reconstruction j (eta:partial_function E E) (a v:E):
  is_circular_disc_radial_map H j eta ->A a ->partial_function_graph eta a v ->
  exists z:E,z \in H j /\exists d:R,0<d /\d<=rho j /\
    rho j-2* rho j/(j+4)%:R<=d /\a= z+d*:v /\N v= 1.
Proof.
move=>hEta ha hGraph.
have [w [hw haW]]:=(hA a).1 ha j.+1.
rewrite (circular_disc_tree_step hH) in hw.
have [z [k [hz hW]]]:=(@circular_disc_refinement_membership R (H j) (rho j) (j+4)%N w).1 hw.
rewrite hW in haW.
have haZ:= @circular_disc_child_containment R j z k a haW.
have [hValue hUnit]:= @circular_disc_radial_map_child_value R H j eta hEta z a v k hz haW hGraph.
have hr:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho hS j.
have hn:(4<=j+4)%N by exact:leq_addl.
have haChild:metric_closed_ball (circular_disc_child_center z (rho j) k) (rho j/(j+4)%:R) a.
  by rewrite -(factorial_disc_radius_step hS).
have hd:= @circular_disc_child_parent_radius_positive R z (rho j) (j+4)%N k a hr hn haChild.
have hLower:= @circular_disc_child_parent_radius_lower R z (rho j) (j+4)%N k a hr hn haChild.
have hUpper:N (a-z)<=rho j by rewrite -inner_metric_distanceE metric_sym.
exists z;split=>//;exists (N (a-z));split=>//;split=>//;split;first by nra.
split=>//.
have hDN:N (a-z)!=0 by rewrite gt_eqF.
rewrite hValue /circular_disc_radial_direction /inner_unit_normalization scalerA mulfV // scale1r.
by rewrite addrC subrK.
Qed.
End Reconstruction.
