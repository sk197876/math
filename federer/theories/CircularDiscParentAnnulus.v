(** Federer (1969), 3.3.19, pp. 305–306: every
    original point of A lies in the thin original
    parent annulus, including closed boundary contacts. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology lra.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscTreeUP CircularDiscLimitUP CircularDiscParentChildPartition CircularDiscRadialDirection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Annulus.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_original_parent_annulus]:
    each original x in A intersect B(z,rho_j) satisfies
    rho_j-2rho_j/(j+4)<=|x-z|<=rho_j, supporting the
    cap and final density estimates in 3.3.19,
    pp. 305–306. Actual child membership proves the lower
    bound; it is not a defining law of A. *)
Theorem circular_disc_original_parent_annulus j (z x:E):
  z \in H j ->A x ->metric_closed_ball z (rho j) x ->
  rho j-2* rho j/(j+4)%:R<=inner_norm (@euclidean_inner_productP R 2) (x-z) /\
  inner_norm (@euclidean_inner_productP R 2) (x-z)<=rho j.
Proof.
move=>hz hx hxBall.
have hMember:(A `&` metric_closed_ball z (rho j)) x by split.
rewrite (@circular_disc_parent_child_partition R H hH A hA j z hz) in hMember.
have [k _ [_ hxChild]]:= hMember.
rewrite (factorial_disc_radius_step (@FactorialDiscScales.laws R)) in hxChild.
have hr:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho
  (@FactorialDiscScales.laws R) j.
have hn:(4<=j+4)%N by exact:leq_addl.
have hLower:= @circular_disc_child_parent_radius_lower R z (rho j) (j+4)%N k x hr hn hxChild.
split;first by nra.
by rewrite -inner_metric_distanceE metric_sym.
Qed.
End Annulus.
