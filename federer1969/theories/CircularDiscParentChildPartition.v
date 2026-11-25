(** Federer (1969), 3.3.19, pp. 304–305: partition
    each original A-piece by its actual original children. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls FactorialDiscScalesSealed
  CircularDiscRefinement CircularDiscTreeUP CircularDiscTreeTopology CircularDiscLimitUP CircularDiscLevelPieces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Pieces.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_parent_child_partition]: the
    original A intersect B is precisely the union of its
    original child A-pieces, supporting the uniform cap
    comparison of 3.3.19, p. 305. Actual original
    fine membership and unique original parents prove it. *)
Theorem circular_disc_parent_child_partition j (z:E):z \in H j ->
  A `&` metric_closed_ball z (rho j)=
    \bigcup_(k in [set: 'I_(j+4)])
      (A `&` metric_closed_ball (circular_disc_child_center z (rho j) k) (rho j.+1)).
Proof.
move=>hz;apply/seteqP;split.
- move=>x [hxA hxZ].
  have [w [hw hxW]]:=(hA x).1 hxA j.+1.
  rewrite (circular_disc_tree_step hH) in hw.
  have [v [k [hv hW]]]:=(@circular_disc_refinement_membership R (H j) (rho j) (j+4)%N w).1 hw.
  rewrite hW in hxW.
  have hxV:= @circular_disc_child_containment R j v k x hxW.
  have hEqual:= @circular_disc_level_point_unique R H hH j x v z hv hz hxV hxZ.
  exists k=>//;split=>//;by rewrite -hEqual.
- move=>x [k _ [hxA hxChild]];split=>//.
  exact:(@circular_disc_child_containment R j z k x hxChild).
Qed.
End Pieces.
