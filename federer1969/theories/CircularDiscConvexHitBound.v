(** Federer (1969), 3.3.19, p. 303: if
    an actual original parent centre is outside the
    original convex S, then no more than n/2+1
    original children can meet B intersect S. Derive
    the halfplane and all original-parent identifications. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls InnerConvex
  EuclideanConvexHalfspace FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscRefinement CircularDiscTreeUP CircularDiscTreeTopology CircularDiscLevelPieces
  CircularDiscTreeExactCount CircularDiscHitCount CircularDiscHalfplaneCriterion CircularDiscHalfplaneCount
  FiniteCellHitMeasureUP FiniteCellHitIndicesLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Bound.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation N:=(@FactorialDiscScales.count R).
Local Notation hs:=(@FactorialDiscScales.laws R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_convex_outside_hit_count]:
    actual child count in the c(B) outside S
    alternative of 3.3.19, p. 303. The
    original convex source may be nonmeasurable; its
    halfplane and the unique original parent are proved. *)
Theorem circular_disc_convex_outside_hit_count j (z:E) (S:set E):
  z \in H j ->S!=set0 ->is_inner_convex S ->~S z ->
  (2*#|` @circular_disc_hit_indices R H j.+1 (metric_closed_ball z (rho j) `&` S)|<=
    (j+4)+2)%N.
Proof.
move=>hz hNonempty hConvex hzOutside.
have [u [hu hHalf]]:=@euclidean_convex_unit_halfspace R 2 S z hNonempty hConvex hzOutside.
pose F:=@circular_halfplane_child_indices R z u (rho j) (j+4)%N.
pose G:{fset E}:=[fset circular_disc_child_center z (rho j) k | k in F].
have hSubset:(@circular_disc_hit_indices R H j.+1 (metric_closed_ball z (rho j) `&` S) `<=` G)%fset.
  apply/fsubsetP=>w.
  move=>/finite_cell_hit_indices_membership[hw [x [hxFine [hxB hxS]]]].
  rewrite (circular_disc_tree_step hH) in hw.
  have [a [k [ha hW]]]:=(@circular_disc_refinement_membership R (H j) (rho j) (j+4)%N w).1 hw.
  have hxParent:metric_closed_ball a (rho j) x.
    apply:(@circular_disc_child_containment R j a k);by rewrite -hW.
  have hEqual:=@circular_disc_level_point_unique R H hH j x a z ha hz hxParent hxB.
  subst a.
  apply/imfsetP;exists k;last exact:hW.
  rewrite /F /circular_halfplane_child_indices in_fset /=;apply/asboolP.
  exists x;split;first by rewrite -(factorial_disc_radius_step hs) -hW.
  exact:hHalf x hxS.
have hCard:#|` G|=#|` F|.
  rewrite /G card_imfset;last exact:(@circular_disc_child_center_injective R z (rho j) (j+4)%N
    (@factorial_disc_radius_positive R N rho hs j) (leq_addl j 4)).
  exact:erefl.
have hCount:=fsubset_leq_card hSubset;rewrite hCard in hCount.
have hHalfCount:=@circular_disc_halfplane_count R z u (rho j) (j+4)%N
  (@factorial_disc_radius_positive R N rho hs j) (leq_addl j 4) hu.
exact:leq_trans (leq_mul (leqnn 2) hCount) hHalfCount.
Qed.
End Bound.
