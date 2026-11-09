(** Federer (1969), 3.3.19, pp. 303–304:
    every original fine disc has an original ancestor
    at every coarser level, with actual whole-disc
    containment. No selected parent is globally exposed. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls FactorialDiscScalesSealed
  CircularDiscRefinement CircularDiscTreeUP CircularDiscTreeTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Ancestors.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_ancestor_offset]: exact
    actual ancestor and whole-disc inclusion at every
    finite offset, supporting 3.3.19, pp. 303–304. *)
Lemma circular_disc_ancestor_offset j:forall m (w:E),w \in H (j+m)%N ->
  exists z:E,z \in H j /\metric_closed_ball w (rho (j+m)%N) `<=` metric_closed_ball z (rho j).
Proof.
elim=>[|m ih] w hw.
- rewrite addn0 in hw *;exists w;split=>//;exact:subset_refl.
- have hIndex:(j+m.+1=(j+m).+1)%N by rewrite addnS.
  rewrite hIndex (circular_disc_tree_step hH) in hw.
  have [a [k [ha hW]]]:=(@circular_disc_refinement_membership R (H (j+m)%N)
    (rho (j+m)%N) ((j+m)+4)%N w).1 hw.
  have [z [hz hInside]]:=ih a ha.
  exists z;split=>//;rewrite hIndex hW.
  exact:subset_trans (@circular_disc_child_containment R (j+m)%N a k) hInside.
Qed.

(** Source for [circular_disc_ancestor_exists]: every
    original fine level disc is contained in an
    original disc at every coarser level, supporting
    the coarse-disc psi sums in 3.3.19, p. 304. *)
Theorem circular_disc_ancestor_exists j k:(j<=k)%N ->forall w:E,w \in H k ->
  exists z:E,z \in H j /\metric_closed_ball w (rho k) `<=` metric_closed_ball z (rho j).
Proof.
move=>hjk.
have hEq:(j+(k-j)=k)%N by rewrite subnKC.
rewrite -hEq;exact:circular_disc_ancestor_offset.
Qed.
End Ancestors.
