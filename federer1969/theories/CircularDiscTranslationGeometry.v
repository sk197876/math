(** Federer (1969), 3.3.19, p. 304:
    support for congruence of the original level
    pieces. Every later original child pattern uses
    the same global circular directions, so translation
    preserves the actual refinement. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls InnerTranslationNeighbourhood
  FactorialDiscScalesSealed CircularDiscRefinement CircularDiscTreeUP CircularDiscTreeTopology
  CircularDiscLevelPieces CircularDiscAncestors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Translation.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).

(** Source for [circular_disc_child_translation]:
    translation preserves the actual original child
    centres, supporting congruence of the original
    A-intersections in 3.3.19, p. 304. *)
Lemma circular_disc_child_translation (z h:E) (r:R) n (k:'I_n):
  circular_disc_child_center (z+h) r k=circular_disc_child_center z r k+h.
Proof. by rewrite /circular_disc_child_center addrAC. Qed.

(** Source for [circular_disc_ball_translation]:
    original translated discs retain exactly the
    original metric membership, supporting the
    congruence assertion in 3.3.19, p. 304. *)
Lemma circular_disc_ball_translation (z h x:E) (r:R):
  metric_closed_ball (z+h) r (x+h) <->metric_closed_ball z r x.
Proof.
change (is_true (mdist (z+h:E) (x+h)<=r) <->is_true (mdist z x<=r)).
by rewrite (@inner_translation_distance R _ (@euclidean_inner_product R 2)
  (@euclidean_inner_productP R 2) h z x).
Qed.

Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_meeting_coarse_ancestor]:
    every original finer disc which meets an
    original coarser disc belongs wholly to that
    coarser disc, supporting 3.3.19, p. 304.
    Actual coarse-level uniqueness discharges ancestry. *)
Lemma circular_disc_meeting_coarse_ancestor j k (c w:E):
  (j<=k)%N ->c \in H j ->w \in H k ->
  metric_closed_ball w (rho k) `&` metric_closed_ball c (rho j)!=set0 ->
  metric_closed_ball w (rho k) `<=` metric_closed_ball c (rho j).
Proof.
move=>hjk hc hw [x [hxW hxC]].
have [a [ha hInside]]:=@circular_disc_ancestor_exists R H hH j k hjk w hw.
have hEqual:=@circular_disc_level_point_unique R H hH j x a c ha hc (hInside x hxW) hxC.
by rewrite -hEqual.
Qed.

(** Source for [circular_disc_descendant_translation_offset]:
    translating an actual original descendant from
    one level disc to any other gives an actual
    descendant at the same finer level, supporting
    the congruent level pieces of 3.3.19,
    p. 304. Induct on actual original
    refinements and use their unique coarse ancestor. *)
Theorem circular_disc_descendant_translation_offset j (c d:E):
  c \in H j ->d \in H j ->forall m (w:E),
  w \in H (j+m)%N ->
  metric_closed_ball w (rho (j+m)%N) `&` metric_closed_ball c (rho j)!=set0 ->
  w+(d-c) \in H (j+m)%N.
Proof.
move=>hc hd;elim=>[|m ih] w hw hMeeting.
- rewrite addn0 in hw hMeeting *.
  have [x [hxW hxC]]:=hMeeting.
  have hEqual:=@circular_disc_level_point_unique R H hH j x w c hw hc hxW hxC.
  by rewrite hEqual addrCA subrr addr0.
- have hIndex:(j+m.+1=(j+m).+1)%N by rewrite addnS.
  rewrite hIndex in hw hMeeting *.
  rewrite (circular_disc_tree_step hH) in hw.
  have [a [k [ha hW]]]:=(@circular_disc_refinement_membership R (H (j+m)%N)
    (rho (j+m)%N) ((j+m)+4)%N w).1 hw.
  have hParentMeeting:metric_closed_ball a (rho (j+m)%N) `&` metric_closed_ball c (rho j)!=set0.
    have [x [hxW hxC]]:=hMeeting;exists x;split=>//.
    apply:(@circular_disc_child_containment R (j+m)%N a k);by rewrite -hW.
  have hParent:=ih a ha hParentMeeting.
  rewrite (circular_disc_tree_step hH);apply/circular_disc_refinement_membership.
  exists (a+(d-c)),k;split=>//.
  by rewrite circular_disc_child_translation hW.
Qed.
End Translation.
