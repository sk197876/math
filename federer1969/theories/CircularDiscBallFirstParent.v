(** Federer (1969), 3.3.19, pp. 303 and 306:
    the actual first split confines all original source
    points of the test ball to one original parent. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls FactorialDiscScalesSealed
  CircularDiscRefinement CircularDiscTreeUP CircularDiscLimitUP CircularDiscHitCount
  CircularDiscFirstSplitUP CircularDiscFirstSplit FiniteCellHitMeasureUP FiniteCellHitIndicesLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Parent.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_ball_first_parent]: the
    actual first splitting ball has one original parent
    containing its vertex and ALL its original A-points;
    every hit fine disc is an actual child of that
    parent. This supplies the geometry of the last
    density proof in 3.3.19, p. 306 from the first
    split of p. 303. No parent is globally selected. *)
Theorem circular_disc_ball_first_parent j (a:E) (t:R):
  A a ->0<=t ->is_circular_first_split H (metric_closed_ball a t) j.+1 ->
  exists z:E,z \in H j /\metric_closed_ball z (rho j) a /\
    (A `&` metric_closed_ball a t) `<=` (A `&` metric_closed_ball z (rho j)) /\
    forall w:E,w \in @circular_disc_hit_indices R H j.+1 (metric_closed_ball a t) ->
      exists k:'I_(j+4),w= circular_disc_child_center z (rho j) k.
Proof.
move=>ha ht hFirst.
have [z [hz [hSingleton hChildren]]]:= @circular_disc_first_split_parent R H
  (metric_closed_ball a t) hH j hFirst.
have hPoint x:A x ->metric_closed_ball a t x ->metric_closed_ball z (rho j) x.
  move=>hxA hxT.
  have [w [hw hxW]]:=(hA x).1 hxA j.
  have hwHit:w \in @circular_disc_hit_indices R H j (metric_closed_ball a t).
    apply/(@finite_cell_hit_indices_membership E E (H j)
      (fun c=>metric_closed_ball c (rho j)) (metric_closed_ball a t) w).
    split=>//;by exists x;split.
  rewrite hSingleton in hwHit.
  have hEqual:w= z by move:hwHit;rewrite in_fset1=>/eqP.
  by rewrite -hEqual.
have hSelf:metric_closed_ball a t a by change (is_true (mdist a a<=t));by rewrite mdistxx.
exists z;split=>//;split;first exact:hPoint a ha hSelf.
split=>// x [hxA hxT];split=>//;exact:hPoint x hxA hxT.
Qed.
End Parent.
