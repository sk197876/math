(** Federer (1969), 3.3.19, pp. 303 and 306:
    positive original balls have an actual first splitting
    level, and small ball radii force that level late. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls MetricDiameterUP MetricDiameter
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscRefinement CircularDiscTreeUP CircularDiscTreeTopology CircularDiscTreeExactCount CircularDiscLimitUP CircularDiscLevelPieces
  CircularDiscHitCount CircularDiscFirstSplitUP CircularDiscFirstSplit CircularDiscHitDiameter CircularDiscSmallCutoff
  FiniteCellHitMeasureUP FiniteCellHitIndicesLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Split.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation hS:=(@FactorialDiscScales.laws R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_positive_ball_first_split]:
    every positive original ball centered at a in A
    has an actual first split j+1. A fine whole
    original parent lies in that ball, so all its
    actual children are hit. Their proved exact count
    supplies splitting; natural minimality gives the first
    level, supporting 3.3.19, pp. 303 and 306. *)
Theorem circular_disc_positive_ball_first_split (a:E) (t:R):
  A a ->0<t ->exists j:nat,is_circular_first_split H (metric_closed_ball a t) j.+1.
Proof.
move=>ha ht.
have hHalf:0<t/2 by lra.
have [K hRadius]:= @factorial_disc_radius_small R (@FactorialDiscScales.count R) rho hS (t/2) hHalf.
have hSmall:= hRadius K (leqnn K).
have [z [hz haZ]]:=(hA a).1 ha K.
have hContains:metric_closed_ball z (rho K) `<=` metric_closed_ball a t.
  move=>x hx.
  have h:= @circular_disc_within_ball_distance R K z a x haZ hx.
  change (is_true (mdist a x<=t));lra.
pose F:=[fset circular_disc_child_center z (rho K) k|k:'I_(K+4)].
have hSubset:(F `<=` @circular_disc_hit_indices R H K.+1 (metric_closed_ball a t))%fset.
  apply/fsubsetP=>w /imfsetP[k _ hW].
  have hChild:metric_closed_ball (circular_disc_child_center z (rho K) k) (rho K.+1) w.
    rewrite hW;change (is_true (mdist (circular_disc_child_center z (rho K) k) (circular_disc_child_center z (rho K) k)<=rho K.+1)).
    rewrite mdistxx;exact:ltW (@factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho hS K.+1).
  have hParent:= @circular_disc_child_containment R K z k w hChild.
  apply/(@finite_cell_hit_indices_membership E E (H K.+1)
    (fun c=>metric_closed_ball c (rho K.+1)) (metric_closed_ball a t) w).
  split.
  - rewrite (circular_disc_tree_step hH);apply/circular_disc_refinement_membership.
    by exists z,k;split.
  - exists w;split;last exact:hContains w hParent.
    change (is_true (mdist w w<=rho K.+1));rewrite mdistxx.
    exact:ltW (@factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho hS K.+1).
have hKN:(4<=K+4)%N by exact:leq_addl.
have hPositive:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho hS K.
have hCard:#|` F|=(K+4)%N:= @circular_disc_child_count R z (rho K) (K+4)%N hPositive hKN.
have hHits:= fsubset_leq_card hSubset.
rewrite hCard in hHits.
have hCount:(2<=#|` @circular_disc_hit_indices R H K.+1 (metric_closed_ball a t)|)%N.
  exact:leq_trans (leq_trans (erefl true:(2<=4)%N) hKN) hHits.
have [j [_ hFirst]]:= @circular_disc_first_split_exists R H (metric_closed_ball a t) K.+1 hCount.
have hJPositive:= @circular_disc_first_split_positive R H (metric_closed_ball a t) hH j hFirst.
case:j hFirst hJPositive=>[|j] hFirst hPositiveJ;first by [].
by exists j.
Qed.

(** Source for [circular_disc_small_balls_split_late]: for
    every original level J there is a positive actual
    radius cutoff such that every first-split parent of
    a smaller original ball has index at least J.
    Actual disc separation and the ball diameter bound
    prove this cutoff for the final density argument
    in 3.3.19, p. 306. *)
Theorem circular_disc_small_balls_split_late J:exists delta:R,0<delta /\
  forall (a:E) (t:R) j,0<t ->t<delta ->
  is_circular_first_split H (metric_closed_ball a t) j.+1 ->(J<=j)%N.
Proof.
have hRadius:= @factorial_disc_radius_positive R (@FactorialDiscScales.count R) rho hS J.+1.
exists (rho J.+1/4);split;first by lra.
move=>a t j ht htSmall hFirst.
have hDiameter:(extended_metric_diameter (metric_closed_ball a t)<=(2* t)%:E)%E.
  apply:(metric_diameter_least (extended_metric_diameter_specification _)).
  - rewrite lee_fin;lra.
  - move=>x y hx hy;rewrite lee_fin.
    have h:=metric_closed_ball_diameter_bound hx hy;lra.
have hSmall:= @circular_disc_two_hits_radius_below_diameter R H hH j.+1 (metric_closed_ball a t) (2* t)
  hFirst.1 hDiameter.
rewrite leqNgt;apply/negP=>hBefore.
have hBeforeS:(j.+1<=J.+1)%N:=leq_trans hBefore (leqnSn J).
have hOrder:= @factorial_disc_radius_antitone R j.+1 J.+1 hBeforeS.
exfalso;lra.
Qed.
End Split.
