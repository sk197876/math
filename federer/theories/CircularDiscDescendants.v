(** Federer (1969), 3.3.19, pp. 302–303:
    every original level disc has descendants at every
    later level and contains a point of the original
    limiting set. Nonempty pieces are proved, never imposed
    as an additional tree or measure law. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls EuclideanClosedBallCompact
  CompactNestedIntersection FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscRefinement CircularDiscTreeUP CircularDiscTreeTopology CircularDiscLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Descendants.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Local Notation N:=(@FactorialDiscScales.count R).
Local Notation hs:=(@FactorialDiscScales.laws R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_descendant_exists]: every
    original disc has an actual descendant at every later
    original level, supporting the count and measure
    assertions in 3.3.19, pp. 302–303. *)
Lemma circular_disc_descendant_exists j (z:E):z \in H j ->forall m,
  exists w:E,w \in H (j+m)%N /\
    metric_closed_ball w (rho (j+m)%N) `<=` metric_closed_ball z (rho j).
Proof.
move=>hz;elim=>[|m [w [hw hInside]]].
- exists z;rewrite addn0;split=>//;exact:subset_refl.
- have hPositive:(0<(j+m)+4)%N by rewrite addn_gt0 orbT.
  pose k:'I_((j+m)+4):=Ordinal hPositive.
  have hIndex:(j+m.+1=(j+m).+1)%N by rewrite addnS.
  exists (circular_disc_child_center w (rho (j+m)%N) k);rewrite hIndex;split.
  + rewrite (circular_disc_tree_step hH);apply/circular_disc_refinement_membership.
    by exists w,k;split.
  + exact:subset_trans (@circular_disc_child_containment R (j+m)%N w k) hInside.
Qed.

(** Source for [circular_disc_limit_meets_every_disc]:
    each original G_n disc meets the actual original A,
    supporting psi_n(A)=1 and the level-piece identities
    in 3.3.19, pp. 303–304. Nested actual compact
    descendants supply a point; none is globally selected. *)
Theorem circular_disc_limit_meets_every_disc (A:set E):
  is_circular_disc_limit H A ->forall j (z:E),z \in H j ->
  A `&` metric_closed_ball z (rho j)!=set0.
Proof.
move=>hA j z hz.
pose K:=fun m:nat=>metric_closed_ball z (rho j) `&` circular_disc_level_union H (j+m)%N.
have hClosed m:closed (K m).
  apply:closedI;first exact:metric_closed_ball_closed.
  exact:(@circular_disc_level_closed R H (j+m)%N).
have hCompact:compact (K 0%N).
  exact:(@compact_closedI E (metric_closed_ball z (rho j))
    (circular_disc_level_union H (j+0)%N) (@euclidean_closed_metric_ball_compact R 2 z (rho j))
    (@circular_disc_level_closed R H (j+0)%N)).
have hNested m n:(m<=n)%N ->K n `<=` K m.
  move=>hmn x [hxBall hxLevel];split=>//.
  have hIndices:(j+m<=j+n)%N by rewrite leq_add2l.
  exact:(@circular_disc_levels_nested R H hH (j+m)%N (j+n)%N hIndices x hxLevel).
have hNonempty m:K m!=set0.
  have [w [hw hInside]]:=@circular_disc_descendant_exists j z hz m.
  have hwBall:metric_closed_ball w (rho (j+m)%N) w.
    change (is_true (mdist w w<=rho (j+m)%N));rewrite mdistxx.
    exact:ltW (@factorial_disc_radius_positive R N rho hs (j+m)%N).
  exists w;split;first exact:hInside w hwBall.
  by exists w;split.
have [x hx]:=@compact_nested_nonempty_intersection E K hCompact hClosed hNested hNonempty.
exists x;split.
- apply:(hA x).2=>m.
  have hLevel:=(hx m Logic.I).2.
  exact:(@circular_disc_levels_nested R H hH m (j+m)%N (leq_addl j m) x hLevel).
- exact:(hx 0%N Logic.I).1.
Qed.
End Descendants.
