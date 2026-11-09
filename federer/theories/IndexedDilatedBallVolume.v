(** Federer (1969), 3.3.6, p. 293: rescale the actual
    disjoint projected-ball volume sum by the fifth power factor. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  EuclideanBallVolume IndexedBallVolume NonnegativeSum NonnegativeSumSupport NonnegativeSumScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_disjoint_dilated_ball_volume_bound]: the
    displayed sum bound in Federer 3.3.6, p. 293, obtained by multiplying
    the disjoint small-ball sum by 5 to power m. The supporting statement
    allows every nonnegative finite dilation and retains degree zero. *)
Theorem euclidean_disjoint_dilated_ball_volume_bound (R:realType) m (I:choiceType)
    (D:set I) (c:I->inner_metric_space (@euclidean_inner_productP R m))
    (r:I->R) a H L:
  countable D ->(forall i,D i ->0<=r i) ->0<=H ->0<=L ->
  (forall i j,D i ->D j ->i<>j ->
    metric_closed_ball (c i) (r i) `&` metric_closed_ball (c j) (r j)=set0) ->
  (forall i,D i ->metric_closed_ball (c i) (r i) `<=` metric_closed_ball a H) ->
  (nonnegative_sum D (fun i=>(euclidean_unit_ball_volume R m*(L*r i)^+m)%:E)<=
    (euclidean_unit_ball_volume R m*(L*H)^+m)%:E)%E.
Proof.
move=>hCount hR hH hL hDisjoint hContain.
have hBound:=euclidean_disjoint_indexed_ball_volume_bound hCount hR hH hDisjoint hContain.
have hCoefficient:0<=L^+m by apply:exprn_ge0.
have hTerms i:D i ->(0<=(euclidean_unit_ball_volume R m*(r i)^+m)%:E)%E.
  move=>hi; rewrite lee_fin; apply:mulr_ge0; first exact:ltW (euclidean_unit_ball_volumeE R m).2.
  apply:exprn_ge0; exact:hR i hi.
have hValues:nonnegative_sum D (fun i=>(euclidean_unit_ball_volume R m*(L*r i)^+m)%:E)=
    ((L^+m)%:E*nonnegative_sum D (fun i=>(euclidean_unit_ball_volume R m*(r i)^+m)%:E))%E.
  rewrite -(@nonnegative_sum_scale R I D
    (fun i=>(euclidean_unit_ball_volume R m*(r i)^+m)%:E) (L^+m) hCoefficient hTerms).
  apply:nonnegative_sum_ext=>i hi; by rewrite -EFinM exprMn mulrCA.
rewrite hValues.
have hScaled:=@lee_wpmul2l R (L^+m)%:E (lee_tofin hCoefficient) _ _ hBound.
rewrite exprMn.
by rewrite -EFinM mulrCA in hScaled.
Qed.
