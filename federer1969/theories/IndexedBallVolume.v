(** Federer (1969), 3.3.6, p. 293: the volume sum for
    the actual countable disjoint family of projected balls. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  EuclideanLebesgueDimensions EuclideanClosedBallVolume EuclideanBallVolume
  MeasureUP MeasureBasic MeasureCountableAdditivity BorelRegularMeasureUP
  TopologicalBorel NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_disjoint_indexed_ball_volume_bound]: the
    disjoint projected-ball volume comparison in Federer 3.3.6, p. 293,
    expanded using 2.1.3(3), p. 55, and the actual closed ball volume.
    Original indices, degree zero, empty families and noninjective
    original centre maps are allowed. Disjointness is only required
    on the selected family. *)
Theorem euclidean_disjoint_indexed_ball_volume_bound (R:realType) m (I:choiceType)
    (D:set I) (c:I->inner_metric_space (@euclidean_inner_productP R m))
    (r:I->R) a H:
  countable D ->(forall i,D i ->0<=r i) ->0<=H ->
  (forall i j,D i ->D j ->i<>j ->
    metric_closed_ball (c i) (r i) `&` metric_closed_ball (c j) (r j)=set0) ->
  (forall i,D i ->metric_closed_ball (c i) (r i) `<=` metric_closed_ball a H) ->
  (nonnegative_sum D (fun i=>(euclidean_unit_ball_volume R m*(r i)^+m)%:E)<=
    (euclidean_unit_ball_volume R m*H^+m)%:E)%E.
Proof.
move=>hCount hR hH hDisjoint hContain.
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
have hMeas i:measure_measurable mu (metric_closed_ball (c i) (r i)).
  apply:(borel_regular_borel_measurable hm (euclidean_lebesgue_borel_regular R m)).
  apply:closed_borel_set; exact:metric_closed_ball_closed.
have hDisjoint' i j:D i ->D j ->i!=j ->forall z,
    metric_closed_ball (c i) (r i) z ->metric_closed_ball (c j) (r j) z ->False.
  move=>hi hj hNe z hZi hZj.
  have hDifferent:i<>j by move=>hEq; move:hNe; by rewrite hEq eqxx.
  have hBoth:(metric_closed_ball (c i) (r i) `&` metric_closed_ball (c j) (r j)) z by split.
  by rewrite (hDisjoint i j hi hj hDifferent) in hBoth.
have hAdd:=@measure_countable_disjoint_additivity R _ I mu hm D
  (fun i=>metric_closed_ball (c i) (r i)) hCount (fun i _=>hMeas i) hDisjoint'.
have hSub:(\bigcup_(i in D) metric_closed_ball (c i) (r i)) `<=` metric_closed_ball a H.
  move=>z [i hi hZi]; exact:hContain i hi z hZi.
have hBound:(mu (\bigcup_(i in D) metric_closed_ball (c i) (r i))<=mu (metric_closed_ball a H))%E.
  exact:(@measure_mono R _ mu hm _ _ hSub).
rewrite hAdd /mu (@euclidean_closed_ball_normalized_volume R m a H hH) in hBound.
have hValues:nonnegative_sum D (fun i=>mu (metric_closed_ball (c i) (r i)))=
    nonnegative_sum D (fun i=>(euclidean_unit_ball_volume R m*(r i)^+m)%:E).
  apply:nonnegative_sum_ext=>i hi.
  exact:(@euclidean_closed_ball_normalized_volume R m (c i) (r i) (hR i hi)).
by rewrite -hValues; exact:hBound.
Qed.
