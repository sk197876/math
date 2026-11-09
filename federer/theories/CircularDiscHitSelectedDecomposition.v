(** Federer (1969), 3.3.19, p. 304:
    the original finer hit mass is exactly the sum
    over original coarser discs which meet the test
    set. Nonmeeting pieces contribute zero. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls FactorialDiscScalesSealed
  CircularDiscTreeUP CircularDiscHitMeasureUP CircularDiscHitMeasureLaws CircularDiscHitCount
  CircularDiscHitDecomposition FiniteCellHitMeasureUP FiniteCellHitIndicesLaws MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [circular_disc_hit_selected_decomposition]:
    exact sum over those B in G_n meeting S,
    in the last cyclic equality of 3.3.19,
    p. 304. Every original test set is
    allowed; measurable coarse discs, rather than
    arbitrary-set additivity, supply the decomposition. *)
Theorem circular_disc_hit_selected_decomposition (R:realType)
    (H:nat->{fset (inner_metric_space (@euclidean_inner_productP R 2))})
    (psi:nat->set (inner_metric_space (@euclidean_inner_productP R 2))->\bar R):
  is_circular_disc_tree H ->is_circular_disc_hit_measures H psi ->
  forall j k (T:set (inner_metric_space (@euclidean_inner_productP R 2))),(j<=k)%N ->
  psi k T=\sum_(z<-@circular_disc_hit_indices R H j T)
    psi k (metric_closed_ball z (@FactorialDiscScales.radius R j) `&` T).
Proof.
move=>hH hPsi j k T hjk.
rewrite (@circular_disc_hit_coarse_decomposition R H hH psi hPsi j k T hjk).
have hOrder:(\sum_(z<-@circular_disc_hit_indices R H j T)
    psi k (T `&` metric_closed_ball z (@FactorialDiscScales.radius R j)))=
    \sum_(z<-H j) psi k (T `&` metric_closed_ball z (@FactorialDiscScales.radius R j)).
  apply:big_fset_incl.
  - exact:finite_cell_hit_indices_subset.
  - move=>z hz hNot.
    have hEmpty:T `&` metric_closed_ball z (@FactorialDiscScales.radius R j)=set0.
      apply/seteqP;split=>[x [hxT hxBall]|x []].
      have hHit:z \in @circular_disc_hit_indices R H j T.
        apply/finite_cell_hit_indices_membership;split=>//;by exists x;split.
      by move:hNot;rewrite hHit.
    rewrite hEmpty;exact:(measure_empty (@circular_disc_hit_is_measure R H psi hPsi k)).
rewrite -hOrder;apply:eq_bigr=>z _;by rewrite setIC.
Qed.
