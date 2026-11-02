(** Federer (1969), 2.10.29, p. 195: the actual finite Cartesian powers of a
    set of positive competing measure retain positive mass. Measurability
    follows from the product rectangle law and inverse Euclidean block
    identities. No topology assumption on the set is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanMeasurePowerUP EuclideanMeasurePower EuclideanBlockSetPower EuclideanBlockCoordinates EuclideanMetricProduct
  MeasureUP MeasurePushforward PushforwardMeasurableSets ProductMeasure ProductRectangleMeasurability
  MetricCartesianRectangleBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_measure_power_positive_set_power]: supporting
    positive mass of the finite mixed-product
    powers in 2.10.29, p. 195. Both
    the measure family and the set family
    are used only through their sealed laws. *)
Theorem euclidean_measure_power_positive_set_power (R : realType) d
    (nu : set (inner_metric_space (@euclidean_inner_productP R d)) -> \bar R) (hn : is_measure nu)
    (C : set (inner_metric_space (@euclidean_inner_productP R d))) :
  measure_measurable nu C -> 0<nu C -> forall q,
    measure_measurable (@euclidean_measure_power R d nu hn q) (@euclidean_block_set_power R d C q) /\
    0< @euclidean_measure_power R d nu hn q (@euclidean_block_set_power R d C q).
Proof.
move=> hC hpos; elim=> [|q ih].
- by rewrite euclidean_measure_power_firstE euclidean_block_set_power_firstE.
- rewrite euclidean_measure_power_successorE euclidean_block_set_power_successorE.
  pose a := euclidean_power_dimension d q.
  pose U := @euclidean_block_set_power R d C q.
  pose mu := @euclidean_measure_power R d nu hn q.
  pose hm := @euclidean_measure_power_is_measure R d nu hn q.
  split.
  + rewrite /paired_product_measure.
    apply: pushforward_measurable_from_preimage.
    have he : ((fun p : inner_metric_space (@euclidean_inner_productP R a)*inner_metric_space (@euclidean_inner_productP R d)=>
        @euclidean_block_join R a d (p.1,p.2)) @^-1`
      [set x | U (@euclidean_block_split R a d x).1 /\ C (@euclidean_block_split R a d x).2])=U `*` C.
      apply: funext=> p.
      change ((U (@euclidean_block_split R a d (@euclidean_block_join R a d (p.1,p.2))).1 /\
        C (@euclidean_block_split R a d (@euclidean_block_join R a d (p.1,p.2))).2)=(U p.1 /\ C p.2)).
      by rewrite euclidean_block_joinK.
    rewrite he; exact (@product_measure_rectangle_measurable R _ _ mu nu hm hn U C ih.1 hC).
  + rewrite (@paired_product_coordinate_rectangle_value R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R (a+d))]
      [the metricType R of inner_metric_space (@euclidean_inner_productP R a)]
      [the metricType R of inner_metric_space (@euclidean_inner_productP R d)]
      (fun x y=>@euclidean_block_join R a d (x,y))
      (fun x=>(@euclidean_block_split R a d x).1) (fun x=>(@euclidean_block_split R a d x).2)
      (@euclidean_blocks_are_metric_product R a d) mu nu hm hn U C ih.1 hC).
    exact: mule_gt0 ih.2 hpos.
Qed.
