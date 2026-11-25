(** Federer (1969), 3.1.8, p. 218: countably
    many measurable Lipschitz restrictions cover the actual domain.
    The small-diameter partitions are used only through their
    existing sealed specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes EuclideanMetricSeparability SmallBorelPartitionUP
  SmallBorelPartitionSealed TopologicalBorel LipschitzUP
  PartialFunctionUP PartialFunctionBasic MeasurableFunctionUP MeasureUP MeasureFiniteClosure
  MeasureSetDensity CenteredBallRelations ApproximateMetricGrowth
  EuclideanGrowthCutoffs EuclideanGrowthCutoffLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_growth_lipschitz_decomposition]:
    the family B_(j,k) in the conclusion and final proof
    paragraph of Federer 3.1.8, pp. 217–218.
    The family is indexed by pairs of natural numbers, a
    countable set. No measurable or Lipschitz assertion about
    the auxiliary values outside A enters the conclusion. *)
Theorem euclidean_growth_lipschitz_decomposition (R : realType) m
    (Y : metricType R) (D : set Y)
    (A : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m)->Y) :
  countable D -> dense D ->
  measure_measurable (@euclidean_lebesgue_measure R m) A ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m) (partial_function_total f) ->
  (forall a, A a -> exists M : R, 0<M /\
    partial_function_graph
      (measure_set_density (@euclidean_lebesgue_measure R m)
        (@centered_closed_ball_relation R
          [the metricType R of inner_metric_space (@euclidean_inner_productP R m)])
        (metric_growth_exception A f a M)) a 0%E) ->
  exists F : (nat*nat)->set (inner_metric_space (@euclidean_inner_productP R m)),
    (forall q, measure_measurable (@euclidean_lebesgue_measure R m) (F q) /\
      F q `<=` A /\ is_metric_lipschitz (F q) f) /\
    A=\bigcup_q F q.
Proof.
move=> hc hd hA hf hfinite.
pose X := inner_metric_space (@euclidean_inner_productP R m).
have [Dx [hDxc hDxd]] := euclidean_metric_separable R m.
pose e j : R := (j.+1%:R)^-1/2.
have he j : 0<e j by rewrite /e divr_gt0 ?invr_gt0 ?ltr0n.
pose P j := @SmallBorelPartition.value R [the metricType R of X] Dx (e j) hDxc hDxd (he j).
have hP j : is_small_borel_partition (e j) (P j) :=
  @SmallBorelPartition.laws R [the metricType R of X] Dx (e j) hDxc hDxd (he j).
pose F (q : nat*nat) := euclidean_growth_cutoff A f q.1 `&` P q.1 q.2.
exists F; split.
- move=> [j k]; split.
  + apply: (measure_measurable_intersection (euclidean_lebesgue_is_measure R m)).
    * exact: euclidean_growth_cutoff_measurable hc hd hA hf.
    * exact: (@euclidean_borel_measurable R m (P j k) (small_partition_borel (hP j) k)).
  + split; first by move=> x [hx _]; exact: hx.1.
    apply: (@euclidean_growth_cutoff_small_piece_lipschitz R m Y A (F (j,k)) f j).
    * by move=> x [hx _].
    * move=> u v [_ hu] [_ hv].
      apply: (le_lt_trans (@small_partition_diameter R [the metricType R of X] (e j) (P j) (hP j) k u v hu hv) _).
      have hp : (0<(j.+1%:R : R)^-1) by rewrite invr_gt0 ltr0n.
      have h2 : (0<(2 : R)) by rewrite ltr0n.
      change (is_true ((j.+1%:R : R)^-1/2<(j.+1%:R : R)^-1)).
      by rewrite (ltr_pdivrMr _ _ h2) ltr_pMr // ltr1n.
- apply/seteqP; split=> a.
  + move=> ha; have [j hj] := euclidean_growth_cutoff_covers ha (hfinite a ha).
    have hp : (\bigcup_k P j k) a by rewrite (small_partition_cover (hP j)).
    have [k _ hk] := hp; exists (j,k); first exact Logic.I; by split.
  + by move=> [[j k] _ [hj _]]; exact: hj.1.
Qed.
