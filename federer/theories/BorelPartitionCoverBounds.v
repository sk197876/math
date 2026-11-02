(** Federer (1969), 2.10.8, p. 175: costs of arbitrary Borel partitions lie
    below the final measure, while a partition with sufficiently small mesh
    bounds each size approximation from above. These statements do not
    require nestedness, refinement, or separability. The latter is used only
    to produce small partitions. No relevant mathematical correction occurs
    in Federer's local LaTeX erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSumSupport TopologicalBorel BorelPartition
  BorelCoverCostUP BorelCaratheodoryMeasure BorelCostPartitionBound
  MetricDiameter MetricScaleEnvelopeUP MetricScaleIndexedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_partition_cost]: direct numerical sum
    over a Borel partition H in the two displays of Federer
    2.10.8, p. 175. H is a family of sets, not an enumeration. *)
Definition borel_partition_cost (R : realType) (X : Type)
    (c : set X -> \bar R) (H : set (set X)) := nonnegative_sum H c.

(** Source for [borel_partition_cost_upper]: direct upper
    inequality in the proof of Federer 2.10.8, p. 175,
    for every Borel partition of A, including empty families. *)
Lemma borel_partition_cost_upper (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (A : set X) (H : set (set X)) :
  is_borel_partition A H -> borel_partition_cost c H<=borel_caratheodory_measure c A.
Proof.
move=> hH; apply: (@borel_cost_disjoint_sum_bound R X c hc
  [the choiceType of set X] H (fun B => B) A).
- exact: borel_partition_members hH.
- move=> B hB x hx; rewrite -(borel_partition_union hH); by exists B.
- exact: borel_partition_disjoint hH.
Qed.

(** Source for [borel_partition_scale_bound]: direct covering
    inequality implicit in the last display of the proof of
    Federer 2.10.8, p. 175. Any Borel partition whose members
    have diameter at most delta is an admissible cover for that
    size approximation. No refinement hypothesis is needed. *)
Lemma borel_partition_scale_bound (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (A : set X) (H : set (set X)) (delta : \bar R) (nu : set X -> \bar R) :
  is_borel_partition A H ->
  is_metric_scale_envelope (fun j : @borel_metric_sets R X => val j)
    (fun j => c (val j)) delta nu ->
  (forall B, H B -> extended_metric_diameter B<=delta) ->
  nu A<=borel_partition_cost c H.
Proof.
move=> hH hn hd.
pose z0 : @borel_metric_sets R X := Sub set0 (mem_set (@open_borel_set X set0 open0)).
pose u (B : set X) := insubd z0 B.
have hu B : H B -> val (u B)=B.
  move=> hB; by rewrite /u val_insubd (mem_set (borel_partition_members hH hB)).
have hnon B : H B -> 0<=c (val (u B)).
  move=> hB; rewrite (hu B hB); exact: (@borel_cover_cost_nonnegative R X c hc B (borel_partition_members hH hB)).
have hdiam B : H B -> extended_metric_diameter (val (u B))<=delta.
  move=> hB; rewrite (hu B hB); exact: hd.
have hcover : A `<=` \bigcup_(B in H) val (u B).
  move=> x; rewrite -(borel_partition_union hH)=> [[B hB hx]].
  exists B=> //; by rewrite (hu B hB).
have hb := @metric_scale_envelope_indexed_cover R X (@borel_metric_sets R X)
  [the choiceType of set X] (fun j => val j) (fun j => c (val j)) delta nu hn A H u
  (borel_partition_countable hH) hnon hdiam hcover.
have hs : nonnegative_sum H (fun B => c (val (u B)))=borel_partition_cost c H.
  apply: nonnegative_sum_ext=> B hB; by rewrite (hu B hB).
by rewrite hs in hb.
Qed.
