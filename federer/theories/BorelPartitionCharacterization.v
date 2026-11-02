(** Federer (1969), 2.10.8, p. 175, first display: the constructed measure
    of a Borel target is the supremum of cost sums over all its Borel
    partitions. Small Borel partitions of a separable metric space supply
    the reverse inequality; no nestedness is imposed on the family in the
    supremum. No relevant mathematical correction occurs in the local
    erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import BorelPartition TopologicalBorel BorelCoverCostUP
  BorelCaratheodoryMeasure BorelPartitionCoverBounds SmallBorelPartitionFamilies
  MetricDiameter MetricScaleEnvelopeUP CaratheodoryLimitUP CaratheodoryBorelRegular
  ExtendedRealBoundsUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_partition_cost_values]: direct family
    of numerical sums in the first display of Federer 2.10.8,
    p. 175, ranging over every Borel partition of A. *)
Definition borel_partition_cost_values (R : realType) (X : topologicalType)
    (c : set X -> \bar R) (A : set X) :=
  [set a | exists H, is_borel_partition A H /\ a=borel_partition_cost c H].

(** Source for [borel_partition_cost_supremum_all]: direct
    supremum assertion of Federer 2.10.8, p. 175. The abstract
    supremum laws include infinite measure and empty target cases. *)
Theorem borel_partition_cost_supremum_all (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c) (D A : set X) :
  countable D -> dense D -> borel_set A ->
  is_extended_real_supremum (borel_partition_cost_values c A) (borel_caratheodory_measure c A).
Proof.
move=> hD hden hA; constructor.
- move=> a [H [hH ->]]; exact: (@borel_partition_cost_upper R X c hc A H hH).
- move=> b hb.
  apply: (caratheodory_limit_least (borel_caratheodory_specification c))=> delta nu hp hn.
  have [k hk] := reciprocal_metric_cutoffs_cofinal hp.
  pose e : R := (((k.+1)%:R)^-1)%R.
  have he : (0<e)%R by rewrite /e invr_gt0 ltr0n.
  have [H [hH hd]] := @small_borel_partition_family_exists R X D A e hD hden hA he.
  have hd' B : H B -> extended_metric_diameter B<=delta.
    move=> hB; exact: le_trans (hd B hB) hk.
  apply: le_trans (@borel_partition_scale_bound R X c hc A H delta nu hH hn hd') _.
  apply: hb; exists H; by split.
Qed.

(** Source for [borel_partition_cost_formula]: direct first
    displayed equation in Federer 2.10.8, p. 175, with the
    sealed extended-real supremum operator on its right side. *)
Corollary borel_partition_cost_formula (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c) (D A : set X) :
  countable D -> dense D -> borel_set A ->
  borel_caratheodory_measure c A=extended_real_sup (borel_partition_cost_values c A).
Proof.
move=> hD hden hA.
apply: extended_real_supremum_unique (@borel_partition_cost_supremum_all R X c hc D A hD hden hA) _.
constructor; [exact: extended_real_sup_upper|exact: extended_real_sup_least].
Qed.
