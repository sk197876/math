(** Federer (1969), 2.10.46, p. 204: the opposite Gross product inequality
    is obtained from 2.10.8, p. 175. For Borel factors, lift each
    second-factor Borel partition to disjoint rectangles. Their
    projected-volume costs dominate first-factor volume times the original
    partition costs. Taking the partition supremum gives the lower bound
    below. This file isolates finite positive first volume; passage to
    arbitrary sets is a separate obligation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  MetricProductRectangles EuclideanRectangleBorel EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  ProjectedVolumeGauge ProjectionMeasure ProductProjectedGaugeLower GrossBorelPartitions
  TopologicalBorel BorelPartition BorelPartitionCoverBounds BorelPartitionCharacterization
  BorelCostPartitionBound NonnegativeSum NonnegativeSumScale ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gross_borel_product_lower_finite_first]: direct
    lower product inequality of 2.10.46, p. 204,
    in the Borel-factor case with positive finite first volume.
    The second Gross measure may be infinite. Empty blocks
    are allowed by the coordinate and partition arguments. *)
Theorem gross_borel_product_lower_finite_first (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) (u : R) :
  (k<=n)%N -> borel_set U -> borel_set V ->
  0<u -> euclidean_lebesgue_measure m U=u%:E ->
  (u%:E*@gross_measure R n k V<=
    @gross_measure R (m+n) (m+k) (metric_product_rectangle
      (fun z=>(@euclidean_block_split R m n z).1)
      (fun z=>(@euclidean_block_split R m n z).2) U V))%E.
Proof.
move=> hkn hU hV hu hvol.
pose P := [the metricType R of inner_metric_space (@euclidean_inner_productP R (m+n))].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose first := fun z=>(@euclidean_block_split R m n z).1.
pose second := fun z=>(@euclidean_block_split R m n z).2.
pose S := fun B : set Y=>metric_product_rectangle first second U B.
have hdim : (m+k<=m+n)%N by rewrite leq_add2l.
rewrite -lee_pdivlMl // (@gross_measure_borel_partition_formula R n k V hkn hV).
apply: extended_real_sup_least=> z [H [hH ->]].
rewrite lee_pdivlMl //.
have hinc B : H B -> B `<=` V.
  move=> hB y hy; rewrite -(borel_partition_union hH); by exists B.
have hBorel B : H B -> borel_set (S B).
  move=> hB; exact: euclidean_rectangle_borel hU (borel_partition_members hH hB).
have hsub B : H B -> S B `<=` S V.
  move=> hB x [hx hy]; split=> //; exact (hinc B hB (second x) hy).
have hdis B C : H B -> H C -> B<>C -> S B `&` S C=set0.
  move=> hB hC hne; apply/seteqP; split=> // x [[_ hx] [_ hy]].
  have hh : (B `&` C) (second x) := conj hx hy.
  by rewrite (borel_partition_disjoint hH hB hC hne) in hh.
have hb := @borel_cost_disjoint_sum_bound R P (@projected_volume_gauge R (m+n) (m+k))
  (@projected_volume_gauge_borel_cover_cost R (m+n) (m+k) hdim)
  [the choiceType of set Y] H S (S V) hBorel hsub hdis.
apply: le_trans _ hb.
rewrite /borel_partition_cost -(@nonnegative_sum_scale R [the choiceType of set Y] H (@projected_volume_gauge R n k) u
  (ltW hu) (fun B _=>@projected_volume_gauge_nonnegative R n k B hkn)).
apply: nonnegative_sum_mono=> B hB.
exact (@product_projected_gauge_lower_finite_first R m n k U B u
  (@euclidean_borel_measurable R m U hU) (borel_partition_members hH hB) hu hvol).
Qed.
