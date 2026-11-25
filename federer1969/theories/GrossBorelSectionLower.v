(** Supporting Federer (1969), 2.10.46, p. 204: the Gross measure of a Borel
    set bounds c times the Gross measure of any Borel parameter set on which
    all horizontal sections have first-factor volume at least c. Apply the
    Borel partition formula 2.10.8, p. 175, and lift its partition cells to
    disjoint pieces of the source. The projected-volume estimate is proved
    separately. This avoids sigma-finiteness assumptions on Gross measure.
    Source context and the partition argument: GrossBorelProductLower.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanLebesgueDimensions EuclideanRectangleBorel MetricProductRectangles
  ProjectedVolumeGauge ProjectionMeasure ProjectedSectionGaugeLower GrossBorelPartitions
  TopologicalBorel BorelFamilyBasic BorelPartition BorelPartitionCoverBounds BorelPartitionCharacterization
  BorelCostPartitionBound NonnegativeSum NonnegativeSumScale ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gross_borel_horizontal_sections_lower_bound]:
    supporting opposite Gross inequality in 2.10.46,
    p. 204, obtained with the help of 2.10.8,
    p. 175. Both Borel sets may have infinite measure;
    the scalar lower bound on their sections is positive. *)
Theorem gross_borel_horizontal_sections_lower_bound (R : realType) m n k
    (H : set (inner_metric_space (@euclidean_inner_productP R (m+n))))
    (B : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R) :
  (k<=n)%N -> borel_set H -> borel_set B -> (0<c)%R ->
  (forall y, B y -> c%:E<=euclidean_lebesgue_measure m
    [set x | H (@euclidean_block_join R m n (x,y))]) ->
  c%:E*@gross_measure R n k B<=@gross_measure R (m+n) (m+k) H.
Proof.
move=> hkn hH hB hc hsec.
pose P := [the metricType R of inner_metric_space (@euclidean_inner_productP R (m+n))].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose first := fun z=>(@euclidean_block_split R m n z).1.
pose second := fun z=>(@euclidean_block_split R m n z).2.
pose S := fun D : set Y=>H `&` metric_product_rectangle first second setT D.
have hdim : (m+k<=m+n)%N by rewrite leq_add2l.
rewrite -lee_pdivlMl // (@gross_measure_borel_partition_formula R n k B hkn hB).
apply: extended_real_sup_least=> z [F [hF ->]]; rewrite lee_pdivlMl //.
have hinc D : F D -> D `<=` B.
  move=> hD y hy; rewrite -(borel_partition_union hF); by exists D.
have hbor D : F D -> borel_set (S D).
  move=> hD; apply: (@borel_family_binary_intersection P setT _ (borel_sets_family P)) hH _.
  apply: euclidean_rectangle_borel _ (borel_partition_members hF hD).
  exact: open_borel_set openT.
have hsub D : F D -> S D `<=` H by move=> _ x [hx _].
have hdis D E : F D -> F E -> D<>E -> S D `&` S E=set0.
  move=> hD hE hne; apply/seteqP; split=> // x [[_ [_ hx]] [_ [_ hy]]].
  have hh : (D `&` E) (second x) := conj hx hy.
  by rewrite (borel_partition_disjoint hF hD hE hne) in hh.
have hb := @borel_cost_disjoint_sum_bound R P (@projected_volume_gauge R (m+n) (m+k))
  (@projected_volume_gauge_borel_cover_cost R (m+n) (m+k) hdim)
  [the choiceType of set Y] F S H hbor hsub hdis.
apply: le_trans _ hb.
rewrite /borel_partition_cost -(@nonnegative_sum_scale R [the choiceType of set Y] F
  (@projected_volume_gauge R n k) c (ltW hc)
  (fun D _=>@projected_volume_gauge_nonnegative R n k D hkn)).
apply: nonnegative_sum_mono=> D hD.
apply: (@projected_horizontal_sections_gauge_lower_bound R m n k (S D) D c hc)=> y hy.
have he : [set x | S D (@euclidean_block_join R m n (x,y))]=
    [set x | H (@euclidean_block_join R m n (x,y))].
  apply/seteqP; split=> [x [hx _]|x hx] //.
  split=> //; change (True /\ D ((@euclidean_block_split R m n (@euclidean_block_join R m n (x,y))).2)).
  by rewrite euclidean_block_joinK.
rewrite he; exact: hsec (hinc D hD y hy).
Qed.
