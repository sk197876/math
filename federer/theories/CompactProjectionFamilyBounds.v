(** Federer (1969), 3.2.37, p. 274: every compact projection
    family cost is bounded by Gross measure and by lower Minkowski
    content. Empty families have zero cost. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions CompactProjectionFamilyUP ProjectedVolumeGauge ProjectionMeasure
  BorelCostPartitionBound FiniteCoverMeasureBounds NonnegativeSum MeasureUP MeasureBasic
  TopologicalBorel MinkowskiContents FiniteCompactMinkowskiProjectionSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_projected_family_gross_bound]: the easy
    upper-bound half of the compact-family supremum asserted in
    Federer 3.2.37, p. 274. It follows from 2.10.8 on the
    actual compact pieces. The containing A is arbitrary. *)
Lemma compact_projected_family_gross_bound (R:realType) n m
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (I:finType)
    (K:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:I->{linear R_n R n->R_n R m}):
  (m<=n)%N ->is_finite_compact_projected_family A K p ->
  (\sum_i @euclidean_lebesgue_measure R m (p i @` K i))<=@gross_measure R n m A.
Proof.
move=>hmn hFamily.
pose X:=[the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose cost:=@projected_volume_gauge R n m.
have hBorel i:borel_set (K i).
  have hK:=@compact_projected_family_compact R n m A I K p hFamily i.
  exact:(@closed_borel_set X (K i) (@compact_closed X (K i)
    (@metric_hausdorff R X) hK)).
have hDisjoint i j:setT i ->setT j ->i<>j ->K i `&` K j=set0.
  move=>_ _ hij; apply/seteqP; split=>[x [hix hjx]|x []].
  have hNe:i!=j by apply/eqP.
  exfalso; exact:(@compact_projected_family_disjoint R n m A I K p hFamily i j hNe x hix hjx).
have hBound:=@borel_cost_disjoint_sum_bound R X cost
  (@projected_volume_gauge_borel_cover_cost R n m hmn) I setT K A
  (fun i _=>hBorel i) (fun i _=>@compact_projected_family_subset R n m A I K p hFamily i) hDisjoint.
have hNonnegative i:0<=cost (K i):=projected_volume_gauge_nonnegative (K i) hmn.
rewrite (finite_type_nonnegative_sum hNonnegative) in hBound.
apply:le_trans _ hBound; apply:lee_sum=>i _.
exact:(@projected_volume_gauge_projection_bound R n m (K i) (p i)
  (@compact_projected_family_projection R n m A I K p hFamily i)).
Qed.

(** Source for [compact_projected_family_lower_minkowski_bound]:
    the compact-family comparison in Federer 3.2.37, p. 274,
    through the independently specified family laws. *)
Lemma compact_projected_family_lower_minkowski_bound (R:realType) n m
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (I:finType)
    (K:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:I->{linear R_n R n->R_n R m}):
  (m<=n)%N ->is_finite_compact_projected_family A K p ->
  (\sum_i @euclidean_lebesgue_measure R m (p i @` K i))<=lower_minkowski_content m A.
Proof.
move=>hmn hFamily.
exact:(@finite_type_compact_projection_lower_minkowski R n m I K p A hmn
  (fun i=>@compact_projected_family_compact R n m A I K p hFamily i)
  (fun i=>@compact_projected_family_subset R n m A I K p hFamily i)
  (fun i=>@compact_projected_family_projection R n m A I K p hFamily i)
  (fun i j=>@compact_projected_family_disjoint R n m A I K p hFamily i j)).
Qed.

(** Source for [compact_projected_family_empty_value]: the empty
    finite family contributes zero to the supremum in Federer
    3.2.37, p. 274, for every source and every degree. *)
Lemma compact_projected_family_empty_value (R:realType) n m
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  compact_projected_family_values m A 0.
Proof.
have p:'I_0->{linear R_n R n->R_n R m}.
  move=>i; have hi:=ltn_ord i; by rewrite ltn0 in hi.
exists ([the finType of 'I_0]),(fun _:'I_0=>set0),p.
split; last by rewrite big_ord0.
constructor; move=>i; have hi:=ltn_ord i; by rewrite ltn0 in hi.
Qed.
