(** Federer (1969), 3.2.37, p. 274: on every Borel source,
    Gross measure is exactly the supremum of the actual projected
    volumes of finite disjoint compact source families. Expand the
    citation of 2.10.8 through compact image approximation. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions CoordinateProjection EuclideanMetricSeparability CompactProjectionFamilyUP
  CompactProjectionFamilyBounds CompactProjectedVolumeDetection FiniteCompactProjectionApproximation
  ProjectedVolumeGauge ProjectionMeasure BorelPartition BorelPartitionCharacterization
  BorelPartitionCoverBounds BorelClosedProjection TopologicalBorel NonnegativeSum
  ExtendedRealBoundsUP ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_projected_family_single_value]: a one-member
    compact family is admissible in the supremum of Federer
    3.2.37, p. 274. The actual projected mass may be zero. *)
Lemma compact_projected_family_single_value (R:realType) n m
    (A K:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:{linear R_n R n->R_n R m}):
  compact K ->K `<=` A ->O_star p ->
  compact_projected_family_values m A (@euclidean_lebesgue_measure R m (p @` K)).
Proof.
move=>hK hKA hp.
exists ([the finType of 'I_1]),(fun _:'I_1=>K),(fun _:'I_1=>p).
split; last by rewrite big_ord1.
constructor=>// i j hij x hix hjx.
by move:hij; rewrite (ord1 i) (ord1 j) eqxx.
Qed.

(** Source for [gross_borel_compact_projection_least_bound]: the
    difficult least-bound half of the compact-family supremum in
    Federer 3.2.37, p. 274. Every finite partition cost is
    approximated by actual compact source projections with one finite
    total error. No local finiteness of Gross measure is assumed. *)
Lemma gross_borel_compact_projection_least_bound (R:realType) n m
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (b:R):
  (m<=n)%N ->borel_set A ->
  (forall v,compact_projected_family_values m A v ->v<=b%:E) ->
  @gross_measure R n m A<=b%:E.
Proof.
move=>hmn hA hBound.
have hGauge (S:set (inner_metric_space (@euclidean_inner_productP R n))):
    borel_set S ->S `<=` A ->projected_volume_gauge m S<=b%:E.
  move=>hS hSA; rewrite leNgt; apply/negP=>hLarge.
  have [K [p [hK hKS hp hCost]]]:=projected_volume_gauge_compact_detection
    (metric_borel_suslin hS) hLarge.
  have hKA:K `<=` A:=fun x hx=>hSA x (hKS x hx).
  have hValue:=@compact_projected_family_single_value R n m A K p hK hKA hp.
  have hFalse:=lt_le_trans hCost (hBound _ hValue); by rewrite ltxx in hFalse.
have [D [hD hDense]]:=euclidean_metric_separable R n.
have hSup:=@borel_partition_cost_supremum_all R
  (inner_metric_space (@euclidean_inner_productP R n)) (@projected_volume_gauge R n m)
  (@projected_volume_gauge_borel_cover_cost R n m hmn) D A hD hDense hA.
apply:(extended_real_supremum_least hSup)=>v [H [hH ->]].
apply:nonnegative_sum_least=>B hBH.
have hBA (i:B):val i `<=` A.
  move=>x hx; rewrite -(borel_partition_union hH); exists (val i)=>//.
  exact:hBH (val i) (fsvalP i).
have hBorel (i:B):borel_set (val i):=borel_partition_members hH (hBH _ (fsvalP i)).
have hFinite (i:B):projected_volume_gauge m (val i)< +oo.
  exact:le_lt_trans (hGauge (val i) (hBorel i) (hBA i)) (ltry b).
apply:(@extended_upper_bound_from_scaled_errors R _ b 1%R ler01)=>e he.
have [K [p [hKP hApprox]]]:=@finite_compact_projection_approximation R n m
  [the finType of (B:Type)] (fun i:B=>val i) e hmn
  (fun i=>metric_borel_suslin (hBorel i)) hFinite he.
have hFamily:is_finite_compact_projected_family A K p.
  constructor.
  - move=>i; exact:(hKP i).1.
  - move=>i x hx; exact:hBA i x ((hKP i).2.1 x hx).
  - move=>i; exact:(hKP i).2.2.
  - move=>i j hij x hix hjx.
    have hNe:val i<>val j.
      move=>hValue; have hEq:i=j:=val_inj hValue.
      by move:hij; rewrite hEq eqxx.
    have hEmpty:=borel_partition_disjoint hH (hBH _ (fsvalP i)) (hBH _ (fsvalP j)) hNe.
    have hX:(val i `&` val j) x by split; [exact:(hKP i).2.1|exact:(hKP j).2.1].
    by rewrite hEmpty in hX.
have hValue:compact_projected_family_values m A
    (\sum_i @euclidean_lebesgue_measure R m (p i @` K i)).
  exists ([the finType of (B:Type)]),K,p; by split.
have hSum:=hBound _ hValue.
rewrite big_seq_fsetE; apply:le_trans hApprox _.
rewrite mul1r EFinD; exact:leeD hSum (lexx e%:E).
Qed.

(** Source for [gross_measure_compact_projection_supremum]: the
    full supremum statement in the last paragraph of Federer
    3.2.37, p. 274, for every Borel A, all admissible natural
    dimensions and infinite values. The family laws precede this
    proved characterization; no maximizing family is assumed. *)
Theorem gross_measure_compact_projection_supremum (R:realType) n m
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  (m<=n)%N ->borel_set A ->
  is_extended_real_supremum (compact_projected_family_values m A) (@gross_measure R n m A).
Proof.
move=>hmn hA; constructor.
- move=>v [I [K [p [hFamily ->]]]].
  exact:compact_projected_family_gross_bound hmn hFamily.
- move=>v hBound; case:v hBound=>[b| |] hBound; [|exact:leey|].
  + exact:gross_borel_compact_projection_least_bound hmn hA hBound.
  + have hZero:=hBound 0 (@compact_projected_family_empty_value R n m A).
    by rewrite leNgt ltNyr in hZero.
Qed.
