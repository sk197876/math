(** Federer (1969), 3.3.20, p. 307: the exact original compact-piece cover bound for Gross measure. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge PowerCantorPairUP PowerCantorPair
  EqualCostIntervalTreeUP SpecialIntervalFamilyUP BinaryCantorSquareLevelsUP BinaryCantorSquareCover
  BinaryCantorSquareCount BinaryCantorLevelWidths CriticalCantorRatio CriticalOriginalPieceGaugeBound
  EuclideanInnerProduct InnerMetric EuclideanCantorProduct EuclideanIntervalRectangles
  CantorSquareCompactMass BinaryCantorSquareLevelTopology ProjectedVolumeGauge ProjectionMeasure
  BorelCoverCostUP BorelCaratheodoryMeasure TopologicalBorel CaratheodoryLimitUP
  MetricScaleEnvelopeUP MetricScaleIndexedCover MetricDiameter MetricDiameterUP CaratheodoryBorelRegular
  RecurrentContraction NonnegativeSum NonnegativeSumSupport FiniteConstantNonnegativeSum RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [critical_original_cantor_square_gross_upper]: the
    Gross upper bound 3/sqrt(5) in 3.3.20, p. 307. Every positive
    cutoff admits the actual finite cover {E intersect T:T in G_j}
    by compact Borel pieces. Exact original similarity gives cost at
    most 4^(-j)3/sqrt(5) per original index; the proved actual cardinal
    4^j cancels it. All signs, actual projection supremum, arbitrary
    positive cutoffs and original Caratheodory laws are retained. *)
Theorem critical_original_cantor_square_gross_upper (R:realType) (c:R)
    (A:set (real_line_metric R)) (f:R->R):
  (0<c)%R ->is_power_cantor_pair c (1/2:R) (fun _:nat=>2%N) A f ->
  @gross_measure R 2 1 (euclidean_cantor_product A A)<=(3/Num.sqrt (5:R))%:E.
Proof.
move=>hc hPair.
have hm:(0<(1/2:R))%R by lra.
have hm1:((1/2:R)<1)%R by lra.
have hCompactA:=(@power_cantor_pair_properties R c (1/2:R) (fun _:nat=>2%N) A f hc hm hm1 hPair).1.
have [J [H [hJ [hTree [hA _]]]]]:=hPair.
have [G hG]:=binary_cantor_square_levels_exist H.
pose X:=[the metricType R of inner_metric_space (@euclidean_inner_productP R 2)].
pose E:=euclidean_cantor_product A A.
pose K:=[the choiceType of (compact_real_intervals R*compact_real_intervals R)%type].
have hCompactE:compact E:=euclidean_cantor_product_compact hCompactA hCompactA.
have hBorel (P:K):borel_set (E `&` euclidean_interval_rectangle P.1 P.2).
  have hClosed:=compact_closed (@metric_hausdorff R X) (@original_interval_rectangle_compact R P.1 P.2).
  have hCompact:=compact_closedI hCompactE hClosed.
  exact:closed_borel_set (compact_closed (@metric_hausdorff R X) hCompact).
pose q (P:K):@borel_metric_sets R X:=Sub (E `&` euclidean_interval_rectangle P.1 P.2) (mem_set (hBorel P)).
apply:(caratheodory_limit_least (@gross_measure_specification R 2 1))=>delta nu hd hn.
have [i hCut]:=reciprocal_metric_cutoffs_cofinal hd.
pose a:=((i.+1%:R:R)^-1)%R.
have ha:(0<a)%R by rewrite /a invr_gt0 ltr0n.
have hQuarter:(0<(1/4:R)<1)%R by apply/andP;split;lra.
have [N hMesh]:=geometric_contraction_small hQuarter (sqrtr_ge0 (2:R)) ha.
rewrite mul1r exprVn mulrC in hMesh.
pose r:=(((4:R)^+N)^-1)%R.
have hr:(0<r)%R by rewrite /r invr_gt0 exprn_gt0 // ltr0n.
have hSmall:(Num.sqrt (2:R) * r<=a)%R:=ltW hMesh.
have hWidth S:S \in H N ->fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))=r.
  move=>hS.
  have h:=@binary_cantor_level_width R c (1/2:R) J H hc hm hJ hTree N S hS.
  by rewrite critical_cantor_binary_ratio exprVn in h.
have hNonnegative (P:K):0<=projected_volume_gauge 1 (val (q P)).
  exact:(@projected_volume_gauge_nonnegative R 2 1 _ (leqnSn 1)).
have hSize (P:K):[set` G N] P ->extended_metric_diameter (val (q P))<=delta.
  move=>hP;change (is_true (P \in G N)) in hP.
  move:hP;rewrite hG in_fsetM=>/andP[hS hT].
  have hRect:=@euclidean_interval_rectangle_diameter_bound R P.1 P.2 r (ltW hr)
    (ltac:(by rewrite hWidth)) (ltac:(by rewrite hWidth)).
  have hSubset:val (q P) `<=` euclidean_interval_rectangle P.1 P.2 by move=>x [].
  apply:le_trans (extended_metric_diameter_mono hSubset) (le_trans hRect _).
  apply:le_trans _ hCut;by rewrite lee_fin.
have hCover:E `<=` \bigcup_(P in [set` G N]) val (q P).
  move=>x hx.
  have [P [hP hxP]]:=@binary_cantor_original_square_level_cover R H G A hA hG N x hx.
  exists P=>//;by split.
pose D:=(3/Num.sqrt (5:R))%R.
have hD:(0<D)%R by rewrite /D divr_gt0 // ?sqrtr_gt0 ltr0n.
have hw:(0<=r * D)%R:=mulr_ge0 (ltW hr) (ltW hD).
have hLocal (P:K):[set` G N] P ->projected_volume_gauge 1 (val (q P))<=(r * D)%R%:E.
  move=>hP;change (is_true (P \in G N)) in hP.
  move:hP;rewrite hG in_fsetM=>/andP[hS hT].
  exact:(@critical_original_piece_projected_volume_gauge_bound R c J P.1 P.2 H A f N
    hc hJ hTree hA hS hT hPair).
have hBound:=@metric_scale_envelope_indexed_cover R X (@borel_metric_sets R X) K
  (fun S=>val S) (fun S=>projected_volume_gauge 1 (val S)) delta nu hn E [set` G N] q
  (finite_set_countable (finite_fset (G N))) (fun P _=>hNonnegative P) hSize hCover.
apply:le_trans hBound _.
apply:le_trans (nonnegative_sum_mono hLocal) _.
rewrite (@finite_constant_nonnegative_sum R K (G N) (r * D)%R hw).
have hCard:=@binary_cantor_original_square_count R c (1/2:R) J H G hc hm hm1 hJ hTree hG N.
rewrite hCard natrX /r.
have hPositive:(0<(4:R)^+N)%R by rewrite exprn_gt0 // ltr0n.
have hCancel:((4:R)^+N * (((4:R)^+N)^-1 * D)=D)%R by rewrite mulrA mulfV ?gt_eqF // mul1r.
by rewrite hCancel.
Qed.
