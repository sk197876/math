(** Federer (1969), 3.3.20, p. 308: first-split descent for the actual original test set. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP BinaryCantorSquareLevelsUP EuclideanInnerProduct InnerMetric
  EuclideanRealPlane EuclideanIntervalRectangles BinaryCantorSquareCoordinates
  BinaryCantorSingleHitSimilarity CriticalSingleHitMeasureSimilarity CriticalCantorRatio
  CriticalFirstLevelAttainment PlanarPositiveSimilarityMetric FiniteFamilyNoTwo
  FiniteCellHitMeasureUP FiniteCellHitIndicesLaws CriticalSquareHitMeasureUP
  MetricDiameter RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_single_hit_descent]: supporting
    initial similarity reduction in 3.3.20, p. 308. Failure of
    finite-stage attainment forces the next original hit family to be
    a singleton whenever the current one is. The original global test
    set is pulled back under an actual positive similarity; no
    measurability, chosen first split or self-similarity is assumed. *)
Theorem critical_original_single_hit_descent (R:realType) (c d:R)
    (J:compact_real_intervals R) H G psi (A:set (real_line_metric R))
    (V:set (inner_metric_space (@euclidean_inner_productP R 2))) j P:
  0<c ->0<=d ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->is_binary_cantor_square_levels H G ->
  is_critical_square_hit_measures G psi ->(extended_metric_diameter V<=d%:E)%E ->
  ~ (exists k,(psi k V<=d%:E)%E) ->
  finite_cell_hit_indices (G j) (fun S=>euclidean_interval_rectangle S.1 S.2) V=[fset P] ->
  exists Q,finite_cell_hit_indices (G j.+1) (fun S=>euclidean_interval_rectangle S.1 S.2) V=[fset Q].
Proof.
move=>hc hd hJ hTree hA hG hPsi hDiameter hNo hSingle.
have hSinglePair:finite_cell_hit_indices (G j) (fun S=>euclidean_interval_rectangle S.1 S.2) V=[fset (P.1,P.2)].
  by rewrite -surjective_pairing.
have hm:0<(1/2:R) by lra.
have hm1:(1/2:R)<1 by lra.
have hPHit:P \in finite_cell_hit_indices (G j) (fun S=>euclidean_interval_rectangle S.1 S.2) V
  by rewrite hSingle in_fset1 eqxx.
have [hP _]:=proj1 (finite_cell_hit_indices_membership _ _ _ _) hPHit.
have hPM:=hP;rewrite hG in_fsetM in hPM;move:hPM=>/andP[hS hT].
have [a [b [hSV hTV]]]:=@binary_cantor_original_square_coordinates R c (1/2:R) J P.1 P.2 H j
  hc hm hJ hTree hS hT.
rewrite critical_cantor_binary_ratio exprVn in hSV hTV.
pose r:=((4:R)^+j)^-1.
have hr:0<r by rewrite /r invr_gt0 exprn_gt0 // ltr0n.
pose F:=fun p:inner_metric_space (@euclidean_inner_productP R 2)=>euclidean_real_plane_pair a b+r*:p.
pose U:=F @^-1` V.
have hDiameterU:(extended_metric_diameter U<=(d/r)%:E)%E.
  exact:(@euclidean_positive_similarity_preimage_diameter R 2
    (euclidean_real_plane_pair a b) r d V hr hd hDiameter).
have hScale:=@critical_original_single_hit_measure_similarity R c a b r J P.1 P.2 H G psi A j V
  hc hr hJ hTree hA hG hPsi hS hT hSV hTV hSinglePair.
have hNoU:~(exists k,(psi k U<=(d/r)%:E)%E).
  move=>[k hk];apply:hNo;exists (j+k)%N;rewrite (hScale k).
  have h:=lee_wpmul2l (lee_tofin (ltW hr)) hk.
  have hCancel:r * (d/r)=d by field;by rewrite gt_eqF.
  by rewrite -EFinM hCancel in h.
have hNoTwo:~(exists Q S,Q \in finite_cell_hit_indices (G 1%N)
      (fun W=>euclidean_interval_rectangle W.1 W.2) U /\
    S \in finite_cell_hit_indices (G 1%N)
      (fun W=>euclidean_interval_rectangle W.1 W.2) U /\Q!=S).
  move=>hTwo;apply:hNoU.
  exact:(@critical_original_first_level_attainment R c (d/r) J H G psi U
    hc hJ hTree hG hPsi hDiameterU hTwo).
have hNonempty:finite_cell_hit_indices (G 1%N)
    (fun W=>euclidean_interval_rectangle W.1 W.2) U!=fset0.
  apply/negP=>/eqP hEmpty;apply:hNoU;exists 1%N.
  rewrite hPsi hEmpty cardfs0 mul0r lee_fin;exact:divr_ge0 hd (ltW hr).
have [Q hQ]:=finite_family_no_two_singleton hNonempty hNoTwo.
have hCount:=@binary_cantor_single_hit_similarity_counts R c (1/2:R) a b r J P.1 P.2 H G A j V
  hc hm hm1 hr hJ hTree hA hG hS hT hSV hTV hSinglePair 1%N.
rewrite addn1 in hCount.
apply/cardfs1P;apply/eqP;by rewrite hCount hQ cardfs1.
Qed.
