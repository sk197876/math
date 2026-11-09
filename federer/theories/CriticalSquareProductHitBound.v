(** Federer (1969), 3.3.20, p. 308:
    actual scaled product mass is bounded by every original hit measure. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP BinaryCantorSquareLevelsUP BinaryCantorSquarePieceMass
  BinaryCantorSquareCover CriticalSquareHitMeasureUP FiniteCellHitMeasureUP
  FiniteEqualCellHitDomination EuclideanInnerProduct InnerMetric EuclideanRealPlane
  EuclideanCantorProduct EuclideanIntervalRectangles PowerCantorProductMeasure
  MeasureUP MeasureBasic MeasureRestriction FiniteMeasureScaling RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_square_original_product_hit_bound]:
    the ORIGINAL product restriction, scaled by sqrt(2),
    is bounded by every literal psi_j on every
    original test set, supporting 3.3.20, p. 308.
    Actual square masses and a finite cover by
    actual hit cells prove the inequality. Neither
    test-set measurability nor the desired diameter
    bound is assumed. *)
Theorem critical_square_original_product_hit_bound (R:realType) (c:R)
    (J:compact_real_intervals R) H G (A:set (real_line_metric R)) psi:
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->is_binary_cantor_square_levels H G ->
  is_critical_square_hit_measures G psi ->
  let nu:=@power_cantor_product_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
    (@euclidean_real_plane_pair R) 1 (1/2:R) ler01 A A in
  forall j T,((Num.sqrt 2)%:E * nu (euclidean_cantor_product A A `&` T)<=psi j T)%E.
Proof.
move=>hc hJ hTree hA hG hPsi nu j.
pose E:=euclidean_cantor_product A A.
pose mu:=fun T=>((Num.sqrt (2:R))%:E * nu (E `&` T))%E.
have hNu:=@power_cantor_product_is_measure R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
  (@euclidean_real_plane_pair R) 1 (1/2:R) ler01 A A.
have hMu:is_measure mu:=finite_scale_is_measure (measure_restrict_is_measure hNu E) (sqrtr_ge0 _).
have hSupport T:mu T=mu (T `&` E).
  have hSet:E `&` T=E `&` (T `&` E).
    apply/seteqP;split=>x.
    - move=>[he ht];split=>//;by split.
    - move=>[he [ht _]];by split.
  by rewrite /mu hSet.
have hCover:=@binary_cantor_original_square_level_cover R H G A hA hG j.
have hCell P:P \in G j ->
    (mu (euclidean_interval_rectangle P.1 P.2)<=(Num.sqrt (2:R)/(4:R)^+j)%:E)%E.
  move=>hP.
  have hSub:E `&` euclidean_interval_rectangle P.1 P.2 `<=` euclidean_interval_rectangle P.1 P.2 by move=>x [].
  have hBound:=lee_wpmul2l (lee_tofin (sqrtr_ge0 (2:R))) (measure_mono hNu hSub).
  have hMember:=hP;rewrite hG in_fsetM in hMember;move:hMember=>/andP[hFirst hSecond].
  have hm:0<(1/2:R) by lra.
  have hm1:(1/2:R)<1 by lra.
  have hMass:=@binary_cantor_original_square_piece_mass R c (1/2:R) J H A
    hc hm hm1 hJ hTree hA j P.1 P.2 hFirst hSecond.
  by rewrite hMass -EFinM in hBound.
exact:(@finite_equal_cell_hit_domination R _ _ (G j)
  (fun P=>euclidean_interval_rectangle P.1 P.2) (Num.sqrt (2:R)/(4:R)^+j)
  mu (psi j) E hMu (hPsi j) hSupport hCover hCell).
Qed.
