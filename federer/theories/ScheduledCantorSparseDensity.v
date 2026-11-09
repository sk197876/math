(** Federer (1969), 3.3.21, p. 309: the actual original real-degree density bound at every sparse radius. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP PowerCantorWidthLawsUP PowerCantorWidthExistence PowerCantorWidthBounds
  PowerCantorUniformGapScalar ScheduledCantorBallPiece ScheduledCantorSquarePieceMass
  SparseCantorDensityScalar RealMetricDensities RealHausdorffMeasure RealHausdorffNormalisation
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanCantorProduct MetricClosedBalls
  MeasureUP MeasureBasic MeasureRestriction RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scheduled_original_sparse_ball_density_bound]: at
    actual r_j=kappa*w_j/(3*n_j), the original restricted real-degree
    ball density is at most K(m)*n_j^(2m-2), at EVERY original
    centre. This supplies 3.3.21, p. 309. Actual original ball
    containment in a single level piece, actual real Hausdorff piece
    mass and the exact positive scalar cancellation prove the bound.
    Neither a pointwise density estimate nor a growth rate is assumed. *)
Theorem scheduled_original_sparse_ball_density_bound (R:realType) (c m:R)
    (hp:0<= 2 * m) (J:compact_real_intervals R) n H w (A:set (real_line_metric R)) j
    (a:inner_metric_space (@euclidean_inner_productP R 2)):
  0<c ->0<m ->m<1 ->(forall k,(2<=n k)%N) ->
  val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J n H ->
  is_special_interval_tree_limit H A ->is_power_cantor_widths c m n w ->
  let k:= 1-2 * real_power 2 (-m^-1) in
  let r:=k * w j/(3 * (n j)%:R) in
  let K:=real_power 2 m * real_power (3/(2 * k)) (2 * m) in
  (0<r /\r<=k/(3 * (n j)%:R)) /\
  (real_metric_ball_density hp
    (measure_restrict (@real_hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2))
      (2 * m) hp) (euclidean_cantor_product A A)) a r<=
      (K * real_power (n j)%:R (2 * m-2))%R%:E)%E.
Proof.
move=>hc hm hm1 hn hJ hTree hA hWidth k r K.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose E:=euclidean_cantor_product A A.
pose mu:=@real_hausdorff_measure R X (2 * m) hp.
have hMu:is_measure mu:=real_hausdorff_measure_is_measure X hp.
have hk:0<k:=(andP (power_cantor_uniform_gap_positive hm hm1)).1.
have hw:=power_cantor_width_positive hWidth j.
have hwChild:=power_cantor_width_positive hWidth j.+1.
have hN:0<((n j)%:R:R) by rewrite ltr0n;exact:leq_trans (leqnSn 1) (hn j).
have hThree:0<(3:R) by rewrite ltr0n.
have hDen:0<3 * (n j)%:R:=mulr_gt0 hThree hN.
have hr:0<r by rewrite /r divr_gt0 // mulr_gt0.
have hWBound: w j<= 1:=(power_cantor_original_width_order hn hWidth).2 j.
have hRadiusBound:r<=k/(3 * (n j)%:R).
  rewrite /r ler_pdivrMr //.
  have hCancel:k/(3 * (n j)%:R) * (3 * (n j)%:R)=k by rewrite divfK ?gt_eqF.
  rewrite hCancel;by rewrite -[X in _<=X]mulr1 ler_pM2l.
split;first by split.
have hDenPositive:=@real_metric_density_denominator_positive R (2 * m) r hp hr.
pose b:=real_hausdorff_normalisation hp.
pose d:=b * real_power (2 * r) (2 * m).
have hd:0<d:=hDenPositive.
have hMass:(mu (E `&` metric_closed_ball a r)<=
    (b * real_power 2 m * real_power (w j.+1) (2 * m))%R%:E)%E.
  case:(@scheduled_original_ball_in_one_piece R c m J n H w A j a
    hc hm hm1 hn hJ hTree hA hWidth)=>[hEmpty|[S [T [hS [hT hContain]]]]].
  - rewrite hEmpty (measure_empty hMu) lee_fin.
    apply:mulr_ge0;last exact:real_power_nonnegative.
    apply:mulr_ge0;[exact:ltW (real_hausdorff_normalisation_positive hp)|exact:real_power_nonnegative].
  - have hWidths:=@power_cantor_original_widths_identify R c m J n H w hc hm hm1 hJ hTree hWidth.
    apply:le_trans (measure_mono hMu hContain) _.
    exact:(@scheduled_original_square_piece_mass_bound R c m (w j.+1) hp J S T n H A j.+1
      hc hm hm1 hwChild hn hTree hA hS hT (hWidths _ _ hS) (hWidths _ _ hT)).
have hReciprocal:(0<=d%:E^-1)%E by rewrite inve_ge0 lee_fin;exact:ltW hd.
have hQuotient:=lee_wpmul2r hReciprocal hMass.
rewrite inver (gt_eqF hd) -EFinM in hQuotient.
rewrite /real_metric_ball_density /measure_restrict -/d inver (gt_eqF hd).
rewrite (@power_cantor_original_width_step R c m n w hc hm hn hWidth j) /d /r
  (@sparse_cantor_density_scalar_identity R m b k (w j) (n j)%:R hm
    (real_hausdorff_normalisation_positive hp) hk hw hN) in hQuotient.
exact:hQuotient.
Qed.
