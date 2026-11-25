(** Federer (1969), 3.2.41, printed p. 278, first proof
    sentence: the original compact-set case follows by finite
    disjoint open-box approximation and the actual compact
    sum's full positive-radius tube-volume limit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes VectorSetSum EuclideanVectorSumCompact MetricOpenThickening
  CompactSumTubeRootBound CompactAmbientTubeLimit EuclideanVolumeRootSum
  ExtendedPositivePower RealPower ExtendedRootPowerComparison
  PositiveRadiusLimits PositiveRadiusLowerApproximation MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_brunn_minkowski]: direct compact-set case
    in Federer 3.2.41, p. 278. The compact original K,L and
    their actual sum are retained. All zero-volume compact sets
    are included; the only nonempty-set and positive-dimension
    premises are those of the original Brunn--Minkowski statement.
    The compact limit is supplied by already proved 3.2.39 in
    ambient degree, not by a new assumed regularity theorem. *)
Theorem compact_brunn_minkowski (R:realType) n
    (K L:set (inner_metric_space (@euclidean_inner_productP R n))):
  (0<n)%N ->compact K ->compact L ->K !=set0 ->L !=set0 ->
  euclidean_volume_root_sum_bound K L.
Proof.
move=> hn hK hL hKNe hLNe.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose C:=vector_set_sum K L.
pose p:R:=n%:R.
have hp:0<p by rewrite /p ltr0n.
have hm:=euclidean_lebesgue_is_measure R n.
have hKF:(mu K < +oo)%E:=euclidean_compact_finite hK.
have hLF:(mu L < +oo)%E:=euclidean_compact_finite hL.
have hKFn:mu K \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm K)); exact hKF.
have hLFn:mu L \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm L)); exact hLF.
pose a:R:=fine (mu K).
pose b:R:=fine (mu L).
have hMA:mu K=a%:E by rewrite /a fineK.
have hMB:mu L=b%:E by rewrite /b fineK.
pose q:R:=real_power a p^-1+real_power b p^-1.
have hq:0<=q by rewrite /q; apply:addr_ge0; exact:real_power_nonnegative.
have hTube r:(0<r)%R ->((real_power q p)%:E<=mu (metric_open_thickening C r))%E.
  move=> hr.
  have hRoot:=@compact_sum_tube_root_bound R n K L r hn hK hL hKNe hLNe hr.
  change (is_true (extended_positive_power (mu K) p^-1+
    extended_positive_power (mu L) p^-1<=extended_positive_power (mu (metric_open_thickening C r)) p^-1)%E) in hRoot.
  rewrite hMA hMB /extended_positive_power -EFinD in hRoot.
  apply:(@extended_root_power_lower_comparison R (mu (metric_open_thickening C r)) p q
    (measure_nonnegative hm _) hp hq).1.
  exact hRoot.
have hLower:=@positive_radius_lower_eventual_bound R
  (fun r:R=>mu (metric_open_thickening C r)) (real_power q p)%:E 1 (ltr01)
  (fun r hr=>hTube r (andP hr).1).
have hC:compact C:=euclidean_vector_sum_compact hK hL.
have hLimit:positive_radius_lower_limit (fun r:R=>mu (metric_open_thickening C r))=mu C:=
  (@compact_ambient_tube_volume_limits R n C hC).2.
rewrite hLimit in hLower.
have hFinal:((q%:E<=extended_positive_power (mu C) p^-1))%E:=
  (@extended_root_power_lower_comparison R (mu C) p q
    (measure_nonnegative hm C) hp hq).2 hLower.
change (is_true (extended_positive_power (mu K) p^-1+
  extended_positive_power (mu L) p^-1<=extended_positive_power (mu C) p^-1)%E).
rewrite hMA hMB /extended_positive_power -EFinD.
exact hFinal.
Qed.
