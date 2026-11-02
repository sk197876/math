(** Federer (1969), 3.2.36, p. 272:
    a common actual norm bound gives
    a uniform Hausdorff volume error estimate. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded
  HausdorffTubeControl SteinerTubeVolumeIncrement EuclideanNormBoundedTubeVolume
  EuclideanClosedBallVolume EuclideanBallVolume EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  MetricClosedBalls MeasureUP MeasureBasic MetricSetDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_common_norm_volume_bound]:
    supporting the intrinsic-volume continuity
    deduction in Federer 3.2.36, p. 272.
    Two compact convex bodies in a common
    norm ball have actual volume difference
    at most r*alpha(n)*(c+1)^n whenever
    their Hausdorff distance is below r<=1.
    This makes the error constant uniform
    over all actual orthogonal projections.
    Actual unit-tube inclusion and Steiner's
    polynomial prove the bound, retaining all
    natural dimensions and empty interiors. *)
Theorem compact_convex_common_norm_volume_bound (R:realType) n
    (A B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n))) (c r:R):
  is_inner_convex (val A) ->is_inner_convex (val B) ->0<=c ->
  (forall x,val A x ->inner_norm (@euclidean_inner_productP R n) x<=c) ->
  (forall x,val B x ->inner_norm (@euclidean_inner_productP R n) x<=c) ->
  0<r ->r<=1 ->mdist A B<r ->
  `|fine (euclidean_lebesgue_measure n (val A))-fine (euclidean_lebesgue_measure n (val B))|<=
    r*(euclidean_unit_ball_volume R n*(c+1)^+n).
Proof.
move=>hA hB hc hNormA hNormB hr hr1 hABr.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
have hm:=euclidean_lebesgue_is_measure R n.
pose C:R:=euclidean_unit_ball_volume R n*(c+1)^+n.
have hBoundA:=compact_metric_diameter_finite A.
have hBoundB:=compact_metric_diameter_finite B.
have hUnitA:(mu [set x|(compact_set_distance_profile A x<1)%R]<=C%:E)%E.
  have h:=euclidean_norm_bounded_tube_volume (compact_set_distance_profile_specification A) hNormA.
  by rewrite (@euclidean_closed_ball_normalized_volume R n (0%R:X) (c+1) ltac:(lra)) in h.
have hUnitB:(mu [set x|(compact_set_distance_profile B x<1)%R]<=C%:E)%E.
  have h:=euclidean_norm_bounded_tube_volume (compact_set_distance_profile_specification B) hNormB.
  by rewrite (@euclidean_closed_ball_normalized_volume R n (0%R:X) (c+1) ltac:(lra)) in h.
have hAInto:(mu (val A)<=mu (val B)+(r*C)%:E)%E.
  apply:le_trans (measure_mono hm (hausdorff_compact_source_in_tube hABr)) _.
  apply:le_trans (convex_small_tube_volume_increment (set_valP B).2 hB hBoundB
    (compact_set_distance_profile_specification B) hr hr1) _.
  rewrite EFinM; apply:leeD; first exact:lexx.
  apply:lee_wpmul2l; first by rewrite lee_fin; exact:ltW hr.
  exact:hUnitB.
have hBAr:mdist B A<r by rewrite metric_sym.
have hBInto:(mu (val B)<=mu (val A)+(r*C)%:E)%E.
  apply:le_trans (measure_mono hm (hausdorff_compact_source_in_tube hBAr)) _.
  apply:le_trans (convex_small_tube_volume_increment (set_valP A).2 hA hBoundA
    (compact_set_distance_profile_specification A) hr hr1) _.
  rewrite EFinM; apply:leeD; first exact:lexx.
  apply:lee_wpmul2l; first by rewrite lee_fin; exact:ltW hr.
  exact:hUnitA.
have hFinA:mu (val A) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)); exact:euclidean_compact_finite (set_valP A).1.
have hFinB:mu (val B) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)); exact:euclidean_compact_finite (set_valP B).1.
rewrite -(fineK hFinA) -(fineK hFinB) -EFinD lee_fin in hAInto hBInto.
have hNormBound (u v w:R):u<=v+w ->v<=u+w ->`|u-v|<=w.
  move=>h1 h2; rewrite ler_norml; apply/andP; split; lra.
exact:hNormBound hAInto hBInto.
Qed.
