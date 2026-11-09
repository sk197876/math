(** Federer (1969), 3.3.21, p. 309: actual real-degree mass of every original small square piece. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter
  EqualCostIntervalTreeUP SpecialIntervalFamilyUP ScheduledCantorSquarePieceSimilarity
  PowerCantorPairUP PowerCantorSquareRealMassBounds RealPowerPositiveLipschitz LipschitzUP
  PlanarPositiveSimilarityMetric EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanCantorProduct
  EuclideanIntervalRectangles RealHausdorffMeasure RealHausdorffNormalisation RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scheduled_original_square_piece_mass_bound]: the
    actual Hausdorff 2m mass in any original square of side r is
    at most b*2^m*r^(2m), uniformly over every original schedule,
    supporting 3.3.21, p. 309. The actual tail square has the
    already proved original mass bound; actual positive Euclidean
    similarity and the existing real-degree image comparison give
    the bound. No mass, similarity or measure premise is supplied. *)
Theorem scheduled_original_square_piece_mass_bound (R:realType) (c m r:R)
    (hp:0<= 2 * m) (J S T:compact_real_intervals R) n H (A:set (real_line_metric R)) j:
  0<c ->0<m ->m<1 ->0<r ->(forall k,(2<=n k)%N) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J n H ->
  is_special_interval_tree_limit H A ->S \in H j ->T \in H j ->
  fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))=r ->
  fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))=r ->
  (@real_hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2))
    (2 * m) hp (euclidean_cantor_product A A `&` euclidean_interval_rectangle S T)<=
      (real_hausdorff_normalisation hp * real_power 2 m * real_power r (2 * m))%R%:E)%E.
Proof.
move=>hc hm hm1 hr hn hTree hA hS hT hWidthS hWidthT.
have [a [b [B [g [hPair hImage]]]]]:=@scheduled_original_square_piece_similarity R c m r J S T n H A j
  hc hm hm1 hr hn hTree hA hS hT hWidthS hWidthT.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose F:=fun x:X=>euclidean_real_plane_pair a b+r*:x.
have hLip:is_metric_lipschitz_bound setT F r.
  split;first exact:ltW hr.
  move=>x y _ _;rewrite /F (@euclidean_positive_similarity_distance R 2 _ r x y (ltW hr)).
  exact:lexx.
have hMeasure:=@real_hausdorff_positive_lipschitz R X X F r (2 * m) hp hr hLip (euclidean_cantor_product B B).
have [_ hUpper]:=@power_cantor_square_real_mass_bounds R c m hp (fun k=>n (j+k)%N) B g hc hm hm1 hPair.
have hScaleNonnegative:(0<=(real_power r (2 * m))%:E)%E by rewrite lee_fin;exact:real_power_nonnegative.
have hFinal:=le_trans hMeasure (lee_wpmul2l hScaleNonnegative hUpper).
rewrite -hImage -EFinM in hFinal.
have hComm:(real_power r (2 * m) * (real_hausdorff_normalisation hp * real_power 2 m))%R=
    (real_hausdorff_normalisation hp * real_power 2 m * real_power r (2 * m))%R
  by rewrite mulrC.
by rewrite hComm in hFinal.
Qed.
