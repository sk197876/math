(** Federer (1969), 3.3.21, p. 309: each actual original square piece is a similarity of the common tail square. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter MetricDiameterReal
  EqualCostIntervalTreeUP SpecialIntervalFamilyUP ScheduledCantorIntervalPieceSimilarity
  PowerCantorPairUP PowerCantorPair PlanarAffineProductImage
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanCantorProduct EuclideanIntervalRectangles RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scheduled_original_square_piece_similarity]: every
    ACTUAL original E intersect T is a positive plane similarity of
    a common original unit-root tail square, retaining the arbitrary
    shifted schedule, 3.3.21, p. 309. Both scalar maps and the
    tail pair remain local existential witnesses used through laws. *)
Theorem scheduled_original_square_piece_similarity (R:realType) (c m r:R)
    (J S T:compact_real_intervals R) n H (A:set (real_line_metric R)) j:
  0<c ->0<m ->m<1 ->0<r ->(forall k,(2<=n k)%N) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J n H ->
  is_special_interval_tree_limit H A ->S \in H j ->T \in H j ->
  fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))=r ->
  fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val T))=r ->
  exists a b B g,is_power_cantor_pair c m (fun k=>n (j+k)%N) B g /\
    euclidean_cantor_product A A `&` euclidean_interval_rectangle S T=
    (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>euclidean_real_plane_pair a b+r*:p) @`
      euclidean_cantor_product B B.
Proof.
move=>hc hm hm1 hr hn hTree hA hS hT hWidthS hWidthT.
have [a [a1 [ha hSV]]]:=set_valP S.
have [b [b1 [hb hTV]]]:=set_valP T.
have hA1:a1=a+r.
  rewrite hSV (extended_metric_diameter_segment ha) in hWidthS.
  change (a1-a=r) in hWidthS;lra.
have hB1:b1=b+r.
  rewrite hTV (extended_metric_diameter_segment hb) in hWidthT.
  change (b1-b=r) in hWidthT;lra.
rewrite hA1 in hSV;rewrite hB1 in hTV.
have [B [g hPair]]:=@power_cantor_pair_exists R c m (fun k=>n (j+k)%N)
  hc hm hm1 (fun k=>hn (j+k)%N).
have [M [hM hImageS]]:=@scheduled_original_interval_piece_similarity R c m a r J S n H A B g j
  hc hm hm1 hr hTree hA hS hSV hPair.
have [N [hN hImageT]]:=@scheduled_original_interval_piece_similarity R c m b r J T n H A B g j
  hc hm hm1 hr hTree hA hT hTV hPair.
exists a,b,B,g;split;first exact:hPair.
rewrite planar_affine_original_product_image hImageS hImageT.
apply/seteqP;split=>x.
- move=>[[hxA hyA] [hxS hyT]];by split;split.
- move=>[[hxA hxS] [hyA hyT]];by split;split.
Qed.
