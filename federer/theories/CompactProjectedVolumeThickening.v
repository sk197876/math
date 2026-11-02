(** Supporting outer approximation for Federer (1969), 2.10.5(2), p. 173,
    comparison with closed convex generators. A fixed projection of an open
    thickening of a compact source has volume approaching the volume of the
    compact projected image. Compactness and open outer approximation also
    control the source thickening uniformly in a neighbourhood of the
    projection. Convexity is unnecessary for these supporting statements.
    They do not assert uniform convergence over all projections or the full
    joint convex continuity theorem cited in 3.2.36, p. 272. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanProjectionMetric ProjectedVolumeMeasurability ProjectedVolumeBounds
  EuclideanLebesgueDimensions EuclideanCompactOpenVolume CompactProductTube
  MetricOpenThickening ExtendedRealOrderTopology ExtendedRealOrderLimit
  ExtendedRealReciprocalBounds MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_projected_thickening_upper_neighbourhood]:
    supporting simultaneous parameter and source
    neighbourhood bound for Federer 2.10.5(2),
    p. 173. Use a near-optimal open volume
    cover of p(K) and a compact product tube. *)
Theorem compact_projected_thickening_upper_neighbourhood (R : realType) (n m : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : euclidean_projection_space R n m) (b : R) :
  compact K -> projected_volume_function K p<b%:E ->
  exists (V : set (euclidean_projection_space R n m)) (r : R),
    open V /\ V p /\ (0<r)%R /\ forall q,
      V q -> projected_volume_function (metric_open_thickening K r) q<b%:E.
Proof.
move=> hK hb.
pose P := euclidean_projection_space R n m.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose F (z : P*E) : Y := euclidean_projection_linear z.1 z.2.
have hF : continuous F := @euclidean_projection_evaluation_continuous R n m.
have [W [hW [hKW hvol]]] := @euclidean_compact_open_volume_bound R m
  (euclidean_projection_linear p @` K) b (@euclidean_projected_compact_image R n m p K hK) hb.
have hinc x : K x -> W (F (p,x)) by move=> hx; apply: hKW; by exists x.
have [V [r [hV [hp [hr hsub]]]]] :=
  @compact_parameter_image_neighbourhood R P E Y F p K W hF hK hW hinc.
exists V,r; split=> //; split=> //; split=> // q hq.
apply: le_lt_trans _ hvol; apply: (measure_mono (euclidean_lebesgue_is_measure R m)).
move=> y [x hx <-]; exact: hsub q x hq hx.
Qed.

(** Source for [compact_projected_thickening_volume_limit]:
    supporting pointwise projection-volume limit
    in the closed-convex comparison of Federer
    2.10.5(2), p. 173. Reciprocal source
    thickenings decrease in size to the compact
    set; outer volume approximation proves the
    limit without exchanging a supremum and a limit. *)
Theorem compact_projected_thickening_volume_limit (R : realType) (n m : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : euclidean_projection_space R n m) :
  compact K -> extended_order_limit
    (fun k => projected_volume_function (metric_open_thickening K (((k.+1)%:R:R)^-1)%R) p)
    (projected_volume_function K p).
Proof.
move=> hK; split.
- move=> a ha; exists 0%N=> k _; apply: lt_le_trans ha _.
  apply: projected_volume_function_mono; apply: metric_open_thickening_includes.
  by rewrite invr_gt0 ltr0n.
- move=> b hb.
  have [q [hq hqb]] := @extended_rationals_order_dense R (projected_volume_function K p) b hb.
  have [V [r [_ [hp [hr hbound]]]]] :=
    @compact_projected_thickening_upper_neighbourhood R n m K p (ratr q) hK hq.
  have [N hN] := positive_reciprocal_nat_small hr.
  exists N=> k hNk; apply: lt_trans _ hqb.
  apply: le_lt_trans _ (hbound p hp).
  apply: projected_volume_function_mono=> x [a ha hax].
  exists a=> //.
  change (is_true (mdist a x<r)%R).
  have hrecip : (((k.+1)%:R:R)^-1<=((N.+1)%:R:R)^-1)%R.
    have hkpos : (0<((k.+1)%:R:R))%R by rewrite ltr0n.
    have hNpos : (0<((N.+1)%:R:R))%R by rewrite ltr0n.
    by rewrite (@lef_pV2 R (k.+1)%:R (N.+1)%:R hkpos hNpos) ler_nat.
  exact: lt_trans (lt_le_trans hax hrecip) hN.
Qed.
