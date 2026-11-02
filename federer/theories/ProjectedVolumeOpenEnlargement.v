(** Supporting open enlargement for Federer (1969), 2.10.4(2), p. 172. For a
    compact generator, each projected image has an open neighbourhood of
    arbitrarily close Lebesgue volume. Joint evaluation continuity gives a
    parameter neighbourhood and a positive source thickening radius.
    Compactness of O*(n,m) makes that radius uniform over all projections.
    Thus the gauge of an open thickening approaches the compact generator's
    gauge. This expands the printed comparison; it does not assume
    continuity of a supremum. Source context and approximation references:
    ProjectedVolumeGaugeUP.v and EuclideanCompactOpenVolume.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanLebesgueDimensions CoordinateProjection ProjectedVolumeGauge EuclideanProjectionSpace
  EuclideanCompactOpenVolume CompactProductTube CompactFiniteCover FiniteOffTargetBallCover
  MetricOpenThickening InnerConvexNeighbourhoods MetricDiameter MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [projected_volume_compact_thickening_bound]:
    supporting uniform cost control for the open convex
    alternative in Federer 2.10.4(2), p. 172.
    The support lemma needs compactness, but not
    convexity or nonemptiness, of the input generator. *)
Theorem projected_volume_compact_thickening_bound (R : realType) (n m : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (b : R) :
  compact K -> (projected_volume_gauge m K<b%:E)%E ->
  exists r : R, 0<r /\ (projected_volume_gauge m (metric_open_thickening K r)<=b%:E)%E.
Proof.
move=> hK hb.
pose P := euclidean_projection_space R n m.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose F (z : P*X) : Y := euclidean_projection_linear z.1 z.2.
have hF : continuous F := @euclidean_projection_evaluation_continuous R n m.
pose J := [the choiceType of (set P*(R*set Y))%type].
pose D : set J := [set z | open z.1 /\ 0<z.2.1 /\
  (euclidean_lebesgue_measure m z.2.2<=b%:E)%E /\
  forall q x, z.1 q -> metric_open_thickening K z.2.1 x -> z.2.2 (F (q,x))].
have hcover : @setT P `<=` \bigcup_(z in D) z.1.
  move=> p _.
  have himage := @euclidean_projected_compact_image R n m p K hK.
  have hcost := @projected_volume_gauge_projection_bound R n m K
    (euclidean_projection_linear p) (euclidean_projection_linear_member p).
  have [U [hU [hKU hvolume]]] := @euclidean_compact_open_volume_bound R m
    (euclidean_projection_linear p @` K) b himage (le_lt_trans hcost hb).
  have hinside x : K x -> U (F (p,x)) by move=> hx; apply: hKU; by exists x.
  have [V [r [hV [hp [hr hsub]]]]] := @compact_parameter_image_neighbourhood R P X Y
    F p K U hF hK hU hinside.
  exists (V,(r,U)); last exact hp.
  split=> //; split=> //; split; first exact: ltW hvolume.
  exact hsub.
have [G hG hcov] := @compact_open_finite_cover P J D (fun z => z.1) setT
  (@euclidean_projection_space_compact R n m) (fun z hz => hz.1) hcover.
have hpos z : [set` G] z -> 0<z.2.1.
  move=> hz; have hd : D z := set_mem (hG z hz); exact hd.2.1.
have [r [hr hrlow]] := @finite_positive_values_lower_bound R J [set` G]
  (fun z => z.2.1) (finite_fset G) hpos.
exists r; split=> //; apply: projected_volume_gauge_least_bound=> p hp.
have [q hq] := euclidean_projection_linear_complete hp.
have [z hz hqV] := hcov q Logic.I.
have hd : D z := set_mem (hG z hz).
apply: le_trans _ hd.2.2.1.
apply: (measure_mono (euclidean_lebesgue_is_measure R m))=> y [x hx <-].
have htx : metric_open_thickening K z.2.1 x.
  have [a ha hax] := hx; exists a=> //; exact: lt_le_trans hax (hrlow z hz).
have hh : z.2.2 (euclidean_projection_linear q x) := hd.2.2.2 q x hqV htx.
by rewrite (hq x) in hh.
Qed.

(** Source for [projected_volume_convex_open_enlargement]:
    supporting open convex replacement with controlled
    diameter and cost in Federer 2.10.4(2), p. 172.
    Shrinking the uniform radius preserves the cost
    bound and leaves room below the target cutoff. *)
Theorem projected_volume_convex_open_enlargement (R : realType) (n m : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (d t b : R) :
  compact K -> @is_inner_convex R (R_n R n) K -> 0<=d -> d<t ->
  (extended_metric_diameter K<=d%:E)%E -> (projected_volume_gauge m K<b%:E)%E ->
  exists U : set (inner_metric_space (@euclidean_inner_productP R n)),
    open U /\ @is_inner_convex R (R_n R n) U /\ K `<=` U /\
    (extended_metric_diameter U<=t%:E)%E /\ (projected_volume_gauge m U<=b%:E)%E.
Proof.
move=> hK hc hd hdt hdiam hcost.
have [s [hs hsmall]] := projected_volume_compact_thickening_bound hK hcost.
pose r := Order.min s ((t-d)/4).
have hr : 0<r by rewrite /r lt_min hs divr_gt0 // subr_gt0.
have hrs : r<=s by rewrite /r ge_min lexx.
have hrt : r<=(t-d)/4 by rewrite /r ge_min lexx orbT.
pose U := metric_open_thickening K r.
have hUcost : (projected_volume_gauge m U<=b%:E)%E.
  apply: le_trans _ hsmall; apply: projected_volume_gauge_mono=> x [a ha hax].
  exists a=> //; exact: lt_le_trans hax hrs.
exists U; split; first exact: metric_open_thickening_open.
split; first exact (@inner_convex_open_thickening R (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) K r hc).
split; first exact: metric_open_thickening_includes hr.
split=> //.
apply: le_trans (metric_open_thickening_diameter_bound hd (ltW hr) hdiam) _.
rewrite lee_fin; have hh : d+r+r<t by lra.
exact: ltW hh.
Qed.
