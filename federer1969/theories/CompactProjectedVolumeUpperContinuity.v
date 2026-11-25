(** Supporting upper continuity of projected volume for Federer (1969),
    2.10.5(2), p. 173, bounded open convex generators. For a compact source
    K, an open near-optimal volume cover of p(K), together with joint
    evaluation continuity and a compact product tube, controls all nearby
    projection images. This proves a supporting semicontinuity fact rather
    than assuming the forward reference to 3.2.36. Source context and the
    absence of a matching. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanProjectionMetric ProjectedVolumeMeasurability EuclideanLebesgueDimensions
  EuclideanCompactOpenVolume CompactProductTube MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_projected_volume_upper_neighbourhood]:
    supporting upper continuity for the projection-
    parameter continuity in Federer 2.10.5(2),
    p. 173. Compact K can be empty; b is
    any finite strict upper bound at the given p. *)
Theorem compact_projected_volume_upper_neighbourhood (R : realType) (n m : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) (b : R) :
  compact K -> projected_volume_function K p<b%:E ->
  exists V : set (orthogonal_projection_metric_space R n m), open V /\ V p /\
    forall q, V q -> projected_volume_function K q<b%:E.
Proof.
move=> hK hb.
pose P := orthogonal_projection_metric_space R n m.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose F (z : P*E) : Y := euclidean_projection_linear z.1 z.2.
have hF : continuous F := @euclidean_projection_evaluation_continuous R n m.
have [W [hW [hKW hvol]]] := @euclidean_compact_open_volume_bound R m
  (euclidean_projection_linear p @` K) b (@euclidean_projected_compact_image R n m p K hK) hb.
have ho : open (F @^-1` W).
  apply: open_comp hW=> z _; exact: hF.
have hinc x : K x -> (F @^-1` W) (p,x).
  move=> hx; apply: hKW; by exists x.
have [V [U [hV [hp [_ [hKU hsub]]]]]] :=
  @compact_product_open_tube P E p K (F @^-1` W) hK ho hinc.
exists V; split=> //; split=> // q hq.
apply: le_lt_trans _ hvol; apply: (measure_mono (euclidean_lebesgue_is_measure R m)).
move=> y [x hx <-]; exact: hsub (q,x) (conj hq (hKU x hx)).
Qed.
