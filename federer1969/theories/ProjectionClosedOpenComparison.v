(** Federer (1969), 2.10.4(2), p. 172: closed convex generators give the
    same Caratheodory measure as open convex generators. For one direction,
    close an open convex generator with unchanged gauge and diameter. For
    the other, finite cutoffs make closed generators compact; the uniform
    projection enlargement gives arbitrarily close-cost open convex
    replacements below a larger cutoff. Source context and expanded
    arguments: ProjectedVolumeClosure.v and
    ProjectedVolumeOpenEnlargement.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  ProjectedVolumeGauge ProjectionMeasureUP ProjectionMeasure ProjectedVolumeClosure
  ProjectedVolumeOpenEnlargement InnerConvexNeighbourhoods EuclideanClosedDiameterCompact
  ExtendedRealOrderTopology MetricDiameter MetricDiameterClosure
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleEnvelopeLaws MetricScaleCutoffCost
  MetricScaleMeasureBound MetricScaleWeightedBound CaratheodoryLimitUP CaratheodoryMeasure
  CaratheodoryBorelRegular CaratheodoryFamilyReplacement MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_projection_open_closed_cover_agreement]:
    direct open/closed convex covering equality in
    Federer 2.10.4(2), p. 172. The two final
    measures are independently specified; targets may
    be arbitrary, unbounded and nonmeasurable. *)
Theorem convex_projection_open_closed_cover_agreement (R : realType) (n m : nat)
    (mu nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :
  (m<=n)%N -> is_caratheodory_projection_measure m mu ->
  is_closed_convex_projection_measure m nu -> forall A, mu A=nu A.
Proof.
move=> hmn hm hn A.
have hlo : nu A<=mu A.
  apply: (@caratheodory_family_replacement R (inner_metric_space (@euclidean_inner_productP R n))
    (open_convex_euclidean_sets R n) (closed_convex_euclidean_sets R n)
    (fun j => val j) (fun j => val j)
    (fun j => projected_volume_gauge m (val j))
    (fun j => projected_volume_gauge m (val j)) mu nu hm hn _ _ A).
  - move=> j; exact: projected_volume_gauge_nonnegative.
  - move=> j.
    pose k : closed_convex_euclidean_sets R n :=
      @exist _ (fun B : set (inner_metric_space (@euclidean_inner_productP R n)) =>
        B \in [set B : set (inner_metric_space (@euclidean_inner_productP R n)) | closed B /\ @InnerConvex.is_inner_convex R (R_n R n) B])
        (closure (val j)) (mem_set (conj (@closed_closure
          (inner_metric_space (@euclidean_inner_productP R n)) (val j))
          (@inner_convex_closure R (R_n R n) (@euclidean_inner_product R n)
            (@euclidean_inner_productP R n) (val j) (set_valP j).2))).
    exists k; split; first exact: (@subset_closure _ (val j)).
    split.
    + change (extended_metric_diameter (closure (val j))<=extended_metric_diameter (val j)).
      by rewrite extended_metric_diameter_closure.
    + change (projected_volume_gauge m (closure (val j))<=projected_volume_gauge m (val j)).
      by rewrite (@projected_volume_gauge_open_convex_closure R n m (val j) hmn
        (set_valP j).1 (set_valP j).2).
apply/eqP; rewrite eq_le hlo andbT.
apply: (caratheodory_limit_least hm)=> tau xi htau hxi.
have [ell hell] := reciprocal_metric_cutoffs_cofinal htau.
pose t : R := (((ell.+1)%:R)^-1)%R.
have ht : (0<t)%R by rewrite /t invr_gt0 ltr0n.
have hd : (0<=t/2)%R by rewrite divr_ge0 //; exact: ltW ht.
have hdt : (t/2<t)%R by rewrite ltr_pdivrMr //; lra.
pose phi := metric_scale_envelope (fun j : closed_convex_euclidean_sets R n => val j)
  (fun j => projected_volume_gauge m (val j)) ((t/2)%R%:E).
have hphi := @metric_scale_envelope_specification R (inner_metric_space (@euclidean_inner_productP R n))
  (closed_convex_euclidean_sets R n) (fun j => val j)
  (fun j => projected_volume_gauge m (val j)) ((t/2)%R%:E).
have hxi_measure : is_measure xi := metric_scale_envelope_is_measure hxi
  (fun j => @projected_volume_gauge_nonnegative R n m (val j) hmn).
have hgen (j : closed_convex_euclidean_sets R n) :
    extended_metric_diameter (val j)<=(t/2)%R%:E -> xi (val j)<=projected_volume_gauge m (val j).
  move=> hj; rewrite leNgt; apply/negP=> hbad.
  have hK := euclidean_closed_finite_diameter_compact (set_valP j).1 hj.
  have [q [hq hqn]] := @extended_rationals_order_dense R (projected_volume_gauge m (val j))
    (xi (val j)) hbad.
  have [U [hU [hc [hJU [hsize hcost]]]]] := @projected_volume_convex_open_enlargement R n m
    (val j) (t/2)%R t (ratr q) hK (set_valP j).2 hd hdt hj hq.
  pose k : open_convex_euclidean_sets R n :=
    @exist _ (fun B : set (inner_metric_space (@euclidean_inner_productP R n)) =>
      B \in [set B : set (inner_metric_space (@euclidean_inner_productP R n)) | open B /\ @InnerConvex.is_inner_convex R (R_n R n) B]) U (mem_set (conj hU hc)).
  have hb := @metric_scale_generator_bound R (inner_metric_space (@euclidean_inner_productP R n))
    (open_convex_euclidean_sets R n) (fun j => val j) (fun j => projected_volume_gauge m (val j))
    tau xi k hxi (@projected_volume_gauge_nonnegative R n m U hmn) (le_trans hsize hell).
  have hmono := @metric_scale_envelope_mono R (inner_metric_space (@euclidean_inner_productP R n))
    (open_convex_euclidean_sets R n) (fun j => val j) (fun j => projected_volume_gauge m (val j))
    tau xi hxi (val j) U hJU.
  by have := lt_le_trans hqn (le_trans hmono (le_trans hb hcost)); rewrite ltxx.
apply: le_trans (@measure_bounded_by_metric_scale_envelope R
  (inner_metric_space (@euclidean_inner_productP R n)) (closed_convex_euclidean_sets R n)
  (fun j => val j) (fun j => projected_volume_gauge m (val j)) ((t/2)%R%:E) phi xi
  hphi hxi_measure hgen A) _.
apply: (@caratheodory_limit_upper R (inner_metric_space (@euclidean_inner_productP R n))
  (closed_convex_euclidean_sets R n) (fun j => val j) (fun j => projected_volume_gauge m (val j))
  nu hn A ((t/2)%R%:E) phi _ hphi).
by rewrite lte_fin divr_gt0 // ltr0n.
Qed.

(** Source for [caratheodory_projection_closed_cover_specification]:
    direct closed convex construction laws for the selected
    Caratheodory measure of Federer 2.10.4(2), p. 172.
    Existence of the competing construction comes from
    the sealed general operator, and equality is proved. *)
Theorem caratheodory_projection_closed_cover_specification (R : realType) (n m : nat) :
  (m<=n)%N -> is_closed_convex_projection_measure m (@caratheodory_projection_measure R n m).
Proof.
move=> hmn.
pose S := fun j : closed_convex_euclidean_sets R n => val j.
pose c := fun j : closed_convex_euclidean_sets R n => projected_volume_gauge m (val j).
pose nu := caratheodory_measure S c.
have hn : is_closed_convex_projection_measure m nu := caratheodory_measure_specification S c.
have he : @caratheodory_projection_measure R n m=nu.
  apply: funext=> A; exact (@convex_projection_open_closed_cover_agreement R n m _ _ hmn
    (@caratheodory_projection_measure_specification R n m) hn A).
by rewrite he.
Qed.
