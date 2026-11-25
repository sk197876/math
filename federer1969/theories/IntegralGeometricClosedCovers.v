(** Federer (1969), 2.10.5(2), p. 173: the independently selected open and
    closed convex constructions give the same Q_t at every exponent,
    including infinity. Finite exponents use the already proved
    dominated-convergence argument. At infinity, compact closed generators
    have actual essential supremum equal to the projection supremum by the
    proved convex projection lower continuity. Reuse the uniform
    projected-volume open enlargement and compare finite-cutoff measures.
    Source context and the geometric proof, without assumed Steiner formula
    or joint Hausdorff continuity: CompactConvexInfinityGauge.v and
    CompactConvexProjectedVolumeLower.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric IntegralGeometricGauge
  IntegralGeometricMeasureUP IntegralGeometricMeasure IntegralGeometricClosure
  IntegralGeometricFiniteClosedCovers IntegralGeometricInfinity CompactConvexInfinityGauge
  ProjectionMeasureUP ProjectedVolumeGauge ProjectedVolumeOpenEnlargement
  BorelClosedProjection TopologicalBorel EuclideanClosedDiameterCompact ExtendedRealOrderTopology
  MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleEnvelopeLaws
  MetricScaleCutoffCost MetricScaleWeightedBound MetricScaleMeasureBound
  CaratheodoryLimitUP CaratheodoryBorelRegular MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [infinity_convex_integral_geometric_open_closed_agreement]:
    direct infinity endpoint of the open/closed
    convex construction equality in Federer
    2.10.5(2), p. 173. Both measures are
    independently specified; arbitrary targets
    and infinite resulting values are allowed. *)
Theorem infinity_convex_integral_geometric_open_closed_agreement (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @convex_integral_geometric_measure R n m hmn +oo A=
    @closed_convex_integral_geometric_measure R n m hmn +oo A.
Proof.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose c (S : set E) := @integral_geometric_gauge R n m hmn +oo S.
pose mu := @convex_integral_geometric_measure R n m hmn +oo.
pose nu := @closed_convex_integral_geometric_measure R n m hmn +oo.
have hm := @convex_integral_geometric_measure_specification R n m hmn +oo.
have hn := @closed_convex_integral_geometric_measure_specification R n m hmn +oo.
have hlo := @closed_convex_integral_geometric_le_open R n m hmn +oo A (leey 1).
apply/eqP; rewrite eq_le hlo andbT.
apply: (caratheodory_limit_least hm)=> tau xi htau hxi.
have [ell hell] := reciprocal_metric_cutoffs_cofinal htau.
pose t : R := (((ell.+1)%:R)^-1)%R.
have ht : (0<t)%R by rewrite /t invr_gt0 ltr0n.
have hd : (0<=t/2)%R by rewrite divr_ge0 //; exact: ltW ht.
have hdt : (t/2<t)%R by rewrite ltr_pdivrMr //; lra.
pose phi := metric_scale_envelope (fun j : closed_convex_euclidean_sets R n => val j)
  (fun j => c (val j)) ((t/2)%R%:E).
have hphi := @metric_scale_envelope_specification R E
  (closed_convex_euclidean_sets R n) (fun j => val j) (fun j => c (val j)) ((t/2)%R%:E).
have hnon (j : open_convex_euclidean_sets R n) : 0<=c (val j).
  apply: (@integral_geometric_gauge_nonnegative R n m hmn +oo (leey 1) (val j)).
  exact: metric_borel_suslin (open_borel_set (set_valP j).1).
have hxi_measure : is_measure xi := metric_scale_envelope_is_measure hxi hnon.
have hgen (j : closed_convex_euclidean_sets R n) :
    extended_metric_diameter (val j)<=(t/2)%R%:E -> xi (val j)<=c (val j).
  move=> hj; rewrite leNgt; apply/negP=> hbad.
  have hK := euclidean_closed_finite_diameter_compact (set_valP j).1 hj.
  have [q [hq hqn]] := @extended_rationals_order_dense R (c (val j)) (xi (val j)) hbad.
  have hq' : projected_volume_gauge m (val j)<(ratr q : R)%:E.
    by rewrite -(@integral_geometric_gauge_infinity_compact_convex R n m hmn (val j)
      hK (set_valP j).2).
  have [U [hU [hc [hJU [hsize hcost]]]]] :=
    @projected_volume_convex_open_enlargement R n m (val j)
      (t/2)%R t (ratr q) hK (set_valP j).2 hd hdt hj hq'.
  rewrite -(@integral_geometric_gauge_infinity_open R n m hmn U hU) in hcost.
  pose k : open_convex_euclidean_sets R n :=
    @exist _ (fun B : set E => B \in [set B : set E |
      open B /\ @InnerConvex.is_inner_convex R (R_n R n) B]) U (mem_set (conj hU hc)).
  have hb := @metric_scale_generator_bound R E (open_convex_euclidean_sets R n)
    (fun j => val j) (fun j => c (val j)) tau xi k hxi (hnon k) (le_trans hsize hell).
  have hmono := @metric_scale_envelope_mono R E (open_convex_euclidean_sets R n)
    (fun j => val j) (fun j => c (val j)) tau xi hxi (val j) U hJU.
  by have := lt_le_trans hqn (le_trans hmono (le_trans hb hcost)); rewrite ltxx.
apply: le_trans (@measure_bounded_by_metric_scale_envelope R E
  (closed_convex_euclidean_sets R n) (fun j => val j) (fun j => c (val j))
  ((t/2)%R%:E) phi xi hphi hxi_measure hgen A) _.
apply: (@caratheodory_limit_upper R E (closed_convex_euclidean_sets R n)
  (fun j => val j) (fun j => c (val j)) nu hn A ((t/2)%R%:E) phi _ hphi).
by rewrite lte_fin divr_gt0 // ltr0n.
Qed.

(** Source for [convex_integral_geometric_open_closed_agreement]:
    direct full open/closed convex construction
    equality of Federer 2.10.5(2), p. 173,
    for every exponent in [1,infinity]. *)
Theorem convex_integral_geometric_open_closed_agreement (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  1<=t -> @convex_integral_geometric_measure R n m hmn t A=
    @closed_convex_integral_geometric_measure R n m hmn t A.
Proof.
case: t=> [p| |] ht //.
- exact: finite_convex_integral_geometric_open_closed_agreement ht.
- exact: infinity_convex_integral_geometric_open_closed_agreement.
Qed.

(** Source for [convex_integral_geometric_closed_cover_specification]:
    direct assertion that the selected Q_t also
    satisfies the independently specified closed
    convex construction of Federer 2.10.5(2),
    p. 173, at every admissible exponent. *)
Corollary convex_integral_geometric_closed_cover_specification (R : realType)
    (n m : nat) (hmn : (m<=n)%N) (t : \bar R) :
  1<=t -> is_closed_convex_integral_geometric_measure hmn t
    (@convex_integral_geometric_measure R n m hmn t).
Proof.
move=> ht.
have he : @convex_integral_geometric_measure R n m hmn t=
    @closed_convex_integral_geometric_measure R n m hmn t.
  apply: funext=> A; exact: convex_integral_geometric_open_closed_agreement ht.
rewrite he; exact: closed_convex_integral_geometric_measure_specification.
Qed.
