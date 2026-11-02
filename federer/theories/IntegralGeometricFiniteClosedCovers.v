(** Federer (1969), 2.10.5(2), p. 173, closed convex alternative, for every
    finite exponent. The open and closed constructions are independently
    selected. Closing open generators gives one inequality. For the other, a
    finite diameter cutoff makes a closed generator compact; the proved
    finite- exponent enlargement supplies arbitrarily close-cost open convex
    replacements below a larger cutoff. Pass the generator inequality
    through the actual scale measures. Exponent infinity remains a separate
    obligation. Source context and the dominated-convergence proof route:
    IntegralGeometricFiniteEnlargement.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric IntegralGeometricGauge
  IntegralGeometricMeasureUP IntegralGeometricMeasure IntegralGeometricClosure
  IntegralGeometricFiniteEnlargement ProjectionMeasureUP BorelClosedProjection TopologicalBorel
  EuclideanClosedDiameterCompact ExtendedRealOrderTopology MetricDiameter
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleEnvelopeLaws MetricScaleCutoffCost
  MetricScaleWeightedBound MetricScaleMeasureBound CaratheodoryLimitUP CaratheodoryBorelRegular MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_convex_integral_geometric_open_closed_agreement]:
    direct open/closed convex construction equality
    of Federer 2.10.5(2), p. 173, at finite
    exponent. The target is arbitrary and the
    independent final values may be infinite. *)
Theorem finite_convex_integral_geometric_open_closed_agreement (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (p : R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (1<=p)%R ->
  @convex_integral_geometric_measure R n m hmn p%:E A=
    @closed_convex_integral_geometric_measure R n m hmn p%:E A.
Proof.
move=> hp.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose c (S : set E) := @integral_geometric_gauge R n m hmn p%:E S.
pose mu := @convex_integral_geometric_measure R n m hmn p%:E.
pose nu := @closed_convex_integral_geometric_measure R n m hmn p%:E.
have hm := @convex_integral_geometric_measure_specification R n m hmn p%:E.
have hn := @closed_convex_integral_geometric_measure_specification R n m hmn p%:E.
have hlo := @closed_convex_integral_geometric_le_open R n m hmn p%:E A hp.
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
  apply: (@integral_geometric_gauge_nonnegative R n m hmn p%:E hp (val j)).
  exact: metric_borel_suslin (open_borel_set (set_valP j).1).
have hxi_measure : is_measure xi := metric_scale_envelope_is_measure hxi hnon.
have hgen (j : closed_convex_euclidean_sets R n) :
    extended_metric_diameter (val j)<=(t/2)%R%:E -> xi (val j)<=c (val j).
  move=> hj; rewrite leNgt; apply/negP=> hbad.
  have hK := euclidean_closed_finite_diameter_compact (set_valP j).1 hj.
  have [q [hq hqn]] := @extended_rationals_order_dense R (c (val j)) (xi (val j)) hbad.
  have [U [hU [hc [hJU [hsize hcost]]]]] :=
    @integral_geometric_finite_convex_open_enlargement R n m hmn (val j) p
      (t/2)%R t (ratr q) hK (set_valP j).2 hp hd hdt hj hq.
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

(** Source for [finite_convex_integral_geometric_closed_cover_specification]:
    direct closed convex covering laws for the
    selected Q_t of Federer 2.10.5(2), p. 173,
    for finite t. Equality with the independent
    closed convex construction is proved above. *)
Corollary finite_convex_integral_geometric_closed_cover_specification (R : realType)
    (n m : nat) (hmn : (m<=n)%N) (p : R) :
  (1<=p)%R -> is_closed_convex_integral_geometric_measure hmn p%:E
    (@convex_integral_geometric_measure R n m hmn p%:E).
Proof.
move=> hp.
have he : @convex_integral_geometric_measure R n m hmn p%:E=
    @closed_convex_integral_geometric_measure R n m hmn p%:E.
  apply: funext=> A; exact: finite_convex_integral_geometric_open_closed_agreement hp.
rewrite he; exact: closed_convex_integral_geometric_measure_specification.
Qed.
