(** Federer (1969), 3.3.19, pp. 302–304:
    the original nested-disc set has convex
    integral-geometric mass Q_1^1 at least pi.
    The distinction from all-Borel I_1 is retained. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets cardinality constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex
  CircularTrigonometryUP CircularTrigonometrySealed RealTrigonometryUP CircularDiscTreeUP CircularDiscLimitUP
  CircularDiscConvexCoverLower IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricMeasureUP
  ProjectionMeasureUP CaratheodoryLimitUP MetricScaleEnvelopeUP MetricScaleEnvelope
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Lower.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation Q:=(@convex_integral_geometric_measure R 2 1 (leqnSn 1) 1).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_first_convex_mass_strict_lower]:
    every 0<lambda<pi is a lower bound
    for original Q_1^1(A), from the actual
    small-cover estimate of 3.3.19,
    pp. 302–304. The independent covering
    infimum and supremum laws discharge the passage
    from countable covers to the final measure. *)
Lemma circular_disc_first_convex_mass_strict_lower (lam:R):
  0<lam ->lam<p ->(lam%:E<=Q A)%E.
Proof.
move=>hLam hLamP.
have [d [hd hCover]]:=@circular_disc_small_convex_cover_lower R H hH A hA lam hLam hLamP.
pose I:=open_convex_euclidean_sets R 2.
pose S:=fun i:I=>val i.
pose c:=fun i:I=>@integral_geometric_gauge R 2 1 (leqnSn 1) 1 (val i).
pose nu:=metric_scale_envelope S c d%:E.
have hNu:=metric_scale_envelope_specification S c d%:E.
have hLower:(lam%:E<=nu A)%E.
  apply:(@metric_scale_envelope_greatest R [the metricType R of E] I S c d%:E nu hNu A lam%:E).
  move=>D hCountable hDiameter hCovered.
  exact:(hCover I D S hCountable (fun i hi=>conj (set_valP i).1
    (conj (set_valP i).2 (hDiameter i hi))) hCovered).
have hdE:(0<d%:E)%E by rewrite lte_fin.
have hFinal:=@caratheodory_limit_upper R [the metricType R of E] I S c Q
  (@convex_integral_geometric_measure_specification R 2 1 (leqnSn 1) 1) A d%:E nu
  hdE hNu.
exact:(le_trans hLower hFinal).
Qed.

(** Source for [circular_disc_first_convex_mass_lower]:
    Q_1^1(A)>=pi, the conclusion of
    the countable convex-cover argument in 3.3.19,
    p. 304. Positivity of pi and the
    actual measure remove the strict lambda error;
    no finite-mass or conclusion premise is added. *)
Theorem circular_disc_first_convex_mass_lower:(p%:E<=Q A)%E.
Proof.
have hp:0<p:=real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
have hNonnegative:=@measure_nonnegative R E Q
  (@convex_integral_geometric_measure_is_measure R 2 1 (leqnSn 1) 1 (lexx _)) A.
case hMass:(Q A) hNonnegative=>[v| |] hNonnegative.
- rewrite ?hMass ?lee_fin in hNonnegative *.
  case:(leP p v)=>hOrder;first by [].
  pose lam:R:=(p+v)/2.
  have hLam:0<lam by rewrite /lam;lra.
  have hLamP:lam<p by rewrite /lam;lra.
  have hBound:=@circular_disc_first_convex_mass_strict_lower lam hLam hLamP.
  rewrite hMass lee_fin in hBound;rewrite /lam in hBound;lra.
- exact:leey.
- by move:hNonnegative.
Qed.
End Lower.
