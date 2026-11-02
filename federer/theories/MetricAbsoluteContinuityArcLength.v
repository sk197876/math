(** Federer (1969), 2.9.22, pp. 167–168: normed absolute continuity extends
    2.9.20(3), pp. 165–166. The first consequent implication in its proof
    bounds sums of variations by the same epsilon. Hence a locally BV metric
    curve satisfies this law exactly when its scalar arc-length parameter
    does. This supporting equivalence uses the printed finite-family
    argument, with no derivative or reflexivity hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology lra.
From Federer Require Import CurveArcLength CurveLipschitzFactor
  MetricCurveAbsoluteContinuityUP MetricIntervalFamilyNearVariation
  OrderedIntervalFamilyUP RealAbsoluteContinuityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [metric_increment_family_bound_variations]: supporting metric
    extension in Federer 2.9.22, pp. 167–168, of the first consequence of
    condition (3) in 2.9.20, p. 166 Approximate the finitely many variations
    from below by one eligible refinement, preserving length, then let its
    arbitrary positive error vanish. *)
Lemma metric_increment_family_bound_variations (R : realType) (Y : metricType R)
    (g : R -> Y) (a b d e : R) (s : seq (R * R)) :
  curve_locally_finite_variation g ->
  (forall t, is_ordered_real_interval_family a b t -> real_interval_family_length t<=d ->
    metric_interval_family_increment_sum g t<=e) ->
  is_ordered_real_interval_family a b s -> real_interval_family_length s<=d ->
  metric_interval_family_variation_sum g s<=e.
Proof.
move=> hg hf hs hlen; apply/ler_addgt0Pr=> eta heta.
have [t [ht [htLen hgap]]] := @metric_ordered_interval_family_near_variation R Y g a b s eta hg hs heta.
have htSmall : real_interval_family_length t<=d by rewrite htLen.
have hb := hf t ht htSmall.
lra.
Qed.

(** Source for [metric_family_arc_variation_sum]: supporting
    arc-length identity for the metric extension in Federer 2.9.22,
    pp. 167–168, of 2.9.20(3), p. 166. The sum of scalar
    arc-length increments is exactly the sum of the original cell
    variations, by the ordered increment identity of 2.5.16, p. 109. *)
Lemma metric_family_arc_variation_sum (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) (s : seq (R * R)) :
  curve_locally_finite_variation g -> is_ordered_real_interval_family a b s ->
  real_interval_family_increment_sum (arc_length g) s=metric_interval_family_variation_sum g s.
Proof.
move=> hg hs; rewrite /real_interval_family_increment_sum /metric_interval_family_variation_sum.
rewrite !big_seq.
apply: eq_bigr=> [[u v] huv].
have [_ [hUV _]] := ordered_real_interval_family_cell_bounds hs huv.
have hmono : 0<=arc_length g v-arc_length g u.
  rewrite subr_ge0; exact (@arc_length_monotone R Y g hg u v (ltW hUV)).
rewrite (ger0_norm hmono).
by rewrite -(@arc_length_increment R Y g hg u v (ltW hUV)).
Qed.

(** Source for [metric_family_cost_below_arc_cost]: supporting
    distance/variation estimate for Federer 2.9.22, pp. 167–168,
    using 2.5.16, p. 109. Any finite family's metric endpoint
    cost is at most its scalar arc-length cost; no ordering is needed
    for this absolute-increment inequality. *)
Lemma metric_family_cost_below_arc_cost (R : realType) (Y : metricType R)
    (g : R -> Y) (s : seq (R * R)) : curve_locally_finite_variation g ->
  metric_interval_family_increment_sum g s<=real_interval_family_increment_sum (arc_length g) s.
Proof.
move=> hg; rewrite /metric_interval_family_increment_sum /real_interval_family_increment_sum.
apply: ler_sum=> [[u v] huv].
have h := @arc_length_distance_abs R Y g hg u v.
by rewrite distrC in h.
Qed.

(** Source for [metric_absolute_continuity_arc_length]: supporting
    equivalence for Federer 2.9.22, pp. 167–168, extending the finite-family
    argument of 2.9.20(3), p. 166 The same finite-family bounds apply to
    total variations, hence to arc-length increments. Conversely endpoint
    distances are bounded by those increments. Singleton or empty source
    intervals are permitted without changing the abstract epsilon law. *)
Theorem metric_absolute_continuity_arc_length (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : curve_locally_finite_variation g ->
  (is_absolutely_continuous_metric_curve g a b <->
    is_absolutely_continuous_real_curve (arc_length g) a b).
Proof.
move=> hg; split=> hAC e he; have [d [hd hb]] := hAC e he.
- exists d; split=> // s hs hlen.
  rewrite (@metric_family_arc_variation_sum R Y g a b s hg hs).
  exact (@metric_increment_family_bound_variations R Y g a b d e s hg hb hs hlen).
- exists d; split=> // s hs hlen.
  exact: le_trans (@metric_family_cost_below_arc_cost R Y g s hg) (hb s hs hlen).
Qed.
