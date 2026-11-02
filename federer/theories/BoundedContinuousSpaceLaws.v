(** Federer (1969), 2.5.16, p. 110: "the Banach space E of all bounded real
    valued continuous functions on Y with the norm nu(f) = sup im |f|
    whenever f in E". From the abstract specification of
    BoundedContinuousSpaceUP.v this module proves that nu is a norm in the
    sense of 1.10.5, pp. 47–48, and 2.4.12, p. 86, and that E is complete
    for the metric of 2.2.7, p. 64, in the sense of 2.2.8, p. 64.
    Completeness follows from the real completeness of 2.2.9, p. 65: the
    values at each point of Y of a Cauchy filter on E form a real Cauchy
    filter; the pointwise limit is a uniform limit, hence bounded and
    continuous, and it is the limit of the filter in E. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealMetricBackground RealNormUP NormMetric CompleteMetricUP
  RealMetricCompleteness MetricCauchyImages MetricBoundedContinuousEmbedding UniformFunctionNormUP
  UniformFunctionNormLaws BoundedContinuousSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Laws.
Variable R : realType.
Variable Y : metricType R.
Variable V : lmodType R.
Variable ev : V -> Y -> R.
Variable N : V -> R.
Hypothesis hv : is_bounded_continuous_space ev N.

(** Source for [bounded_continuous_evaluation_zero]: the zero of E
    is the zero function, Federer 2.5.16, p. 110. *)
Lemma bounded_continuous_evaluation_zero : ev 0 = (fun _ => 0).
Proof.
apply: funext=> y.
have h := bounded_continuous_evaluation_linear hv (-1) 0 0 y.
by rewrite scaler0 addr0 mulN1r addNr in h.
Qed.

(** Source for [bounded_continuous_evaluation_add]: addition in E
    is pointwise, Federer 2.5.16, p. 110. *)
Lemma bounded_continuous_evaluation_add u v : ev (u + v) = (fun y => ev u y + ev v y).
Proof.
apply: funext=> y; have h := bounded_continuous_evaluation_linear hv 1 u v y.
by rewrite scale1r mul1r in h.
Qed.

(** Source for [bounded_continuous_evaluation_scale]: scalar
    multiplication in E is pointwise, Federer 2.5.16, p. 110. *)
Lemma bounded_continuous_evaluation_scale c u : ev (c *: u) = (fun y => c * ev u y).
Proof.
apply: funext=> y; have h := bounded_continuous_evaluation_linear hv c u 0 y.
by rewrite addr0 bounded_continuous_evaluation_zero addr0 in h.
Qed.

(** Source for [bounded_continuous_evaluation_subtract]: differences
    in E are pointwise, Federer 2.5.16, p. 110. *)
Lemma bounded_continuous_evaluation_subtract u v : ev (u - v) = (fun y => ev u y - ev v y).
Proof.
rewrite -scaleN1r bounded_continuous_evaluation_add bounded_continuous_evaluation_scale.
by apply: funext=> y; rewrite mulN1r.
Qed.

(** Source for [bounded_continuous_evaluation_bound]: |f(y)| <= nu(f)
    for f in E and y in Y, Federer 2.5.16, p. 110. *)
Lemma bounded_continuous_evaluation_bound v y : `|ev v y| <= N v.
Proof. exact: uniform_function_norm_bound (bounded_continuous_norm_supremum hv v) y. Qed.

(** Source for [bounded_continuous_norm_least]: nu(f) <= c whenever
    0 <= c and |f(y)| <= c for y in Y, the supremum in Federer 2.5.16,
    p. 110. *)
Lemma bounded_continuous_norm_least v c : 0 <= c -> (forall y, `|ev v y| <= c) -> N v <= c.
Proof.
move=> hc hb; exact: (uniform_function_norm_least (bounded_continuous_norm_supremum hv v) hc hb).
Qed.

(** Source for [bounded_continuous_norm_laws]: nu(f) = sup im |f| is
    a norm on E, Federer 2.5.16, p. 110, in the sense of 1.10.5,
    pp. 47–48, and 2.4.12, p. 86. *)
Theorem bounded_continuous_norm_laws : is_real_norm N.
Proof.
split.
- constructor.
  + move=> v; exact: uniform_function_norm_nonnegative (bounded_continuous_norm_supremum hv v).
  + move=> c u.
    have h := bounded_continuous_norm_supremum hv (c *: u).
    rewrite bounded_continuous_evaluation_scale in h.
    exact: uniform_function_norm_unique h
      (uniform_function_norm_scale c (bounded_continuous_norm_supremum hv u)).
  + move=> u v.
    have h := bounded_continuous_norm_supremum hv (u + v).
    rewrite bounded_continuous_evaluation_add in h.
    exact: uniform_function_norm_triangle (bounded_continuous_norm_supremum hv u)
      (bounded_continuous_norm_supremum hv v) h.
- move=> v hz; apply: (bounded_continuous_evaluation_injective hv).
  rewrite bounded_continuous_evaluation_zero; apply: funext=> y.
  have h := bounded_continuous_norm_supremum hv v.
  rewrite hz in h; exact: uniform_function_norm_separates h y.
Qed.

Local Notation E := (real_norm_metric_space bounded_continuous_norm_laws).

(** Source for [bounded_continuous_evaluation_lipschitz]: evaluation
    at a point of Y does not increase distances in E,
    |f(y) - g(y)| <= nu(f - g), Federer 2.5.16, p. 110. *)
Lemma bounded_continuous_evaluation_lipschitz (u v : E) y :
  `|ev u y - ev v y| <= mdist u v.
Proof.
rewrite real_norm_metric_distanceE.
have h := bounded_continuous_evaluation_bound (u - v) y.
by rewrite bounded_continuous_evaluation_subtract in h.
Qed.

(** Source for [bounded_continuous_cauchy_uniform]: supporting step of
    the completeness of E, Federer 2.5.16, p. 110: if a proper Cauchy
    filter on E has pointwise limit h, then for every e > 0 it
    contains a set on which |f(y) - h(y)| <= e for all y in Y. *)
Lemma bounded_continuous_cauchy_uniform (F : set_system E) (h : Y -> R) :
  ProperFilter F -> cauchy F ->
  (forall y, (fun u : E => (ev u y : real_line_metric R)) @ F --> (h y : real_line_metric R)) ->
  forall e, 0 < e -> exists2 B, F B & forall u, B u -> forall y, `|ev u y - h y| <= e.
Proof.
move=> PF hc hh e he.
have FF : Filter F := @filter_filter _ F PF.
have he2 : 0 < e / 2 by rewrite divr_gt0 // ltr0n.
have [c hcB] := (proj1 (cauchyP F) hc) (e / 2) he2.
exists (ball c (e / 2))=> // u hu y.
apply/ler_addgt0Pr=> d hd.
have hnb : nbhs (h y : real_line_metric R) [set z : real_line_metric R | mdist (h y : real_line_metric R) z < d].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (h y : real_line_metric R) _)).
  by exists d=> // z hz.
have hF := hh y _ hnb.
have [u' [hu' hu'y]] := @filter_ex _ _ PF _ (@filterI _ _ FF _ _ hcB hF).
have hd' : `|h y - ev u' y| < d by move: hu'y; rewrite /= real_line_metric_distanceE.
have huu' : `|ev u y - ev u' y| < e.
  apply: le_lt_trans (bounded_continuous_evaluation_lipschitz u u' y) _.
  move: hu hu'; rewrite !ballEmdist /= => h1 h2.
  apply: le_lt_trans (metric_triangle u c u') _.
  rewrite metric_sym (splitr e); exact: ltrD h1 h2.
apply: ltW; rewrite -(subrK (ev u' y) (ev u y)) -addrA.
apply: le_lt_trans (ler_normD _ _) _.
by apply: ltrD=> //; rewrite distrC.
Qed.

(** Source for [bounded_continuous_space_complete]: E is a Banach
    space, Federer 2.5.16, p. 110: complete for the metric
    induced by nu in the sense of 2.2.8, p. 64. *)
Theorem bounded_continuous_space_complete : is_complete_metric_space [the metricType R of E].
Proof.
move=> F PF hc.
have FF : Filter F := @filter_filter _ F PF.
have hpt : forall y, exists l : real_line_metric R,
    (fun u : E => (ev u y : real_line_metric R)) @ F --> l.
  move=> y.
  pose f (u : E) : real_line_metric R := ev u y.
  have hnon : forall u u' : E, mdist (f u) (f u') <= mdist u u'.
    move=> u u'; rewrite real_line_metric_distanceE; exact: bounded_continuous_evaluation_lipschitz.
  have hfc := @distance_nonincreasing_cauchy_image R [the metricType R of E]
    [the metricType R of real_line_metric R] f F PF hnon hc.
  exact: (@real_line_metric_complete R (f @ F) (@fmap_proper_filter _ _ f F PF) hfc).
have [h hh] := choice hpt.
have hunif := bounded_continuous_cauchy_uniform PF hc hh.
have hhb : bounded_continuous_functions h.
  split.
  - move=> y0; apply/cvgrPdist_lt=> eps heps.
    have he3 : 0 < eps / 3 by rewrite divr_gt0 // ltr0n.
    have [B hB hBu] := hunif _ he3.
    have [u hu] := @filter_ex _ _ PF _ hB.
    have hcu := (bounded_continuous_evaluation_member hv u).1 y0.
    have FY : Filter (nbhs y0) := @nbhs_filter Y y0.
    have hnear := (proj1 (cvgrPdist_lt _ _) hcu) _ he3.
    near=> y.
    have hy : `|ev u y0 - ev u y| < eps / 3 by near: y; exact: hnear.
    have h1 : `|h y0 - ev u y0| <= eps / 3 by rewrite distrC; exact: hBu u hu y0.
    have h2 := hBu u hu y.
    have hsum : `|h y0 - h y| <= `|h y0 - ev u y0| + `|ev u y0 - ev u y| + `|ev u y - h y|.
      have he : h y0 - h y = (h y0 - ev u y0) + (ev u y0 - ev u y) + (ev u y - h y).
        by ring.
      rewrite he; apply: le_trans (ler_normD _ _) _.
      by apply: lerD (ler_normD _ _) (lexx _).
    lra.
    Unshelve. all: end_near.
  - have [B hB hBu] := hunif _ ltr01.
    have [u hu] := @filter_ex _ _ PF _ hB.
    exists (N u + 1)=> y.
    have h1 := hBu u hu y.
    have h2 := bounded_continuous_evaluation_bound u y.
    have h3 : `|h y| <= `|ev u y| + `|ev u y - h y|.
      have he : h y = ev u y - (ev u y - h y) by ring.
      by rewrite [in X in X <= _]he; exact: ler_normB.
    lra.
have [v hev] := bounded_continuous_evaluation_surjective hv hhb.
exists (v : E)=> U hU.
have [e he hsub] := proj1 (metricType_numDomainType.nbhs_mdistP (v : E) U) hU.
have he2 : 0 < e / 2 by rewrite divr_gt0 // ltr0n.
have [B hB hBu] := hunif _ he2.
apply: (@filterS _ F FF _ _ _ hB)=> u hu; apply: hsub.
rewrite /= real_norm_metric_distanceE.
have hle : N (v - u) <= e / 2.
  apply: (bounded_continuous_norm_least (ltW he2))=> y.
  rewrite bounded_continuous_evaluation_subtract hev distrC; exact: hBu u hu y.
lra.
Qed.

End Laws.
