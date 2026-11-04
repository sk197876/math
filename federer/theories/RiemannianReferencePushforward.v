(** Federer (1969), 3.2.46, pp. 281–282: ordinary
    volume on the chart subtype pushes forward to L^n
    restricted to the original open A. This supports the
    printed ambient-coordinate integral without replacing
    completed measurability by Borel measurability. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanLebesgueDimensions RiemannianTensorUP
  RiemannianMetricCarrier RiemannianChartReference
  MeasureUP MeasurePushforward MeasureRestriction PushforwardMeasurabilityTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_chart_domain_open]: the independent
    domain-interior law gives exactly the usual open domain A,
    as stipulated in Federer 3.2.46, p. 281. *)
Lemma riemannian_chart_domain_open (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) :
  @open [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] A.
Proof.
rewrite openE=> a ha.
have [r [hr hA]] := riemannian_tensor_domain_open hg ha.
apply: (metricType_numDomainType.nbhs_mdistP a _).2.
exists r=> // x hx.
have hNorm : inner_norm (@euclidean_inner_productP R n) (x-a)<r.
  by rewrite -inner_metric_distanceE metric_sym.
have h := hA (x-a) hNorm.
by rewrite addrC subrK in h.
Qed.

(** Source for [riemannian_reference_pushforward]: the exact
    chart-to-ambient reference-measure identity, supporting
    3.2.46, pp. 281–282. All target subsets are retained. *)
Lemma riemannian_reference_pushforward (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) :
  measure_pushforward
    (fun x : riemannian_metric_space hg=>(val x : inner_metric_space (@euclidean_inner_productP R n)))
    (@riemannian_chart_reference R n A g hg) =
  measure_restrict (@euclidean_lebesgue_measure R n) A.
Proof.
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose M := [the metricType R of riemannian_metric_space hg].
apply: funext=> B.
rewrite /measure_pushforward (@riemannian_chart_reference_value R n A g hg).
congr (euclidean_lebesgue_measure n _).
apply/seteqP; split=> y.
- move=> [x hx <-]; split; first exact: set_valP x.
  exact hx.
- move=> [hAy hBy]; exists (@exist E (fun z=>z \in (A : set E)) y (mem_set hAy)); by [].
Qed.

(** Source for [riemannian_reference_measurable_preimage]:
    original Lebesgue-measurable subsets have measurable chart
    preimages, by the proved injection and exact pushforward
    identity, supporting 3.2.46, pp. 281–282. *)
Lemma riemannian_reference_measurable_preimage (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) B :
  measure_measurable (@euclidean_lebesgue_measure R n) B ->
  measure_measurable (@riemannian_chart_reference R n A g hg)
    ((fun x : riemannian_metric_space hg=>val x) @^-1` B).
Proof.
move=> hB.
apply: (@measure_pushforward_preimage_measurable R
  [the choiceType of riemannian_metric_space hg]
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
  (fun x=>val x) (@riemannian_chart_reference R n A g hg) B).
- by move=> x y h; exact: val_inj h.
- rewrite riemannian_reference_pushforward; exact: measure_restrict_measurable hB.
Qed.
