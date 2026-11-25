(** The real scalar target used in the local counterexample to Federer
    (1969), 2.3.8, p. 78, is a Banach space with its absolute-value norm.
    This adapter transports the real completeness already justified in
    RealMetricCompleteness.v to the abstract norm metric. Source context:
    MeasurableNormedFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP RealMetricBackground RealMetricCompleteness
  MetricCauchyImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_norm_metric_complete]: the real scalar
    target satisfies the Banach completeness hypothesis of Federer
    2.3.8, p. 78. Its metric is exactly the ordinary
    real absolute-difference metric. *)
Lemma scalar_norm_metric_complete (R : realType) :
  is_complete_metric_space [the metricType R of real_norm_metric_space (scalar_absolute_value_norm R)].
Proof.
pose M := real_norm_metric_space (scalar_absolute_value_norm R).
pose L := real_line_metric R.
move=> F PF hc.
pose f (x : M) : L := x.
have PF' : ProperFilter (f @ F) := @fmap_proper_filter M L f F PF.
have hnon : forall x y : M, mdist (f x) (f y) <= mdist x y.
  move=> x y; change (`|x-y| <= `|x-y|); exact: lexx.
have hfc := @distance_nonincreasing_cauchy_image R [the metricType R of M] [the metricType R of L] f F PF hnon hc.
have [x hx] := @real_line_metric_complete R (f @ F) PF' hfc.
exists (x : M)=> U hu.
have [e he hsub] := proj1 (metricType_numDomainType.nbhs_mdistP (x : M) U) hu.
have hnb : nbhs (x : L) [set y : L | mdist x y < e].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (x : L) _)); exists e=> // y hy; exact hy.
have hh := hx _ hnb.
apply: (@filterS M F (@filter_filter M F PF) _ _ _ hh)=> y hy.
apply: hsub; exact hy.
Qed.
