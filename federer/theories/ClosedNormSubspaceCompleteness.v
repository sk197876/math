(** Federer (1969), 3.1.1, p. 211: the closed separable linear
    target reduction preserves completeness. The inherited norm
    gives exactly the ambient metric on the subspace carrier. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import ModuleQuotient SubspaceCarrier RealNormUP NormMetric NormedSubspace
  CompleteMetricUP MetricCauchyImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_norm_subspace_complete]: supporting
    completeness of the reduced target in 3.1.1, p. 211.
    The original norm is restricted through the linear inclusion. *)
Theorem closed_norm_subspace_complete (R : realType) (Y : lmodType R)
    (N : Y -> R) (hN : is_real_norm N) (S : subspace Y) :
  is_complete_metric_space (real_norm_metric_space hN) ->
  closed (fun y : real_norm_metric_space hN => S y) ->
  is_complete_metric_space (real_norm_metric_space (subspace_norm_laws hN S)).
Proof.
move=> hY hS F PF hc.
pose E := real_norm_metric_space (subspace_norm_laws hN S).
pose T := real_norm_metric_space hN.
pose inc (x : E) : T := subspace_val x.
have FF : Filter F := @filter_filter _ F PF.
have PFi : ProperFilter (inc @ F) := @fmap_proper_filter E T inc F PF.
have hci : cauchy (inc @ F).
  apply: (@distance_nonincreasing_cauchy_image R E T inc F PF).
  - move=> x y; change (N (subspace_val x-subspace_val y)<=N (subspace_val (x-y))).
    by rewrite linearB.
  - exact hc.
have [y hy] := hY _ PFi hci.
have hyS : S y.
  apply: hS=> W hW.
  have [x hx] := @filter_ex E F PF _ (hy W hW).
  exists (inc x); split=> //; exact: subspace_valP x.
pose z : E := subspace_lift hyS.
exists z=> W hW.
have [r hr hb] := proj1 (metricType_numDomainType.nbhs_mdistP z W) hW.
have hn : nbhs y [set v : T | mdist y v<r].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP y _)); by exists r.
apply: (@filterS _ F FF _ _ _ (hy _ hn))=> x hx; apply: hb.
change (N (subspace_val (z-x))<r).
rewrite linearB /z; exact hx.
Qed.
