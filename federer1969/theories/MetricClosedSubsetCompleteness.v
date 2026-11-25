(** General topology supporting Federer (1969), 2.2.10, p. 65: a closed
    subset of a complete metric space is complete. We send a Cauchy filter
    through the distance-preserving inclusion, use ambient completeness and
    closedness, then lift the resulting limit to the subtype. Source
    editions: SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import CompleteMetricUP MetricSubsetBackground MetricCauchyImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [complete_closed_metric_subset]: supporting closed-subspace
    completeness in Federer 2.2.10, p. 65, used before applying 2.2.8 to the
    closed witness C. The empty closed subset is allowed; completeness
    itself does not assert inhabitance. *)
Theorem complete_closed_metric_subset (R : realType) (T : metricType R) (A : set T) :
  is_complete_metric_space T -> closed A ->
  is_complete_metric_space [the metricType R of metric_subset A].
Proof.
move=> hT hA F PF hc.
pose inc (x : metric_subset A) : T := val x.
have FF : Filter F := @filter_filter _ F PF.
have PF' : ProperFilter (inc @ F) := @fmap_proper_filter _ _ inc F PF.
have hc' : cauchy (inc @ F).
  apply: (@distance_nonincreasing_cauchy_image R
    [the metricType R of metric_subset A] T inc F PF)=> //.
have [x hx] := hT _ PF' hc'.
have hAx : A x.
  apply: hA=> U hU.
  have hFU : F (inc @^-1` U) := hx U hU.
  have [a ha] := @filter_ex _ F PF _ hFU.
  exists (inc a); split=> //; exact: set_valP.
pose a : metric_subset A := @exist T (fun y => y \in A) x (mem_set hAx).
exists a=> U hU.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP a U) hU.
have hn : nbhs x [set y | mdist x y < e].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP x _)); by exists e.
apply: (@filterS _ F FF _ _ _ (hx _ hn))=> b hxb.
apply: hb; exact hxb.
Qed.
