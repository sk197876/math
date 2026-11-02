(** General topology supporting Federer (1969), 2.2.10, p. 65: a continuous
    parametrisation with image contained in S is continuous as a map into
    the metric subspace S. This permits composition with maps defined only
    on S, as in the printed continuous-image assertion. Source context:
    SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import MetricSubsetBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_subset_corestriction]: supporting codomain
    restriction for Federer 2.2.10, p. 65: a map with
    values in A is regarded as a map into the subtype A. *)
Definition metric_subset_corestriction (R : realType) (T : metricType R)
    (X : Type) (A : set T) (f : X -> T) (hfA : forall x, A (f x))
    (x : X) : metric_subset A :=
  @exist T (fun y => y \in A) (f x) (mem_set (hfA x)).

(** Source for [metric_subset_corestriction_continuous]: supporting
    relative continuity for the composition f composed with h in
    Federer 2.2.10, p. 65. No ambient continuous extension
    of the map defined on the Suslin subset is assumed. *)
Lemma metric_subset_corestriction_continuous (R : realType) (T : metricType R)
    (X : topologicalType) (A : set T) (f : X -> T) (hfA : forall x, A (f x)) :
  continuous f -> continuous (metric_subset_corestriction hfA).
Proof.
move=> hf x U hU.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP
  (metric_subset_corestriction hfA x) U) hU.
have hn : nbhs (f x) [set y | mdist (f x) y < e].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP (f x) _)); by exists e.
have hn' : nbhs x [set y | mdist (f x) (f y) < e] := hf x _ hn.
apply: (filterS _ hn')=> y hy; apply: hb; exact hy.
Qed.
