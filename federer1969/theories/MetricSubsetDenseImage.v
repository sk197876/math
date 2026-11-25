(** General topology supporting Federer (1969), 2.3.8, p. 78: countable
    dense subsets of separable subspaces provide countable ambient
    generators. Source context: ClosedLinearSpanUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import MetricSubsetBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_subset_dense_image_closure]: supporting
    closure relation for the separable-span reduction in Federer
    2.3.8, p. 78: the ambient image of a relatively dense
    set has closure containing the entire subspace. *)
Lemma metric_subset_dense_image_closure (R : realType) (T : metricType R)
    (A : set T) (D : set (metric_subset A)) : dense D ->
  A `<=` closure ((fun z : metric_subset A => (val z : T)) @` D).
Proof.
move=> hd x hx W hW.
pose z : metric_subset A := @exist T (fun y => y \in A) x (mem_set hx).
have hnb : nbhs z [set t : metric_subset A | W (val t)].
  exact: (@metric_subset_inclusion_continuous R T A z W hW).
have [U [hU hz] hUW] := hnb.
have [w [hw hD]] := hd U (ex_intro _ z hz) hU.
exists (val w); split.
- by exists w.
- exact: hUW w hw.
Qed.

(** Source for [metric_subset_dense_image_countable]: supporting
    countability of ambient generators in Federer 2.3.8,
    p. 78, from a countable relative dense set. *)
Lemma metric_subset_dense_image_countable (R : realType) (T : metricType R)
    (A : set T) (D : set (metric_subset A)) : countable D ->
  countable ((fun z : metric_subset A => (val z : T)) @` D).
Proof. exact: sub_countable (card_image_le _ _). Qed.
