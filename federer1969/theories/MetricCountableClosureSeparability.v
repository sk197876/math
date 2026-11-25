(** General topology for the separable closed spans supporting Federer
    (1969), 2.3.8, p. 78. The closure of a countable set is separable in its
    induced metric. Source context: ClosedLinearSpanUP.v. Empty sets and
    empty subspaces need no chosen inhabitant. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import MetricSubsetBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [countable_metric_closure_separable]: supporting
    separability of the closed countable hull for Federer 2.3.8,
    p. 78; the original countable set, lifted into its closure,
    is dense there. *)
Theorem countable_metric_closure_separable (R : realType) (T : metricType R)
    (D : set T) : countable D ->
  exists H : set (metric_subset (closure D)), countable H /\ dense H.
Proof.
move=> hc.
pose q (z : set_type D) : metric_subset (closure D) :=
  @exist T (fun x => x \in closure D) (val z)
    (mem_set (@subset_closure T D (val z) (set_valP z))).
exists (q @` setT); split.
- apply: sub_countable (card_image_le _ _) _.
  by rewrite (eq_countable (card_setT D)).
- move=> W [x hx] ho.
  have hnb : nbhs x W by rewrite openE in ho; exact: ho x hx.
  have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP x W) hnb.
  have hball : nbhs (val x) [set y : T | mdist (val x) y < e].
    apply: (proj2 (metricType_numDomainType.nbhs_mdistP (val x) _)).
    exists e=> // y hy; exact hy.
  have hcl : closure D (val x) := set_valP x.
  have [y [hy hd]] := hcl _ hball.
  pose z : set_type D := @exist T (fun y => y \in D) y (mem_set hy).
  exists (q z); split.
  + apply: hb; exact hd.
  + by exists z.
Qed.
