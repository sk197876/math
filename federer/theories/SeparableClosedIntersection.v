(** General topology supporting Federer (1969), 2.4.19, p. 91: intersect the
    essentially separable range with C before constructing C-valued finite
    approximants. The supporting separability argument uses metric subspaces
    and the already proved closed-subset theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import MetricSubsetBackground MetricClosedSubsetSeparability SeparableClosedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [separable_closed_intersection]: supporting separability of C
    intersect the separable range in Federer 2.4.19, p. 91 The ambient
    metric space need not be separable. *)
Lemma separable_closed_intersection (R : realType) (T : metricType R) (Z C : set T) :
  (exists D : set (metric_subset Z), countable D /\ dense D) ->
  closed C -> Z `&` C !=set0 ->
  exists H : set (metric_subset (Z `&` C)), countable H /\ dense H.
Proof.
move=> hZ hC [z [hzZ hzC]].
pose B : set (metric_subset Z) := [set x | C (val x)].
have hB : closed B.
  exact: (proj1 (continuous_closedP (fun x : metric_subset Z => (val x : T)))
    (@metric_subset_inclusion_continuous R T Z) C hC).
have hBn : B !=set0.
  exists (@exist T (fun x => x \in Z) z (mem_set hzZ)); exact hzC.
have [D [hc hd]] := @nonempty_closed_metric_subset_separable R
  [the metricType R of metric_subset Z] B hZ hB hBn.
pose i (w : metric_subset B) : metric_subset (Z `&` C) :=
  @exist T (fun x => x \in (Z `&` C)) (val (val w))
    (mem_set (conj (set_valP (val w)) (set_valP w))).
exists (i @` D); split; first exact: sub_countable (card_image_le _ _) hc.
move=> W [x hx] ho.
have hn : nbhs x W by rewrite openE in ho; exact: ho x hx.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP x W) hn.
pose xZ : metric_subset Z := @exist T (fun y => y \in Z) (val x) (mem_set (set_valP x).1).
pose xB : metric_subset B := @exist (metric_subset Z) (fun y => y \in B) xZ (mem_set (set_valP x).2).
have [w [hw hnear]] := @metric_dense_point_near R [the metricType R of metric_subset B] D hd xB e he.
exists (i w); split; last by exists w.
apply: hb; exact hnear.
Qed.
