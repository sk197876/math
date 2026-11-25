(** Federer (1969), 2.2.10(1), p. 67: disjoint images of two closed subsets
    of a complete separable metric space under a continuous map to a
    Hausdorff space are Borel separated. The public proof uses only abstract
    shrinking-branch laws and their sealed existence. Source context:
    SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import CompleteMetricUP BorelSeparation InseparableClosedBranchesUP
  InseparableClosedBranchesBasic InseparableClosedBranchesSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [disjoint_closed_images_borel_separated]: direct assertion
    (1) of Federer 2.2.10, p. 67, with all printed hypotheses retained.
    Failure of separation gives inseparable shrinking branches,
    contradicting completeness, continuity and Hausdorff separation of their
    limit images. *)
Theorem disjoint_closed_images_borel_separated (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (C D : set T) :
  is_complete_metric_space T ->
  (exists H : set T, countable H /\ dense H) ->
  hausdorff_space Y -> continuous f -> closed C -> closed D ->
  (f @` C) `&` (f @` D) = set0 -> borel_separated (f @` C) (f @` D).
Proof.
move=> hT [H [hc hd]] hY hf hC hD hdis; apply: contrapT=> hn.
pose W := @InseparableClosedBranches.value R T Y f H hc hd C D hC hD hn.
have hW : is_inseparable_closed_branches f C D W.1 W.2 :=
  @InseparableClosedBranches.laws R T Y f H hc hd C D hC hD hn.
exact: (@inseparable_closed_branches_contradiction R T Y f C D W.1 W.2 hT hY hf hdis hW).
Qed.
