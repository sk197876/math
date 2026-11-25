(** Federer (1969), 2.2.10, p. 67: pairwise disjoint images of a sequence of
    Suslin sets have pairwise disjoint Borel supersets. Source context:
    SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets cardinality reals topology.
From Federer Require Import CompleteMetricUP SuslinSetUP TopologicalBorel
  SuslinImageSeparation BorelDisjointContainers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [disjoint_suslin_images_borel_containers]: direct consequence
    after (1) in Federer 2.2.10, p. 67. Pairwise separation supplies the
    disjoint Borel supersets by the locally proved countable separator
    construction. *)
Theorem disjoint_suslin_images_borel_containers (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (S : nat -> set T) :
  is_complete_metric_space T ->
  (exists H : set T, countable H /\ dense H) -> hausdorff_space Y -> continuous f ->
  (forall i, is_suslin_set R (S i)) ->
  (forall i j, i <> j -> (f @` S i) `&` (f @` S j) = set0) ->
  exists B : nat -> set Y,
    (forall i, borel_set (B i) /\ (f @` S i) `<=` B i) /\
    forall i j, i <> j -> B i `&` B j = set0.
Proof.
move=> hT hsep hY hf hS hdis; apply: pairwise_separated_borel_containers=> i j hij.
exact: (@disjoint_suslin_images_borel_separated R T Y f (S i) (S j)
  hT hsep hY hf (hS i) (hS j) (hdis i j hij)).
Qed.
