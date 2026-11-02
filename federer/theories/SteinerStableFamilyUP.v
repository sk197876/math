(** Federer (1969), 2.10.31, pp. 195–196: the class C of nonempty compact
    sets is closed for the Hausdorff metric and preserved by every
    hyperplane Steiner symmetrisation. This file states the preservation
    predicate; nonemptiness and closedness are separate hypotheses of the
    subsequent theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import InnerProductUP InnerMetric CompactSetDistanceProfile CompactHausdorffMetric
  SteinerSymmetrisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_steiner_stable_family]: direct stability
    assumption of 2.10.31, p. 195. Normal
    choice does not affect the operation by the
    previously proved 2.10.30 laws. The existential
    image remains a nonempty compact member of C;
    no global operation on arbitrary family codes
    or additional project axiom is postulated. *)
Definition is_steiner_stable_family (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (C : set (compact_hausdorff_space (inner_metric_space hB))) :=
  forall (S : compact_hausdorff_space (inner_metric_space hB)), C S ->
  forall u : V, B u u= 1 ->
  exists T : compact_hausdorff_space (inner_metric_space hB),
    C T /\ is_steiner_symmetrisation hB u (val S) (val T).
Arguments is_steiner_stable_family {R V B} hB C.
