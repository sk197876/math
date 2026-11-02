(** Federer (1969), 1.7.13, p. 37: a Hilbert space is an inner-product space
    complete for the metric |x-y|. Completeness below is the general
    topological property that every proper Cauchy filter converges. The
    metric and norm are the locally proved inner-product metric and norm of
    1.7.1. The local May 1987 erratum has no correction to p. 37. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From mathcomp Require Import classical_sets topology.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_hilbert_space]: Federer 1.7.13, p. 37,
    opening definition: completeness for the specified inner-product
    metric. This is a property to be proved or assumed of the
    supplied space, not a global completeness axiom or a construction. *)
Definition is_hilbert_space (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) : Prop :=
  forall F : set_system (inner_metric_space hB),
    ProperFilter F -> cauchy F -> cvg F.
