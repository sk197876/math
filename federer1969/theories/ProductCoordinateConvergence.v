(** General product topology supporting Federer (1969), 2.10.32, p. 196,
    Hausdorff closedness of the exterior-diameter constraint. Coordinatewise
    convergence of chosen endpoint families gives convergence in the product
    topology. This is background topology, not an extra assertion attributed
    to Federer. The index family may be arbitrary; the application has
    finitely many endpoint coordinates. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ArrowAsProduct.
Local Open Scope classical_set_scope.

(** Source for [product_coordinate_filter_convergence]: supporting
    topology for the closedness claim in 2.10.32,
    p. 196. No continuity of the chosen
    coordinate maps away from the limiting compact
    set is required. *)
Lemma product_coordinate_filter_convergence (A : Type) (I : eqType)
    (Y : I -> topologicalType) (F : set_system A)
    (f : A -> forall i, Y i) (y : forall i, Y i) :
  Filter F -> (forall i, (fun a=>f a i) @ F --> y i) -> f @ F --> y.
Proof.
move=> hF hc; apply/cvg_sup=> i.
move=> U /= [_ [[B hB <-] hy hU]].
have hn : nbhs (y i) B.
  rewrite openE in hB; exact: hB _ hy.
have hh := hc i B hn.
change (F [set a | U (f a)]).
apply: (@filterS A F hF [set a | B (f a i)] [set a | U (f a)] _ hh)=> a ha.
exact (hU (f a) ha).
Qed.
