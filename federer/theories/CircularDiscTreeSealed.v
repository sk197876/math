(** Opaque original disc families for Federer (1969),
    3.3.19, p. 302; only the independent recurrence is exposed. *)
From mathcomp Require Import all_boot finmap boolp reals.
From Federer Require Import EuclideanInnerProduct InnerMetric CircularDiscTreeUP CircularDiscTreeConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CircularDiscTreeSignature.
(** Source for [centres]: original finite centre family
    G_n in 3.3.19, p. 302, indexed by n-3. *)
Parameter centres:forall R:realType,nat->{fset inner_metric_space (@euclidean_inner_productP R 2)}.
(** Source for [laws]: actual unit-root and child-refinement
    laws of 3.3.19, p. 302, proved by existence. *)
Parameter laws:forall R:realType,@is_circular_disc_tree R (@centres R).
End CircularDiscTreeSignature.
Module CircularDiscTree:CircularDiscTreeSignature.
(** Source for [centres]: hidden recursive witness for
    the families in 3.3.19, p. 302. *)
Definition centres (R:realType):=projT1 (cid (circular_disc_tree_exists R)).
(** Source for [laws]: the hidden witness satisfies the
    independent recurrence of 3.3.19, p. 302. *)
Lemma laws (R:realType):@is_circular_disc_tree R (@centres R).
Proof. exact:(projT2 (cid (circular_disc_tree_exists R))). Qed.
End CircularDiscTree.
