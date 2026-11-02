(** Opaque Euclidean Lebesgue family for Federer (1969),
    2.6.5, pp. 119–120. The signature exposes only
    the measures and their abstract inductive laws. Source
    editions: EuclideanLebesgueUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueUP EuclideanLebesgueConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type EuclideanLebesgueSignature.
(** Source for [value]: the finite Euclidean Lebesgue
    products of Federer 2.6.5, pp. 119–120. Stage n
    represents positive dimension n+1. *)
Parameter value : forall (R : realType) n,
  set (inner_metric_space (@euclidean_inner_productP R n.+1)) -> \bar R.
(** Source for [laws]: abstract product laws in Federer
    2.6.5, pp. 119–120, to be proved by the witness. *)
Parameter laws : forall R : realType, is_euclidean_lebesgue_family (@value R).
End EuclideanLebesgueSignature.
Module EuclideanLebesgue : EuclideanLebesgueSignature.
(** Source for [value]: private selection from proved
    existence of the family in Federer 2.6.5, pp. 119–120. *)
Definition value R := projT1 (cid (@euclidean_lebesgue_family_exists R)).
(** Source for [laws]: the selected family satisfies the
    inductive product laws of Federer 2.6.5, pp. 119–120. *)
Lemma laws R : is_euclidean_lebesgue_family (@value R).
Proof. exact: projT2 (cid (@euclidean_lebesgue_family_exists R)). Qed.
End EuclideanLebesgue.
