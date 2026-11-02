(** Federer (1969), 2.2.15, p. 71: opaque interface for the integer-cell
    approximants h_i. Source context and scalar background:
    RealQuantisationConstruction.v. The floor witness is private; clients
    use only cell membership and the cellwise value. *)
From mathcomp Require Import all_boot boolp classical_sets reals.
From Federer Require Import RealQuantisationUP RealQuantisationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type RealQuantisationSignature.
(** Source for [value]: abstract approximant h_i in
    Federer 2.2.15, p. 71, with positive i=k+1. *)
Parameter value : forall (R : realType) (X : Type), (X -> R) -> nat -> X -> R.
(** Source for [laws]: the integer-cell and value laws
    of h_i in Federer 2.2.15, p. 71. *)
Parameter laws : forall (R : realType) (X : Type) (f : X -> R) k,
  is_real_quantisation f (@value R X f k) k.
End RealQuantisationSignature.

Module RealQuantisation : RealQuantisationSignature.
(** Source for [value]: private selection of the proved
    approximant witness for Federer 2.2.15, p. 71. *)
Definition value (R : realType) (X : Type) (f : X -> R) k :=
  projT1 (cid (@real_quantisation_exists R X f k)).
(** Source for [laws]: the selected approximant satisfies
    the abstract specification of Federer 2.2.15, p. 71. *)
Lemma laws (R : realType) (X : Type) (f : X -> R) k :
  is_real_quantisation f (@value R X f k) k.
Proof. exact: projT2 (cid (@real_quantisation_exists R X f k)). Qed.
End RealQuantisation.
