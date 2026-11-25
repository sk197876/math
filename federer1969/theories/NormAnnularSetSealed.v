(** Opaque annular-set choice for Federer (1969),
    3.2.16, p. 253. Only the independent
    exact membership law is available downstream. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import NormAnnularSetUP NormAnnularSetConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type NormAnnularSetSignature.
(** Source for [value]: the annular set T,
    Federer 3.2.16, p. 253. *)
Parameter value : forall (R : realType) (X : lmodType R),
  (X -> R) -> (nat -> set X) -> X -> (nat -> R) -> set X.
(** Source for [laws]: exact annular membership,
    Federer 3.2.16, p. 253. *)
Parameter laws : forall (R : realType) (X : lmodType R)
  (NX : X -> R) (S : nat -> set X) (a : X) (rho : nat -> R),
  is_norm_annular_set NX S a rho (@value R X NX S a rho).
End NormAnnularSetSignature.
Module NormAnnularSet : NormAnnularSetSignature.
(** Source for [value]: selection from the proved
    set existence in Federer 3.2.16, p. 253. *)
Definition value (R : realType) (X : lmodType R)
  (NX : X -> R) (S : nat -> set X) (a : X) (rho : nat -> R) :=
  projT1 (cid (@norm_annular_set_exists R X NX S a rho)).
(** Source for [laws]: the witness satisfies the
    exact annular specification, Federer 3.2.16, p. 253. *)
Lemma laws (R : realType) (X : lmodType R)
  (NX : X -> R) (S : nat -> set X) (a : X) (rho : nat -> R) :
  is_norm_annular_set NX S a rho (@value R X NX S a rho).
Proof. exact: projT2 (cid (@norm_annular_set_exists R X NX S a rho)). Qed.
End NormAnnularSet.
