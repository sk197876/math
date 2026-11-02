(** Opaque maximal-family interface supporting Federer (1969), 2.5.10, p.
    101 Source context and eligibility convention:
    MaximalDisjointFamilyUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import MaximalDisjointFamilyUP MaximalDisjointFamilyConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type MaximalDisjointFamilySignature.
(** Source for [value]: abstract maximal family supporting
    Federer 2.5.10, p. 101. *)
Parameter value : forall X : choiceType, set (set X) -> set (set X).
(** Source for [laws]: eligibility, disjointness and maximality
    laws for Federer 2.5.10, p. 101. *)
Parameter laws : forall (X : choiceType) (P : set (set X)),
  is_maximal_disjoint_family P (@value X P).
End MaximalDisjointFamilySignature.
Module MaximalDisjointFamily : MaximalDisjointFamilySignature.
(** Source for [value]: private witness selection from the proved
    existence supporting Federer 2.5.10, p. 101. *)
Definition value (X : choiceType) (P : set (set X)) :=
  projT1 (cid (@maximal_disjoint_family_exists X P)).
(** Source for [laws]: the selected family satisfies the abstract
    specification supporting Federer 2.5.10, p. 101. *)
Lemma laws (X : choiceType) (P : set (set X)) : is_maximal_disjoint_family P (@value X P).
Proof. exact: projT2 (cid (@maximal_disjoint_family_exists X P)). Qed.
End MaximalDisjointFamily.
