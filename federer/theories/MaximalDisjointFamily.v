(** Public maximal-family interface supporting Federer (1969), 2.5.10, p.
    101. Source context: MaximalDisjointFamilyUP.v. Downstream arguments use
    only the opaque family's proved laws. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import MaximalDisjointFamilyUP MaximalDisjointFamilySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [maximal_disjoint_family]: public witness for the
    family chosen in Federer 2.5.10, p. 101. *)
Definition maximal_disjoint_family (X : choiceType) (P : set (set X)) := @MaximalDisjointFamily.value X P.

(** Source for [maximal_disjoint_family_specification]: abstract
    laws of the family in Federer 2.5.10, p. 101. *)
Lemma maximal_disjoint_family_specification (X : choiceType) (P : set (set X)) :
  is_maximal_disjoint_family P (@maximal_disjoint_family X P).
Proof. exact: MaximalDisjointFamily.laws. Qed.
