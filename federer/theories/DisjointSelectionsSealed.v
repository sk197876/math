(** Sealed disjoint selections for Federer (1969), 2.2.4, p. 62 The measure
    argument sees only membership and disjointness, not the chosen well
    ordering or transfinite recursion. Source context and the interleaving
    proof variant: DisjointSelectionsConstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals.
From Federer Require Import SequenceSpace DisjointSelectionsUP DisjointSelectionsConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope card_scope.
Module Type DisjointSelectionsSignature.
(** Source for [value]: abstract pair of selections in the
    proof of Federer 2.2.4, p. 62. *)
Parameter value : forall (R : realType) (I T : choiceType) (E : I -> set T) (i0 : I),
  (@setT I) #<= (@setT (positive_sequence_space R)) ->
  (forall i, (@setT (positive_sequence_space R)) #<= E i) -> (I -> T) * (I -> T).
(** Source for [laws]: membership and separated images required by Federer
    2.2.4, p. 62 *)
Parameter laws : forall (R : realType) (I T : choiceType) (E : I -> set T) (i0 : I)
  (hI : (@setT I) #<= (@setT (positive_sequence_space R)))
  (hE : forall i, (@setT (positive_sequence_space R)) #<= E i),
  is_disjoint_family_selection E (@value R I T E i0 hI hE).1 (@value R I T E i0 hI hE).2.
End DisjointSelectionsSignature.
Module DisjointSelections : DisjointSelectionsSignature.
(** Source for [value]: private choice from the proved existence
    of disjoint selections for Federer 2.2.4, p. 62. *)
Definition value (R : realType) (I T : choiceType) (E : I -> set T) (i0 : I)
  (hI : (@setT I) #<= (@setT (positive_sequence_space R)))
  (hE : forall i, (@setT (positive_sequence_space R)) #<= E i) : (I -> T) * (I -> T) :=
  let e := cid (@full_cardinality_disjoint_selections_exist R I T E i0 hI hE) in
  (projT1 e, projT1 (cid (projT2 e))).
(** Source for [laws]: the constructed witnesses satisfy the
    abstract selection laws used in Federer 2.2.4, p. 62. *)
Lemma laws (R : realType) (I T : choiceType) (E : I -> set T) (i0 : I)
  (hI : (@setT I) #<= (@setT (positive_sequence_space R)))
  (hE : forall i, (@setT (positive_sequence_space R)) #<= E i) :
  is_disjoint_family_selection E (@value R I T E i0 hI hE).1 (@value R I T E i0 hI hE).2.
Proof. exact: projT2 (cid (projT2 (cid (@full_cardinality_disjoint_selections_exist R I T E i0 hI hE)))). Qed.
End DisjointSelections.
