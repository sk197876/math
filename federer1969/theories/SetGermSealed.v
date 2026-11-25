(** Federer (1969), 3.4.5, pp. 319–320: the actual
    Boolean operations on set germs, hidden behind representative laws. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SetGermsSignature.
(** Source for [join]: union of set germs, 3.4.5, pp. 319–320. *)
Parameter join:forall (X:topologicalType) (a:X),set_germ_space a->set_germ_space a->set_germ_space a.
(** Source for [meet]: intersection of set germs, 3.4.5, pp. 319–320. *)
Parameter meet:forall (X:topologicalType) (a:X),set_germ_space a->set_germ_space a->set_germ_space a.
(** Source for [neg]: complement of set germs, 3.4.5, pp. 319–320. *)
Parameter neg:forall (X:topologicalType) (a:X),set_germ_space a->set_germ_space a.
(** Source for [laws]: original representative laws for the
    induced Boolean operations, 3.4.5, pp. 319–320. *)
Parameter laws:forall (X:topologicalType) (a:X),
  is_set_germ_operations (@join X a) (@meet X a) (@neg X a).
End SetGermsSignature.
Module SetGerms:SetGermsSignature.
(** Source for [join]: private union witness from the
    proved existence theorem, 3.4.5, pp. 319–320. *)
Definition join (X:topologicalType) (a:X):=
  projT1 (cid (@set_germ_operations_exists X a)).
(** Source for [meet]: private intersection witness from the
    same existence theorem, 3.4.5, pp. 319–320. *)
Definition meet (X:topologicalType) (a:X):=
  projT1 (cid (projT2 (cid (@set_germ_operations_exists X a)))).
(** Source for [neg]: private complement witness from the
    same existence theorem, 3.4.5, pp. 319–320. *)
Definition neg (X:topologicalType) (a:X):=
  projT1 (cid (projT2 (cid (projT2 (cid (@set_germ_operations_exists X a)))))).
(** Source for [laws]: each selected operation satisfies its
    independent representative law, 3.4.5, pp. 319–320. *)
Lemma laws (X:topologicalType) (a:X):
  is_set_germ_operations (@join X a) (@meet X a) (@neg X a).
Proof.
exact:(projT2 (cid (projT2 (cid (projT2 (cid (@set_germ_operations_exists X a))))))).
Qed.
End SetGerms.
