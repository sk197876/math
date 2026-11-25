(** Federer (1969), 2.10.48, p. 206: the supremum of the finite compact
    masses is approached by an increasing compact sequence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP FiniteCompactMassUP FiniteCompactMassConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Module Type FiniteCompactMassSignature.
(** Source for [sequence]: abstract increasing compact choice in
    2.10.48, p. 206, under a finite bound for compact masses. *)
Parameter sequence : forall (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (S : set X) (M : R), is_measure mu ->
    (forall C, compact C -> C `<=` S -> mu C< +oo -> mu C<=M%:E) -> nat -> set X.
(** Source for [laws]: the choice satisfies precisely the sequence
    laws needed by 2.10.48, p. 206. *)
Parameter laws : forall (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (S : set X) (M : R) (hm : is_measure mu)
    (hb : forall C, compact C -> C `<=` S -> mu C< +oo -> mu C<=M%:E),
  is_finite_compact_mass_sequence mu S (@sequence R X mu S M hm hb).
End FiniteCompactMassSignature.

Module FiniteCompactMass : FiniteCompactMassSignature.
(** Source for [sequence]: private witness selection from the proved
    existence theorem for 2.10.48, p. 206. *)
Definition sequence (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (S : set X) (M : R) (hm : is_measure mu)
    (hb : forall C, compact C -> C `<=` S -> mu C< +oo -> mu C<=M%:E) :=
  projT1 (cid (@finite_compact_mass_sequence_exists R X mu S M hm hb)).
(** Source for [laws]: proved laws of the opaque sequence used in
    2.10.48, p. 206; no choice equations escape the seal. *)
Lemma laws (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (S : set X) (M : R) (hm : is_measure mu)
    (hb : forall C, compact C -> C `<=` S -> mu C< +oo -> mu C<=M%:E) :
  is_finite_compact_mass_sequence mu S (@sequence R X mu S M hm hb).
Proof. exact: projT2 (cid (@finite_compact_mass_sequence_exists R X mu S M hm hb)). Qed.
End FiniteCompactMass.
