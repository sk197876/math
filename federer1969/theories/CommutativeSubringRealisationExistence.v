(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: original subring laws give a ring carrier
    satisfying the independent inclusion laws. This is an
    existence proof for the Rees-ring interface; Bourbaki,
    Commutative Algebra (1972), Chapter III, section 3,
    no. 1, Lemma 1, p. 197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeSubringUP CommutativeSubringRealisationUP
  CommutativeSubringCarrier.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [commutative_subring_realisation_exists]: the
    original subring has an exact ring realisation with
    injective inclusion, supporting the cited Rees-ring Lemma 1
    and the expanded algebra for 3.4.8(5), p. 328. *)
Theorem commutative_subring_realisation_exists (A:comNzRingType) (S:set A):
  is_commutative_subring S ->exists C:comNzRingType,
    exists inclusion:{rmorphism C->A},is_commutative_subring_realisation S inclusion.
Proof.
move=>hS.
exists (@subring_member_ring A S hS),(@subring_member_inclusion A S hS).
exact:(@subring_member_realisation A S hS).
Qed.
