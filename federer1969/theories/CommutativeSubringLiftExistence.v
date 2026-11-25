(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: the actual coefficient map lifts to the
    abstract Rees-ring carrier. Source: Bourbaki,
    Commutative Algebra (1972), Chapter III, section 3,
    no. 1, Lemma 1, p. 197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeSubringRealisationUP CommutativeSubringLiftConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [commutative_subring_ring_lift_exists]:
    an original homomorphism with image in the subring
    has an actual ring homomorphism lift through its
    specified inclusion, supporting the cited Lemma 1.
    The selected lift remains a local existence witness. *)
Theorem commutative_subring_ring_lift_exists (A B C:comNzRingType)
    (S:set B) (inclusion:{rmorphism C->B})
    (hC:is_commutative_subring_realisation S inclusion) (phi:{rmorphism A->B}):
  (forall a:A,S (phi a)) ->exists psi:{rmorphism A->C},
    forall a:A,inclusion (psi a)=phi a.
Proof.
move=>hImage;exists (@subring_lift_ring_map A B C S inclusion hC phi hImage).
move=>a;exact:(@subring_lift_function_equation A B C S inclusion hC phi hImage a).
Qed.
