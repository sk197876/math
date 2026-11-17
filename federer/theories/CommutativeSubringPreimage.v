(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 329: pull a subring back through
    an original ring map when applying the
    existing least-subring property. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeSubringUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [commutative_subring_ring_preimage]: the
    subring test used in the original
    coordinate-generator induction of 3.4.8(8), p. 329.
    The original homomorphism laws prove closure. *)
Lemma commutative_subring_ring_preimage (A C:comNzRingType) (f:{rmorphism A->C}) (S:set C):
  is_commutative_subring S ->is_commutative_subring (f @^-1` S).
Proof.
move=>hS;constructor.
- change (S (f 0));rewrite rmorph0;exact:commutative_subring_zero hS.
- change (S (f 1));rewrite rmorph1;exact:commutative_subring_one hS.
- move=>a b hA hB;change (S (f (a+b)));rewrite rmorphD.
  exact:(@commutative_subring_add C S hS (f a) (f b) hA hB).
- move=>a hA;change (S (f (-a)));rewrite rmorphN.
  exact:(@commutative_subring_opp C S hS (f a) hA).
- move=>a b hA hB;change (S (f (a*b)));rewrite rmorphM.
  exact:(@commutative_subring_multiply C S hS (f a) (f b) hA hB).
Qed.
