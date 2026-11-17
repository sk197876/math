(** Supporting algebra for Federer (1969), 3.4.8(5), p. 328:
    control an original scalar functional on coefficient ideal
    powers without treating the functional as multiplicative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import RingScalarRestriction CommutativeIdealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [linear_multiplier_locus]: supporting coefficient
    filtration for Federer 3.4.8(5), p. 328. Require every original
    ring multiple to be sent into the specified original scalar ideal.
    The definition assumes no closure or power law. *)
Definition linear_multiplier_locus (A C:comNzRingType) (phi:{rmorphism A->C})
    (L:{linear [the lmodType A of ring_restricted_space phi C^o]->A^o})
    (I:set A):set C:=fun z=>forall c:C,I (L (c*z)).

(** Source for [linear_multiplier_locus_is_ideal]: supporting original
    scalar functional filtration for Federer 3.4.8(5), p. 328.
    Additivity suffices for the multiplier locus to be a C-ideal;
    no multiplicativity of the functional is asserted. *)
Theorem linear_multiplier_locus_is_ideal (A C:comNzRingType) (phi:{rmorphism A->C})
    (L:{linear [the lmodType A of ring_restricted_space phi C^o]->A^o})
    (I:set A):is_commutative_ideal I ->is_commutative_ideal (linear_multiplier_locus L I).
Proof.
move=>hI;constructor.
- move=>c;rewrite mulr0 linear0;exact:commutative_ideal_zero hI.
- move=>x y hX hY c;rewrite mulrDr linearD.
  exact:(@commutative_ideal_add A I hI _ _ (hX c) (hY c)).
- move=>x hX c;rewrite mulrN linearN.
  exact:(@commutative_ideal_opp A I hI _ (hX c)).
- move=>x y hY c;rewrite mulrA;exact:hY (c*x).
Qed.
