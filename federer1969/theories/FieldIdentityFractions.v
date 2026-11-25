(** Federer (1969), 3.4.8(10), p. 331:
    apply the original fraction representation theorem
    inside the fraction field itself when
    representing an inverse. A field is
    its own fraction field by the
    independent fraction laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import FractionFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [field_identity_fraction_laws]: treating
    the original inverse in L as
    an element of its own fraction
    field, supporting the denominator argument
    of 3.4.8(10), p. 331. *)
Lemma field_identity_fraction_laws (L:fieldType):
  is_commutative_fraction_field (GRing.RMorphism.clone L L idfun _).
Proof.
constructor;first by move=>x y.
move=>x;exists x,1;split.
- by apply/eqP;exact:oner_neq0.
- exact:esym (divr1 x).
Qed.
