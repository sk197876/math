(** Federer (1969), 3.4.5, p. 320: the
    prime-product condition corresponding exactly to the literal
    irreducibility union test. Propriety is kept separate so
    the printed empty-germ edge remains explicit. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import CommutativeIdealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [has_prime_ideal_product_property]: an
    actual ideal contains a product only when it contains
    a factor, the algebraic condition used in 3.4.5,
    p. 320. Unlike proper primeness, this condition
    permits the whole ring and matches the empty germ. *)
Definition has_prime_ideal_product_property (A:comNzRingType) (I:set A):=
  is_commutative_ideal I /\forall x y,I (x*y) ->I x \/I y.
