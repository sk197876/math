(** Federer (1969), 3.4.7, p. 325: units,
    irreducible elements and prime factorization in the analytic
    germ ring. These algebraic definitions assert no existence
    or uniqueness theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_commutative_unit]: the multiplier
    Q is a unit when Q(0) is nonzero, 3.4.7,
    p. 325. A unit has a multiplicative inverse. *)
Definition is_commutative_unit (A:comNzRingType) (x:A):Prop:=
  exists y:A,y*x = 1.

(** Source for [commutative_divides]: divisibility used
    in the factorization argument of 3.4.7, p. 325. *)
Definition commutative_divides (A:comNzRingType) (x y:A):Prop:=
  exists z:A,y = z*x.

(** Source for [is_commutative_irreducible]: a nonzero
    nonunit has no product decomposition into two nonunits,
    supporting prime factorization in 3.4.7, p. 325. *)
Definition is_commutative_irreducible (A:comNzRingType) (x:A):Prop:=
  x<>0 /\~is_commutative_unit x /\
  forall y z,x = y*z ->is_commutative_unit y \/is_commutative_unit z.

(** Source for [is_commutative_prime_element]: a nonzero
    nonunit divides a product only if it divides one
    factor, supporting 3.4.7, p. 325. *)
Definition is_commutative_prime_element (A:comNzRingType) (x:A):Prop:=
  x<>0 /\~is_commutative_unit x /\
  forall y z,commutative_divides x (y*z) ->
    commutative_divides x y \/commutative_divides x z.

(** Source for [is_unique_factorization_commutative_domain]:
    the unique factorization domain assertion of 3.4.7,
    p. 325, specified by the equivalent prime-factorization
    property together with absence of zero divisors.
    Uniqueness up to units and permutation is a separate
    consequence to be proved. *)
Definition is_unique_factorization_commutative_domain (A:comNzRingType):Prop:=
  (forall x y:A,x*y = 0 ->x = 0 \/y = 0) /\
  forall x:A,x<>0 ->exists u:A,exists F:seq A,
    is_commutative_unit u /\
    (forall p,p \in F ->is_commutative_prime_element p) /\
    x = u*\prod_(p<-F) p.
