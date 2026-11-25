(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: the kernel of a homomorphism
    into a field is a proper prime ideal.
    Reuse the project's ideal-preimage theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP NoetherianRingSurjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [commutative_ring_kernel_ideal]: the
    original canonical-map kernel in 3.4.8(8),
    p. 329, is an ideal. Apply the
    already proved ideal-preimage theorem. *)
Lemma commutative_ring_kernel_ideal (A C:comNzRingType) (f:{rmorphism A->C}):
  is_commutative_ideal (fun a:A=>f a = 0).
Proof.
have hZero:is_commutative_ideal (fun c:C=>c = 0).
  constructor.
  - by [].
  - move=>x y -> ->;exact:add0r.
  - move=>x ->;exact:oppr0.
  - move=>x y ->;exact:mulr0.
exact:(commutative_ideal_ring_preimage f hZero).
Qed.

(** Source for [commutative_field_kernel_prime]: the
    kernel is prime when the original target
    is a field, supporting minimal polynomials
    in 3.4.8(8), pp. 329–330. *)
Theorem commutative_field_kernel_prime (A:comNzRingType) (L:fieldType)
  (f:{rmorphism A->L}):is_prime_commutative_ideal (fun a:A=>f a = 0).
Proof.
split;first exact:commutative_ring_kernel_ideal.
split.
- rewrite rmorph1;by apply/eqP;exact:oner_neq0.
- move=>x y;rewrite rmorphM=>/eqP;rewrite mulf_eq0.
  by move/orP=>[/eqP hX|/eqP hY];[left|right].
Qed.
