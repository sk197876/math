(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: the Rees subring consists of finite
    polynomials whose degree-n coefficient lies in the
    original nth ideal power. Source: Bourbaki,
    Commutative Algebra (1972), Chapter III, section 3,
    no. 1, Lemma 1, p. 197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealPowersSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_rees_subring]: independent coefficient
    membership laws for the original Rees subring in
    the cited Lemma 1, supporting 3.4.8(5), p. 328. *)
Definition is_rees_subring (A B:comNzRingType) (coefficient:B->nat->A)
    (I:set A) (S:set B):Prop:=
  forall P:B,S P <->forall n,@CommutativeIdealPowers.value A I n (coefficient P n).
