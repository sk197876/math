(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: finite polynomial coefficient ideals used in
    an expanded ideal-closure argument. Compare Bourbaki,
    Elements of Mathematics: Commutative Algebra (1972),
    Chapter III, section 2, no. 10, Corollary 1, p. 184.
    The coefficient-image laws precede existence and imply
    no Noetherian or closure conclusion. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_truncated_polynomial_leading_family]:
    the bounded coefficient ideals in the elementary
    coefficient proof of Hilbert's theorem; Bourbaki (1972),
    Chapter III, section 2, no. 10, Corollary 1, p. 184.
    This supports the expanded algebra for 3.4.8(5), p. 328.
    Degree d means all coefficients above d vanish; the
    coefficient at d may be zero. *)
Definition is_truncated_polynomial_leading_family (A B:comNzRingType)
    (coefficient:B->nat->A) (I:set B) (L:nat->set A):Prop:=
  forall d a,L d a <->exists P:B,I P /\
    (forall i,(d<i)%N ->coefficient P i = 0) /\coefficient P d = a.
