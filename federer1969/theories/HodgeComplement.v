(** Federer (1969), 1.7.8, p. 34: distinct increasing index sets have
    distinct complements. Supporting combinatorics for the Hodge pairing
    formula *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ExteriorIndices TopComplements.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [top_complement_injective]: Federer 1.7.8,
    p. 34, supporting injectivity of the complement operation
    on index sets of a fixed degree. *)
Lemma top_complement_injective n p : injective (@top_complement n p).
Proof.
move=> lambda mu h.
have hh : mu == lambda.
  rewrite -(top_complement_shared_right lambda mu) h.
  exact: top_complement_permutation.
by apply/eqP; rewrite eq_sym.
Qed.
