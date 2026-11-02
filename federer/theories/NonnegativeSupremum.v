(** Federer (1969), 1.7.7, p. 34: elementary supremum step in the projection
    formulas. This order-theoretic helper is not a separately numbered book
    claim. It also covers the empty set, whose real supremum in the library
    convention is zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [nonnegative_supremum_attained_if_nonzero]: Federer
    1.7.7, p. 34, supporting passage from an upper bound and nonzero
    attainment to the supremum, allowing the zero/empty case. *)
Theorem nonnegative_supremum_attained_if_nonzero (R : realType)
    (S : set R) L (hL : 0 <= L)
    (hS : forall r, S r -> 0 <= r /\ r <= L)
    (hA : L != 0 -> S L) : L = sup S.
Proof.
have hu : ubound S L by move=> r hr; exact: (hS r hr).2.
have [he|he] := pselect (exists r, S r).
- have [r hr] := he.
  apply/eqP; rewrite eq_le; apply/andP; split.
  + have [->|hn] := eqVneq L 0.
    * exact: le_trans (hS r hr).1 (ub_le_sup (ex_intro _ L hu) hr).
    * apply: ub_le_sup (hA hn); by exists L.
  + apply: ge_sup hu; exact he.
- have hs : S = set0 by apply/seteqP; split=> r // hr; exfalso; apply: he; exists r.
  have [->|hn] := eqVneq L 0; first by rewrite hs sup0.
  exfalso; apply: he; exists L; exact: hA.
Qed.
