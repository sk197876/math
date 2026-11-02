(** General set-theoretic background for Federer (1969), 2.2.6, p. 63, last
    paragraph: a countable product of sequence spaces is reindexed by a
    bijection between pairs of natural indices and natural indices. The
    local statement specifies inverse laws; countable cardinal arithmetic
    supplies their existence. No particular pairing algorithm is exposed. *)
From mathcomp Require Import all_boot boolp classical_sets functions cardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [natural_pairing_exists]: supporting set-theoretic existence
    for Federer 2.2.6, p. 63: natural pairs and natural numbers admit
    mutually inverse enumerations. Zero-based indices encode the positive
    indices in the book. *)
Lemma natural_pairing_exists : exists (encode : nat * nat -> nat) (decode : nat -> nat * nat),
  cancel encode decode /\ cancel decode encode.
Proof.
have [e [_ he hs]] := elimT card_set_bijP card_nat2.
have hex n : exists p, e p = n.
  have [p _ hp] := hs n Logic.I; by exists p.
pose d n := projT1 (cid (hex n)).
have hd n : e (d n) = n by exact: projT2 (cid (hex n)).
exists e, d; split=> // p; apply: he; try by rewrite inE.
exact: hd.
Qed.
