(** Federer (1969), 2.6.1, pp. 114–115, and 2.6.2, p. 116: replacing a
    countable rectangle family by a sequence, filling missing positions with
    empty rectangles. This is supporting set theory, not a separate printed
    claim. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_default_enumeration]: supporting
    countable-family enumeration for Federer 2.6.2, p. 116.
    A supplied default fills unused indices; the empty family
    becomes the constant default sequence. Every original member occurs. *)
Lemma countable_default_enumeration (J : choiceType) (D : set J) (d : J) :
  countable D -> exists u : nat -> J,
    (forall n, D (u n) \/ u n = d) /\ (forall j, D j -> exists n, u n = j).
Proof.
move=> /countable_injP[g hg].
pose E n := [set j | D j /\ g j = n].
pose u n := if pselect (exists j, E n j) is left h then projT1 (cid h) else d.
have hu n : E n (u n) \/ (u n = d /\ ~ exists j, E n j).
  rewrite /u; case: pselect=> [h|hn]; first by left; exact: projT2 (cid h).
  right; by split.
exists u; split.
- move=> n; have [[hd _]|[he _]] := hu n; [by left|by right].
- move=> j hj; exists (g j); have [[hd he]|[_ hn]] := hu (g j).
  + apply: hg; [exact: mem_set hd|exact: mem_set hj|exact he].
  + exfalso; apply: hn; exists j; by split.
Qed.
