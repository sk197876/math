(** General topology of the real line supporting Federer (1969), 2.5.16, p.
    109: a property holding near x from the left holds on an interval {t : u
    < t < x}, and a property holding near x from the right holds on an
    interval {t : x < t < u}. The one sided filters are those of the
    analysis library. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology normedtype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [at_left_threshold]: supporting extraction of a left
    threshold from a property near x from the left, used for the
    limits as t tends to x from the left in Federer 2.5.16, p. 109. *)
Lemma at_left_threshold (R : realType) (x : R) (P : set R) :
  (\forall t \near x^'-, P t) -> exists u, u < x /\ forall t, u < t -> t < x -> P t.
Proof.
rewrite near_withinE=> /nbhs_ballP [d hd hsub].
exists (x - d); split; first by rewrite ltrBlDr ltrDl.
move=> t hut htx; apply: (hsub t); last exact: htx.
rewrite /ball /= gtr0_norm ?subr_gt0 // ltrBlDl.
by move: hut; rewrite ltrBlDr addrC.
Qed.

(** Source for [at_right_threshold]: supporting extraction of a right
    threshold from a property near x from the right, used for the
    limits as t tends to x from the right in Federer 2.5.16, p. 109. *)
Lemma at_right_threshold (R : realType) (x : R) (P : set R) :
  (\forall t \near x^'+, P t) -> exists u, x < u /\ forall t, x < t -> t < u -> P t.
Proof.
rewrite near_withinE=> /nbhs_ballP [d hd hsub].
exists (x + d); split; first by rewrite ltrDl.
move=> t hxt htu; apply: (hsub t); last exact: hxt.
rewrite /ball /= ltr0_norm ?subr_lt0 // opprB ltrBlDl.
by move: htu; rewrite addrC.
Qed.
