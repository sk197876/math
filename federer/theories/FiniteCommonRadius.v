(** General finite-family reasoning supporting Federer (1969),
    3.1.1, p. 211: choose one positive radius for finitely many
    partial-derivative bounds. The empty family is included. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_common_radius]: supporting finite-minimum
    step in the choice of delta for all coordinate partial derivatives
    in Federer 3.1.1, p. 211. Only existence is exposed; a concrete
    witness is built inside the opaque proof by finite induction. *)
Lemma finite_common_radius (R : realType) (I : finType) (X : Type)
    (w : X -> R) (P : I -> X -> Prop) :
  (forall i, exists d : R, 0 < d /\ forall x, w x < d -> P i x) ->
  exists d : R, 0 < d /\ forall i x, w x < d -> P i x.
Proof.
move=> hp.
have hs : forall s : seq I, exists d : R, 0 < d /\
    forall i, i \in s -> forall x, w x < d -> P i x.
  elim=> [|i s [d [hd hb]]].
  - exists 1; split; first exact: ltr01.
    by move=> i; rewrite in_nil.
  - have [r [hr hi]] := hp i.
    exists (Num.min r d); split; first by rewrite lt_min hr hd.
    move=> j; rewrite in_cons=> /orP [/eqP ->|hj] x hx.
    + apply: hi; apply: lt_le_trans hx _; by rewrite ge_min lexx.
    + apply: (hb j hj x); apply: lt_le_trans hx _; by rewrite ge_min lexx orbT.
have [d [hd hb]] := hs (enum I).
exists d; split=> // i x hx; apply: (hb i _ x hx).
by rewrite mem_enum.
Qed.
