(** Private countable rational hull supporting Federer (1969), 2.3.8, p. 78:
    a countable set generates a separable real linear subspace after taking
    closure. Source context: ClosedLinearSpanUP.v. Iterated rational
    operations construct a witness; no downstream interface exposes its
    recursion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [countable_hull_union]: set-theoretic support for
    the countable rational hull in Federer 2.3.8, p. 78. *)
Lemma countable_hull_union (T : Type) (A B : set T) :
  countable A -> countable B -> countable (A `|` B).
Proof.
move=> ha hb.
have he : A `|` B = \bigcup_(b in @setT bool) (if b then A else B).
  apply/seteqP; split.
  - move=> x [hx|hx]; [by exists true|by exists false].
  - by move=> x [[] _ hx]; [left|right].
rewrite he; apply: bigcup_countable; first exact: countableP.
by move=> [] _.
Qed.

Section Hull.
Variable R : realType.
Variable V : lmodType R.
Variable D : set V.

(** Source for [rational_hull_level]: private finite operation
    levels for the separable-span argument supporting Federer
    2.3.8, p. 78; rational sums and multiples suffice densely. *)
Fixpoint rational_hull_level n : set V :=
  if n is k.+1 then
    let A := rational_hull_level k in
    (A `|` ((fun p : V*V => p.1+p.2) @` (A `*` A))) `|`
      ((fun p : rat*V => (ratr p.1 : R) *: p.2) @` (setT `*` A))
  else [set 0] `|` D.

(** Source for [rational_hull]: private countable union of the
    operation levels for Federer 2.3.8, p. 78. *)
Definition rational_hull := \bigcup_n rational_hull_level n.

(** Source for [rational_hull_level_step]: supporting inclusion
    of consecutive levels in the span argument for Federer 2.3.8, p. 78. *)
Lemma rational_hull_level_step n : rational_hull_level n `<=` rational_hull_level n.+1.
Proof. move=> x hx; left; by left. Qed.

(** Source for [rational_hull_level_mono]: supporting nesting
    of the countable hull levels for Federer 2.3.8, p. 78. *)
Lemma rational_hull_level_mono n m : (n <= m)%N ->
  rational_hull_level n `<=` rational_hull_level m.
Proof.
elim: m=> [|m ih] in n *.
- by rewrite leqn0=> /eqP ->.
- rewrite leq_eqVlt=> /orP [/eqP ->|hnm] // x hx.
  rewrite ltnS in hnm.
  exact: rational_hull_level_step (ih n hnm x hx).
Qed.

(** Source for [rational_hull_countable]: countability of the rational hull
    used in the separable-span reduction in Federer 2.3.8, p. 78 *)
Lemma rational_hull_countable : countable D -> countable rational_hull.
Proof.
move=> hd; apply: bigcup_countable; first exact: countableP.
move=> n _; elim: n=> [|n ih] /=.
- apply: countable_hull_union=> //; exact: countable1.
- apply: countable_hull_union.
  + apply: countable_hull_union=> //.
    apply: sub_countable (card_image_le _ _) _; exact (@countableX V V _ _ ih ih).
  + apply: sub_countable (card_image_le _ _) _.
    apply: countableX=> //; exact: countableP.
Qed.

(** Source for [rational_hull_contains]: generators belong to
    the rational hull supporting Federer 2.3.8, p. 78. *)
Lemma rational_hull_contains : D `<=` rational_hull.
Proof. move=> x hx; exists 0%N=> //; by right. Qed.

(** Source for [rational_hull_zero]: zero belongs to the
    rational hull supporting Federer 2.3.8, p. 78. *)
Lemma rational_hull_zero : rational_hull 0.
Proof. exists 0%N=> //; left; by []. Qed.

(** Source for [rational_hull_add]: additive stability of the
    dense countable set supporting Federer 2.3.8, p. 78. *)
Lemma rational_hull_add x y : rational_hull x -> rational_hull y -> rational_hull (x+y).
Proof.
move=> [n _ hx] [m _ hy]; exists (maxn n m).+1=> //.
left; right; exists (x,y)=> //; split.
- exact (@rational_hull_level_mono n (maxn n m) (leq_maxl n m) x hx).
- exact (@rational_hull_level_mono m (maxn n m) (leq_maxr n m) y hy).
Qed.

(** Source for [rational_hull_scale]: rational-scalar stability
    of the dense countable hull supporting Federer 2.3.8, p. 78. *)
Lemma rational_hull_scale (q : rat) x : rational_hull x ->
  rational_hull ((ratr q : R) *: x).
Proof. move=> [n _ hx]; exists n.+1=> //; right; exists (q,x)=> //; by split. Qed.
End Hull.
