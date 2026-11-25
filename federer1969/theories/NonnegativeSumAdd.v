(** Federer (1969), 2.1.1(2)-(3), p. 52: additivity of nonnegative
    summation. The proof below passes to finite subsums in both summands and
    combines their indexing sets by union. editions: NonnegativeSumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum_add_bound]: Federer 2.1.1(2),
    p. 52; supporting passage from finite-subsum bounds after adding
    a fixed nonnegative scalar to the corresponding bound on the sum. *)
Lemma nonnegative_sum_add_bound (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) y c : 0 <= y ->
  (forall (B : {fset I}), (forall x, x \in B -> A x) ->
    (\sum_(x <- B) f x) + y <= c) -> nonnegative_sum A f + y <= c.
Proof.
case: y=> [r| |] hy hb; last by [].
- rewrite -leeBrDr //; apply: nonnegative_sum_least=> B hB.
  rewrite leeBrDr //; exact: hb.
- have h0 : (forall x : I, x \in fset0 -> A x) by move=> x; rewrite in_fset0.
  have hc := hb fset0 h0; rewrite big_seq_fset0 add0e in hc.
  exact: le_trans (leey _) hc.
Qed.

(** Source for [nonnegative_sum_add]: Federer 2.1.1(2), p. 52 and sentence
    after (4); nonnegative summation is additive on arbitrary sets. *)
Theorem nonnegative_sum_add (R : realType) (I : choiceType)
    (A : set I) (f g : I -> \bar R) :
  (forall x, A x -> 0 <= f x) -> (forall x, A x -> 0 <= g x) ->
  nonnegative_sum A (fun x => f x + g x) = nonnegative_sum A f + nonnegative_sum A g.
Proof.
move=> hf hg; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: nonnegative_sum_least=> B hB; rewrite big_split /=.
  apply: leeD; exact: nonnegative_sum_upper hB.
- apply: nonnegative_sum_add_bound; first exact: nonnegative_sum_nonnegative.
  move=> B hB; rewrite addeC; apply: nonnegative_sum_add_bound.
  + rewrite big_seq; apply: sume_ge0=> x hx; exact: hf (hB x hx).
  + move=> C hC; pose D := (B `|` C)%fset.
    have hD : forall x, x \in D -> A x.
      move=> x /fsetUP[hx|hx]; [exact: hB | exact: hC].
    have hBD : (\sum_(x <- B) f x) <= \sum_(x <- D) f x.
      apply: lee_sum_nneg_subfset.
      * move=> x hx; by rewrite /D in_fsetU hx.
      * move=> x; rewrite inE => /andP[_ hx] _; exact: hf (hD x hx).
    have hCD : (\sum_(x <- C) g x) <= \sum_(x <- D) g x.
      apply: lee_sum_nneg_subfset.
      * move=> x hx; by rewrite /D in_fsetU hx orbT.
      * move=> x; rewrite inE => /andP[_ hx] _; exact: hg (hD x hx).
    apply: le_trans (leeD hCD hBD) _.
    rewrite addeC -big_split /=; exact: nonnegative_sum_upper hD.
Qed.
