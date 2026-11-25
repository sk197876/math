(** Federer (1969), 2.3.9, p. 79: summable successive distances control all
    later distances by the series tail. This supporting metric argument
    retains the book's proof. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSequenceTail NonnegativeSequenceTailStep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [summable_metric_increment_bound]: supporting
    telescoping triangle estimate for Federer 2.3.9, p. 79,
    last paragraph. For an arbitrary metric space, the distance
    between two terms is bounded by the earlier series tail. *)
Lemma summable_metric_increment_bound (R : realType) (T : metricType R)
    (u : nat -> T) (a : nat -> \bar R) j :
  (forall n, 0 <= a n) ->
  (forall n, (j <= n)%N -> (mdist (u n.+1) (u n))%:E <= a n) ->
  forall m n, (j <= m)%N -> (m <= n)%N ->
    (mdist (u n) (u m))%:E <= nonnegative_sequence_tail a m.
Proof.
move=> ha hinc m n hjm hmn.
have ht k : (mdist (u (m+k)%N) (u m))%:E + nonnegative_sequence_tail a (m+k)%N <=
    nonnegative_sequence_tail a m.
  elim: k=> [|k ih].
  - by rewrite addn0 mdistxx add0e.
  rewrite addnS.
  have hstep := hinc (m+k)%N (leq_trans hjm (leq_addr _ _)).
  have htri : (mdist (u (m+k)%N.+1) (u m))%:E <=
      a (m+k)%N + (mdist (u (m+k)%N) (u m))%:E.
    apply: le_trans _ (leeD hstep (lexx _)).
    by rewrite -EFinD lee_fin; exact: metric_triangle.
  apply: le_trans (leeD htri (lexx _)) _.
  rewrite [a (m+k)%N + _]addeC -addeA -nonnegative_sequence_tail_step //.
have hh := ht (n-m)%N; rewrite subnKC // in hh.
apply: le_trans _ hh.
rewrite -{1}(adde0 (mdist (u n) (u m))%:E).
exact: leeD (lexx _) (nonnegative_sequence_tail_nonnegative a n).
Qed.
