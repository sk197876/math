(** Federer (1969), 2.3.3, p. 76: partial sums stay nonnegative and below
    the target. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import GreedyScalarExpansionUP NonnegativeSum NonnegativeSumNatPrefix NonnegativeSeriesParity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [greedy_scalar_term_nonnegative]: supporting
    nonnegative summands in Federer 2.3.3, p. 76. *)
Lemma greedy_scalar_term_nonnegative (R : realType) (r : nat -> R) (t : \bar R) s :
  (forall n, (0 <= r n)%R) -> forall n, (0 <= greedy_scalar_term r t s n)%R.
Proof. move=> hr n; rewrite /greedy_scalar_term; by case: ifP. Qed.

(** Source for [greedy_scalar_bounds]: direct inductive partial-sum bound
    used in Federer 2.3.3, p. 76. *)
Lemma greedy_scalar_bounds (R : realType) (r : nat -> R) (t : \bar R) s :
  (forall n, (0 <= r n)%R) -> 0 <= t -> is_greedy_scalar_expansion r t s ->
  forall n, (0 <= s n)%R /\ (s n)%:E <= t.
Proof.
move=> hr ht hs; elim=> [|n [h0 hn]].
- by rewrite (greedy_scalar_initial hs); split.
- rewrite (greedy_scalar_step hs); case: ifP=> hstep; split=> //.
  exact: addr_ge0 h0 (hr n).
Qed.

(** Source for [greedy_scalar_prefix_sum]: supporting equality of the
    abstract partial sum and the finite selected-weight sum in Federer
    2.3.3, p. 76 *)
Lemma greedy_scalar_prefix_sum (R : realType) (r : nat -> R) (t : \bar R) s :
  (forall n, (0 <= r n)%R) -> is_greedy_scalar_expansion r t s -> forall N,
  nonnegative_sum [set n | (n < N)%N] (fun n => (greedy_scalar_term r t s n)%:E) = (s N)%:E.
Proof.
move=> hr hs; elim=> [|N IH].
- by rewrite nonnegative_sum_nat_prefix_zero (greedy_scalar_initial hs).
- rewrite nonnegative_sum_nat_prefix_succ; last first.
    move=> n; rewrite lee_fin; exact (@greedy_scalar_term_nonnegative R r t s hr n).
  rewrite IH -EFinD (greedy_scalar_step hs) /greedy_scalar_term.
  by case: ifP=> _; rewrite ?addr0.
Qed.

(** Source for [greedy_scalar_series_upper]: direct inequality of the
    selected-weight series with the target in Federer 2.3.3, p. 76 *)
Lemma greedy_scalar_series_upper (R : realType) (r : nat -> R) (t : \bar R) s :
  (forall n, (0 <= r n)%R) -> 0 <= t -> is_greedy_scalar_expansion r t s ->
  nonnegative_sum setT (fun n => (greedy_scalar_term r t s n)%:E) <= t.
Proof.
move=> hr ht hs; apply: nonnegative_series_prefix_bound=> N.
rewrite (@greedy_scalar_prefix_sum R r t s hr hs); exact: (@greedy_scalar_bounds R r t s hr ht hs N).2.
Qed.
