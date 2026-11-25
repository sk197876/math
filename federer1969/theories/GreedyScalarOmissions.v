(** Federer (1969), 2.3.3, p. 76: a finite selected sum omits arbitrarily
    late weights. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import GreedyScalarExpansionUP NonnegativeSum NonnegativeSumSupport NonnegativeDivergentTails.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [greedy_scalar_arbitrarily_late_omissions]: Supporting
    Federer 2.3.3, p. 76.The conclusion is conditional on finiteness of the
    selected sum. *)
Lemma greedy_scalar_arbitrarily_late_omissions (R : realType)
    (r : nat -> R) (t : \bar R) (s : nat -> R) :
  (forall n, (0 <= r n)%R) -> nonnegative_sum setT (fun n => (r n)%:E) = +oo ->
  nonnegative_sum setT (fun n => (greedy_scalar_term r t s n)%:E) < +oo ->
  forall N, exists n, (N <= n)%N /\ ~~ ((s n + r n)%R%:E <= t).
Proof.
move=> hr hdiv hfin N; apply: contrapT=> hn.
have hall n : (N <= n)%N -> (s n+r n)%R%:E <= t.
  move=> hN; apply: contrapT=> hh; apply: hn; exists n; split=> //; exact/negP.
have he : nonnegative_sum [set n | (N <= n)%N] (fun n => (r n)%:E) =
    nonnegative_sum [set n | (N <= n)%N] (fun n => (greedy_scalar_term r t s n)%:E).
  apply: nonnegative_sum_ext=> n hnN; by rewrite /greedy_scalar_term (hall n hnN).
have hbound : nonnegative_sum [set n | (N <= n)%N]
    (fun n => (greedy_scalar_term r t s n)%:E) <=
    nonnegative_sum setT (fun n => (greedy_scalar_term r t s n)%:E).
  apply: nonnegative_sum_subset=> n _; exact Logic.I.
rewrite -he (@nonnegative_real_divergent_tail R r hr hdiv N) in hbound.
have hbad := le_lt_trans hbound hfin; by rewrite ltxx in hbad.
Qed.
