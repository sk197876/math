(** Federer (1969), 2.3.3, p. 76: removing finitely many finite weights does
    not change divergence of their sum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumNatPrefix NonnegativeSumRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_real_prefix_finite]: supporting finiteness of
    the initial real-weight sum in Federer 2.3.3, p. 76 *)
Lemma nonnegative_real_prefix_finite (R : realType) (r : nat -> R) :
  (forall n, (0 <= r n)%R) -> forall N,
  nonnegative_sum [set n | (n < N)%N] (fun n => (r n)%:E) < +oo.
Proof.
move=> hr; elim=> [|N IH].
- rewrite nonnegative_sum_nat_prefix_zero; exact: ltry.
- rewrite nonnegative_sum_nat_prefix_succ; last by move=> n; rewrite lee_fin.
  exact (lte_add_pinfty IH (ltry (r N))).
Qed.

(** Source for [nonnegative_real_divergent_tail]: supporting tail divergence
    in Federer 2.3.3, p. 76. *)
Lemma nonnegative_real_divergent_tail (R : realType) (r : nat -> R) :
  (forall n, (0 <= r n)%R) -> nonnegative_sum setT (fun n => (r n)%:E) = +oo ->
  forall N, nonnegative_sum [set n | (N <= n)%N] (fun n => (r n)%:E) = +oo.
Proof.
move=> hr hsum N.
have he : setT `\` [set n | (n < N)%N] = [set n | (N <= n)%N].
  apply/seteqP; split=> n.
  - move=> [_ hn]; rewrite /= leqNgt; exact/negP.
  - move=> hn; split=> // hlt; have hn' : (N <= n)%N := hn.
    by move: hn'; rewrite leqNgt hlt.
have hsplit := @nonnegative_sum_split R nat setT [set n | (n < N)%N]
  (fun n => (r n)%:E) (fun n _ => hr n).
rewrite setTI he hsum in hsplit.
apply/eqP; rewrite eq_le leey andTb leNgt; apply/negP=> htail.
have hp := @nonnegative_real_prefix_finite R r hr N.
have hh := lte_add_pinfty hp htail.
by rewrite -hsplit ltxx in hh.
Qed.
