(** Federer (1969), 3.2.16, p. 253: the
    geometric tail estimate in the annular proof.
    Derived from finite sums and the project's
    abstract nonnegative numerical sum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumRestriction
  NonnegativeSumScale GeometricErrorBudget.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [geometric_error_tail_sum_bound]:
    the bound by 2^(-j) for the remaining
    errors in Federer 3.2.16, p. 253.
    Indices start at zero, so the budget
    at n is 2^(-n-1). *)
Theorem geometric_error_tail_sum_bound (R : realType) J :
  nonnegative_sum [set n | (J<=n)%N]
    (fun n => (geometric_error_budget (2:R) n)%:E) <=
    (geometric_error_tail (2:R) J)%:E.
Proof.
have h2 : (0<(2:R))%R by rewrite ltr0n.
have hb n : 0 <= (geometric_error_budget (2:R) n)%:E.
  rewrite lee_fin; exact: ltW (geometric_error_budget_positive n h2).
have hsplit := @nonnegative_sum_split R _ setT
  [set n : nat | (n<J)%N] (fun n => (geometric_error_budget (2:R) n)%:E)
  (fun n _ => hb n).
have hprefix : (setT `&` [set n | (n<J)%N]) = [set n | (n<J)%N].
  by apply/seteqP; split=> n; [move=> [_ hn]|move=> hn; split].
have htail : (setT `\` [set n | (n<J)%N]) = [set n | (J<=n)%N].
  apply/seteqP; split=> n.
  - move=> [_ hn]; change (is_true (J<=n)%N); rewrite leqNgt; apply/negP; exact: hn.
  - move=> hn; split=> // hn'; by have := leq_ltn_trans hn hn'; rewrite ltnn.
rewrite hprefix htail (geometric_error_prefix_sum J h2) in hsplit.
have hsum := geometric_error_sum_bound h2.
rewrite hsplit in hsum.
have ht0 : geometric_error_tail (2:R) 0= (1:R)%R.
  by rewrite /geometric_error_tail expr0 mulr1 divff // pnatr_eq0.
rewrite ht0 divff ?pnatr_eq0 // in hsum.
have he : (1:R)%:E = (1-geometric_error_tail (2:R) J)%R%:E +
    (geometric_error_tail (2:R) J)%:E.
  by rewrite -EFinD subrK.
rewrite he leeD2lE // in hsum.
Qed.

(** Source for [geometric_error_weighted_tail_bound]:
    after multiplying by r^m the omitted
    annular mass is at most r^m 2^(-j),
    Federer 3.2.16, p. 253. *)
Lemma geometric_error_weighted_tail_bound (R : realType) J (c : R) :
  (0<=c)%R ->
  nonnegative_sum [set n | (J<=n)%N]
    (fun n => (c*geometric_error_budget (2:R) n)%R%:E) <=
    (c*geometric_error_tail (2:R) J)%R%:E.
Proof.
move=> hc.
have hb n : 0 <= (geometric_error_budget (2:R) n)%:E.
  rewrite lee_fin; apply: ltW; apply: geometric_error_budget_positive; by rewrite ltr0n.
rewrite EFinM (@nonnegative_sum_scale R _ [set n : nat | (J<=n)%N] (fun n => (geometric_error_budget (2:R) n)%:E) c hc (fun n _=>hb n)).
rewrite EFinM; apply: lee_wpmul2l; first by rewrite lee_fin.
exact: geometric_error_tail_sum_bound.
Qed.
