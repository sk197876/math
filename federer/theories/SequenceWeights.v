(** Federer (1969), 2.2.6, p. 63: the positive weights 2^-i make the
    coordinate metric series bounded. We reuse the locally proved
    geometric-error bound from 2.2.2, without importing a series theorem.
    Source context and positive-index encoding: SequenceSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport GeometricErrorBudget SequenceSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [sequence_metric_weight_positive]: Federer
    2.2.6, p. 63, positivity of every weight in the metric sum. *)
Lemma sequence_metric_weight_positive (R : realType) i :
  (0 < @sequence_metric_weight R i)%R.
Proof. by rewrite /sequence_metric_weight exprn_gt0 // invr_gt0 ltr0n. Qed.
Arguments sequence_metric_weight_positive {R} i.

(** Source for [sequence_metric_weight_as_budget]: supporting
    reuse of the geometric-sum estimate of Federer 2.2.2, p. 61,
    for the exact weights in 2.2.6, p. 63. At tolerance 2, our
    half-error budget has terms exactly 2^-(i+1). *)
Lemma sequence_metric_weight_as_budget (R : realType) i :
  @sequence_metric_weight R i = geometric_error_budget (2 : R)%R i.
Proof.
have hhalf : (1 - (2 : R)^-1 = (2 : R)^-1)%R.
  by rewrite {1}(splitr (1 : R)%R) !mul1r addrK.
rewrite /geometric_error_budget /geometric_error_tail divff ?pnatr_eq0 // !mul1r.
rewrite exprSr -{1}[(((2 : R)^-1)^+i)%R]mulr1 -mulrBr hhalf.
by rewrite /sequence_metric_weight exprSr.
Qed.

(** Source for [sequence_metric_weight_sum_bound]: Federer
    2.2.6, p. 63, supporting bound by one for the sum of all
    metric weights. The locally proved finite-subsum estimate suffices. *)
Lemma sequence_metric_weight_sum_bound (R : realType) :
  nonnegative_sum setT (fun i => (@sequence_metric_weight R i)%:E) <= 1.
Proof.
have he : nonnegative_sum setT (fun i => (@sequence_metric_weight R i)%:E) =
    nonnegative_sum setT (fun i => (geometric_error_budget (2 : R)%R i)%:E).
  apply: nonnegative_sum_ext=> i _; by rewrite sequence_metric_weight_as_budget.
rewrite he; have hp : (0 < (2 : R))%R by rewrite ltr0n.
have h := geometric_error_sum_bound hp.
by rewrite divff ?pnatr_eq0 // in h.
Qed.
