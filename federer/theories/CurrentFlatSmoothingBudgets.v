(** Federer (1969), 4.1.18, p. 376: the
    three geometric allowances in the original flat-residual
    iteration. Index k=0 corresponds to printed i=1.
    Reuse the earlier positive geometric budgets and their
    finite-prefix and total-sum estimates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology ring lra.
From Federer Require Import GeometricErrorBudget GeometricUniformTail
  NonnegativeSum NonnegativeSumNatPrefix NonnegativeSumContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Budgets.
Variable R:realType.
Variable delta:R.

(** Source for [flat_smoothing_radius_budget]: the radius
    2^(-i-1)delta in Federer 4.1.18, p. 376. *)
Definition flat_smoothing_radius_budget k:=geometric_error_budget delta k.
(** Source for [flat_smoothing_price_budget]: the price
    2^(-i-2)delta in Federer 4.1.18, p. 376. *)
Definition flat_smoothing_price_budget k:=geometric_error_budget (delta/2) k.
(** Source for [flat_smoothing_residual_budget]: the error
    2^(-i-3)delta in Federer 4.1.18, p. 376. *)
Definition flat_smoothing_residual_budget k:=geometric_error_budget (delta/4) k.

(** Source for [flat_smoothing_budgets_positive]: all three
    original choices are positive when delta>0,
    Federer 4.1.18, p. 376. *)
Lemma flat_smoothing_budgets_positive k:0<delta->
  0<flat_smoothing_radius_budget k /\
  0<flat_smoothing_price_budget k /\
  0<flat_smoothing_residual_budget k.
Proof.
move=>hDelta;split;first exact:geometric_error_budget_positive.
split;apply:geometric_error_budget_positive;rewrite divr_gt0 // ltr0n.
Qed.

(** Source for [flat_smoothing_budget_ratios]: twice the
    approximation error is the next residual allowance,
    and twice the price allowance is the support radius.
    These are the displayed powers in Federer 4.1.18, p. 376. *)
Lemma flat_smoothing_budget_ratios k:
  2*flat_smoothing_residual_budget k=flat_smoothing_price_budget k /\
  2*flat_smoothing_price_budget k=flat_smoothing_radius_budget k.
Proof.
rewrite /flat_smoothing_residual_budget /flat_smoothing_price_budget
  /flat_smoothing_radius_budget /geometric_error_budget /geometric_error_tail.
have hTwo:(2:R)!=0 by rewrite pnatr_eq0.
have hFour:(4:R)!=0 by rewrite pnatr_eq0.
split;field;rewrite ?pnatr_eq0 //.
Qed.

(** Source for [flat_smoothing_radius_total]: the complete
    original support allowance is at most delta/2,
    Federer 4.1.18, p. 376. *)
Lemma flat_smoothing_radius_total:0<delta->
  (nonnegative_sum setT (fun k=>(flat_smoothing_radius_budget k)%:E)<=
    (delta/2)%:E)%E.
Proof. exact:geometric_error_sum_bound. Qed.

(** Source for [flat_smoothing_price_small]: the original
    residual bounds tend uniformly to zero, supporting
    the weak-limit identity in Federer 4.1.18, p. 376. *)
Lemma flat_smoothing_price_small:0<delta->forall eta:R,0<eta->
  exists k,forall j,(k<=j)%N->flat_smoothing_price_budget j<eta.
Proof.
move=>hDelta eta hEta.
have hHalf:(0<(2:R)^-1<1) by rewrite invr_gt0 ltr0n invf_lt1 // ltr1n.
have hScale:0<=delta/4 by rewrite divr_ge0 // ?ltW // ler0n.
have[k hk]:=@geometric_uniform_tail R ((2:R)^-1) (delta/4) eta hHalf hScale hEta.
exists k=>j hj.
have hBound:flat_smoothing_price_budget j<=((2:R)^-1)^+j*(delta/4).
  rewrite /flat_smoothing_price_budget /geometric_error_budget
    /geometric_error_tail exprSr.
  have hPow:0<=((2:R)^-1)^+j by rewrite exprn_ge0 // invr_ge0 ler0n.
  have hPowNext:0<=((2:R)^-1)^+j.+1 by rewrite exprn_ge0 // invr_ge0 ler0n.
  have hTwo:(2:R)!=0 by rewrite pnatr_eq0.
  have hScaleE:delta/2/2=delta/4 by field.
  rewrite hScaleE.
  nra.
exact:(le_lt_trans hBound (hk j hj)).
Qed.
End Budgets.
