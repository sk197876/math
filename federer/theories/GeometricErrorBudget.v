(** Federer (1969), 2.2.2, p. 61, geometric error bounds in the closed/open
    approximation proof. We reserve half the requested error, using epsilon
    times 2^-(n+2), so a non-strict sum bound still gives a strict final
    error. No external series theorem is used. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumNatPrefix NonnegativeSumContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [geometric_error_tail]: supporting finite-tail
    expression for Federer 2.2.2, p. 61. Half the total error
    remains initially, and the remainder is halved at each step.
    This is an elementary scalar construction used to prove summability. *)
Definition geometric_error_tail (R : realType) (epsilon : R) n :=
  (epsilon / 2 * (2^-1) ^+ n)%R.

(** Source for [geometric_error_budget]: Federer 2.2.2,
    p. 61, geometric choice of tolerances. We express epsilon
    times 2^-(n+2) as consecutive tail differences, which telescope.
    The extra factor one half leaves room for a strict final bound. *)
Definition geometric_error_budget (R : realType) (epsilon : R) n :=
  (geometric_error_tail epsilon n - geometric_error_tail epsilon n.+1)%R.

(** Source for [geometric_error_tail_nonnegative]: supporting nonnegativity
    of the remainder in the geometric estimate of Federer 2.2.2, p. 61 *)
Lemma geometric_error_tail_nonnegative (R : realType) (epsilon : R) n :
  (0 <= epsilon)%R -> (0 <= geometric_error_tail epsilon n)%R.
Proof.
move=> he; rewrite /geometric_error_tail mulr_ge0 //.
- by rewrite divr_ge0 // ler0n.
- by rewrite exprn_ge0 // invr_ge0 ler0n.
Qed.

(** Source for [geometric_error_budget_positive]: Federer
    2.2.2, p. 61, each selected error tolerance is positive,
    so the approximation hypotheses can be applied at that tolerance. *)
Lemma geometric_error_budget_positive (R : realType) (epsilon : R) n :
  (0 < epsilon)%R -> (0 < geometric_error_budget epsilon n)%R.
Proof.
move=> he; rewrite /geometric_error_budget /geometric_error_tail exprSr.
rewrite -mulrBr mulr_gt0 //.
- by rewrite divr_gt0 // ltr0n.
- rewrite -{1}[(((2 : R)^-1)^+n)%R]mulr1 -mulrBr mulr_gt0 //.
  + by rewrite exprn_gt0 // invr_gt0 ltr0n.
  + by rewrite subr_gt0 invf_lt1 // ltr1n.
Qed.

(** Source for [geometric_error_prefix_sum]: supporting finite
    geometric-sum identity in Federer 2.2.2, p. 61. The
    consecutive tail differences telescope to the initial half-error
    minus the remaining tail. The zero prefix is included. *)
Lemma geometric_error_prefix_sum (R : realType) (epsilon : R) N :
  (0 < epsilon)%R ->
  nonnegative_sum [set n | (n < N)%N] (fun n => (geometric_error_budget epsilon n)%:E) =
    (geometric_error_tail epsilon 0 - geometric_error_tail epsilon N)%:E.
Proof.
move=> he.
have hb n : 0 <= (geometric_error_budget epsilon n)%:E.
  rewrite lee_fin; exact: ltW (geometric_error_budget_positive n he).
elim: N=> [|N IH].
- by rewrite nonnegative_sum_nat_prefix_zero subrr.
- rewrite (nonnegative_sum_nat_prefix_succ _ hb) IH -EFinD /geometric_error_budget.
  congr (_%:E); by rewrite addrA subrK.
Qed.

(** Source for [geometric_error_sum_bound]: Federer 2.2.2,
    p. 61, summable geometric errors, proved from bounds on
    finite subsums. Our total is at most epsilon/2, hence strictly
    less than epsilon; this avoids a separate strict-series comparison. *)
Theorem geometric_error_sum_bound (R : realType) (epsilon : R) :
  (0 < epsilon)%R ->
  nonnegative_sum setT (fun n => (geometric_error_budget epsilon n)%:E) <= (epsilon / 2)%:E.
Proof.
move=> he; apply: nonnegative_sum_least=> B _.
have [N hN] : exists N, forall n, n \in B -> (n < N)%N.
  apply: (@finite_increasing_cover _ (fun N => [set n | (n < N)%N]) B).
  - move=> n m hnm k hk; exact: leq_trans hk hnm.
  - move=> k _; exists k.+1; exact: ltnSn.
have hb := @nonnegative_sum_upper R _ [set n | (n < N)%N]
  (fun n => (geometric_error_budget epsilon n)%:E) B hN.
apply: le_trans hb _; rewrite (geometric_error_prefix_sum N he) lee_fin.
have ht := geometric_error_tail_nonnegative N (ltW he).
rewrite /geometric_error_tail expr0 mulr1.
by rewrite lerBlDr lerDl.
Qed.
