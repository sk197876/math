(** Federer (1969), 2.5.7, p. 99: weights 2^-i in the p=1 maximization
    functional. Indices begin at zero here, so the weight is 2^-(n+1).
    Existing telescoping nonnegative-sum bounds supply summability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport GeometricErrorBudget.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [density_dyadic_weight]: exact coefficient 2^-i in Federer
    2.5.7, p. 99 *)
Definition density_dyadic_weight (R : realType) (n : nat) := (((2%R : R)^-1)^+n.+1)%R.

(** Source for [density_dyadic_weight_positive]: strict positivity needed
    for the increasing scalar functional in Federer 2.5.7, p. 99 *)
Lemma density_dyadic_weight_positive (R : realType) n : (0 < @density_dyadic_weight R n)%R.
Proof. by rewrite /density_dyadic_weight exprn_gt0 // invr_gt0 ltr0n. Qed.

(** Source for [density_dyadic_weight_telescoping]: supporting telescoping
    identity for the weights in Federer 2.5.7, p. 99 This identifies them
    with the already proved geometric budget at epsilon=2. *)
Lemma density_dyadic_weight_telescoping (R : realType) n :
  @density_dyadic_weight R n=geometric_error_budget (2%R : R) n.
Proof.
have h2 : (2%R : R)!=0%R by rewrite pnatr_eq0.
have hh : (1-(2%R : R)^-1=(2%R : R)^-1)%R.
  have h := splitr (1 : R); rewrite !mul1r in h.
  by rewrite {1}h addrK.
rewrite /density_dyadic_weight /geometric_error_budget /geometric_error_tail divff // !mul1r !exprSr.
symmetry; by rewrite -{1}[(((2%R : R)^-1)^+n)%R]mulr1 -mulrBr hh.
Qed.

(** Source for [density_dyadic_weights_sum_bound]: the unit total-weight
    bound for r in Federer 2.5.7, p. 99 The weak bound is all that is needed
    for the maximization argument. *)
Lemma density_dyadic_weights_sum_bound (R : realType) :
  nonnegative_sum setT (fun n => (@density_dyadic_weight R n)%:E) <= 1.
Proof.
have he : (fun n => (@density_dyadic_weight R n)%:E)=
    (fun n => (geometric_error_budget (2%R : R) n)%:E).
  by apply: funext=> n; rewrite density_dyadic_weight_telescoping.
rewrite he.
have h2p : (0 < 2 :> R)%R by rewrite ltr0n.
have hh := @geometric_error_sum_bound R 2%R h2p.
by rewrite divff ?pnatr_eq0 in hh.
Qed.
