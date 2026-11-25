(** Federer (1969), 2.4.12, p. 87: norm control for finite-image
    approximants in the density assertion. The nearest-prefix construction
    is a supporting way to make its finite-partition approximation
    compatible with dominated convergence. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import RealNormUP NormMetric FiniteNearestApproximationUP FiniteNearestApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_nearest_norm_error_bound]: supporting
    integrable majorant for Federer 2.4.12, p. 87: if
    zero is the first candidate, the error never exceeds the input
    norm. This includes the zero vector and n=0. *)
Lemma finite_nearest_norm_error_bound (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (y : nat -> real_norm_metric_space hN) (q : nat -> real_norm_metric_space hN -> nat) :
  y 0%N=0 -> is_finite_nearest_approximation y q -> forall n x,
    N (x-y (q n x)) <= N x.
Proof.
move=> hy h n x; have hh := finite_nearest_map_reference_bound h n x.
change (is_true (N (x-y (q n x)) <= N (x-y 0%N))) in hh.
by rewrite hy subr0 in hh.
Qed.

(** Source for [finite_nearest_norm_value_bound]: supporting
    summability bound for the finite-image approximants in Federer
    2.4.12, p. 87. Their norms are at most twice
    the original norm, by the error bound and the triangle inequality. *)
Lemma finite_nearest_norm_value_bound (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (y : nat -> real_norm_metric_space hN) (q : nat -> real_norm_metric_space hN -> nat) :
  y 0%N=0 -> is_finite_nearest_approximation y q -> forall n x,
    N (y (q n x)) <= N x+N x.
Proof.
move=> hy h n x.
have hb := @finite_nearest_norm_error_bound R V N hN y q hy h n x.
have ht := @real_seminorm_triangle R V N hN.1 x (y (q n x)-x).
rewrite addrC subrK (real_seminorm_subtract hN.1) in ht.
exact: le_trans ht (lerD (lexx _) hb).
Qed.
