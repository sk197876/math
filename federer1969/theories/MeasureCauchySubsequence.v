(** Federer (1969), 2.3.10, p. 80: a Cauchy sequence has a subsequence with
    summable successive distances. We use the previously proved positive
    geometric budget 2^-(n+2), a smaller geometric tolerance than the
    printed 2^-n; the indexing starts at zero. Source context:
    CauchyIndexSelectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureConvergenceUP NonnegativeSum GeometricErrorBudget
  CauchyIndexSelectionUP CauchyIndexSelectionSealed CauchyIndexSelectionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [cauchy_measure_summable_subsequence]: the
    choice of N(n) and summable increment estimate in Federer
    2.3.10, p. 80. This selection uses only the Cauchy
    property, so no measurability or completeness is needed yet. *)
Lemma cauchy_measure_summable_subsequence (R : realType) (X : choiceType)
    (V : lmodType R) (mu : set X -> \bar R) (N : V -> R)
    (f : nat -> partial_function X V) :
  cauchy_in_measure mu N f -> exists s : nat -> nat,
    (forall n, (s n < s n.+1)%N) /\
    nonnegative_sum setT (fun n => measure_normed_distance mu N (f (s n.+1)) (f (s n))) < +oo.
Proof.
move=> hc.
pose d i j := measure_normed_distance mu N (f i) (f j).
pose b := geometric_error_budget (1%R : R).
have hb n : (0 < b n)%R := geometric_error_budget_positive n (ltr01 : (0 < 1 :> R)%R).
have hcut n : exists K, forall i j, (K <= i)%N -> (K <= j)%N -> d i j < (b n)%:E.
  exact: hc (b n) (hb n).
pose s := @CauchyIndexSelection.value R d b hcut.
have hs := @CauchyIndexSelection.laws R d b hcut.
exists s; split; first exact hs.1.
apply: le_lt_trans _ (ltry ((1/2)%R : R)).
apply: le_trans _ (geometric_error_sum_bound (ltr01 : (0 < 1 :> R)%R)).
apply: nonnegative_sum_mono=> n _; exact: ltW (cauchy_index_successive_bound hs n).
Qed.
