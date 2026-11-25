(** Federer (1969), 2.2.6, p. 63: finiteness of the displayed series
    defining sequence distance. The coordinate distances are bounded by one,
    and the local weight sum is bounded by one. Source context:
    SequenceSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum PositiveIntegerDistance SequenceSpaceUP SequenceWeights.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [sequence_metric_series_bound]: Federer
    2.2.6, p. 63, supporting bound for the printed series on
    any coordinate representation. It is nonnegative and at most
    one, so it is the image of a finite real number. *)
Lemma sequence_metric_series_bound (R : realType) (N : choiceType)
    (coordinate : N -> nat -> nat) (x y : N) :
  0 <= nonnegative_sum setT (fun i =>
    (@sequence_metric_weight R i * positive_integer_distance (coordinate x i) (coordinate y i))%:E) /\
  nonnegative_sum setT (fun i =>
    (@sequence_metric_weight R i * positive_integer_distance (coordinate x i) (coordinate y i))%:E) <= 1.
Proof.
split; first exact: nonnegative_sum_nonnegative.
apply: le_trans _ (@sequence_metric_weight_sum_bound R).
apply: nonnegative_sum_mono=> i _; rewrite lee_fin.
rewrite -{2}[@sequence_metric_weight R i]mulr1.
apply: ler_wpM2l; first exact: ltW (sequence_metric_weight_positive i).
exact: ltW (positive_integer_distance_lt_one (coordinate x i) (coordinate y i)).
Qed.
