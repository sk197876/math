(** Federer (1969), 2.2.6, p. 63: the displayed series is a metric. These
    metric laws follow locally from the abstract series formula and
    coordinate injectivity; no witness is unfolded. Source context and
    encoding: SequenceSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumAdd
  PositiveIntegerDistance SequenceSpaceUP SequenceWeights SequenceMetricBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [sequence_metric_term_nonnegative]: Federer
    2.2.6, p. 63, supporting nonnegativity of each weighted
    coordinate distance in the printed metric. *)
Lemma sequence_metric_term_nonnegative (R : realType) (N : choiceType)
    (coordinate : N -> nat -> nat) (x y : N) i :
  0 <= (@sequence_metric_weight R i * positive_integer_distance (coordinate x i) (coordinate y i))%:E.
Proof.
rewrite lee_fin; apply: mulr_ge0.
- exact: ltW (sequence_metric_weight_positive i).
- exact: positive_integer_distance_nonnegative.
Qed.

(** Source for [positive_sequence_distance_bounds]: Federer
    2.2.6, p. 63, supporting nonnegativity and unit bound for
    any distance satisfying the abstract metric formula. *)
Lemma positive_sequence_distance_bounds (R : realType) (N : choiceType)
    (coordinate : N -> nat -> nat) (d : N -> N -> R)
    (hd : is_positive_sequence_metric coordinate d) x y :
  (0 <= d x y <= 1)%R.
Proof.
have [h0 h1] := @sequence_metric_series_bound R N coordinate x y.
rewrite (hd x y) lee_fin in h0 h1; exact/andP.
Qed.

(** Source for [positive_sequence_distance_self]: Federer
    2.2.6, p. 63, metric identity: the distance from a sequence
    to itself is zero because each coordinate summand is zero. *)
Lemma positive_sequence_distance_self (R : realType) (N : choiceType)
    (coordinate : N -> nat -> nat) (d : N -> N -> R)
    (hd : is_positive_sequence_metric coordinate d) x : d x x = 0%R.
Proof.
apply/eqP; rewrite -eqe -(hd x x).
apply/eqP; apply: nonnegative_sum_zero=> i _.
by rewrite positive_integer_distance_self mulr0.
Qed.

(** Source for [positive_sequence_distance_symmetry]: Federer
    2.2.6, p. 63, metric symmetry, obtained by symmetry in
    every coordinate of the defining series. *)
Lemma positive_sequence_distance_symmetry (R : realType) (N : choiceType)
    (coordinate : N -> nat -> nat) (d : N -> N -> R)
    (hd : is_positive_sequence_metric coordinate d) x y : d x y = d y x.
Proof.
apply/eqP; rewrite -eqe -(hd x y) -(hd y x); apply/eqP.
apply: nonnegative_sum_ext=> i _; by rewrite positive_integer_distance_symmetry.
Qed.

(** Source for [positive_sequence_distance_separates]: Federer
    2.2.6, p. 63, separation of distinct sequences: a zero
    sum of nonnegative terms forces every positive-weight coordinate
    distance to vanish, and coordinates determine the sequence. *)
Lemma positive_sequence_distance_separates (R : realType) (N : choiceType)
    (coordinate : N -> nat -> nat) (hN : is_positive_sequence_representation coordinate)
    (d : N -> N -> R) (hd : is_positive_sequence_metric coordinate d) x y :
  d x y = 0%R -> x = y.
Proof.
move=> hzero; apply: (sequence_coordinates_injective hN); apply: funext=> i.
have hs : nonnegative_sum setT (fun j =>
    (@sequence_metric_weight R j * positive_integer_distance (coordinate x j) (coordinate y j))%:E) = 0.
  by rewrite (hd x y) hzero.
have hterm := proj1 (nonnegative_sum_zero_iff
  (fun j _ => @sequence_metric_term_nonnegative R N coordinate x y j)) hs i Logic.I.
move/eqP: hterm; rewrite eqe mulf_eq0 (gt_eqF (sequence_metric_weight_positive i)) orFb=> /eqP hc.
exact: positive_integer_distance_separates hc.
Qed.

(** Source for [positive_sequence_distance_triangle]: Federer
    2.2.6, p. 63, metric triangle inequality. Multiply the
    coordinate inequalities by the positive weights and use local
    nonnegative-sum comparison and additivity from 2.1.1. *)
Lemma positive_sequence_distance_triangle (R : realType) (N : choiceType)
    (coordinate : N -> nat -> nat) (d : N -> N -> R)
    (hd : is_positive_sequence_metric coordinate d) x y z :
  (d x z <= d x y + d y z)%R.
Proof.
rewrite -lee_fin EFinD -(hd x z) -(hd x y) -(hd y z).
rewrite -nonnegative_sum_add.
- apply: nonnegative_sum_mono=> i _; rewrite -EFinD lee_fin -mulrDr.
  apply: ler_wpM2l; first exact: ltW (sequence_metric_weight_positive i).
  exact: positive_integer_distance_triangle.
- move=> i _; exact: sequence_metric_term_nonnegative.
- move=> i _; exact: sequence_metric_term_nonnegative.
Qed.
