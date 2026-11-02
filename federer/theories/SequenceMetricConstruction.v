(** Federer (1969), 2.2.6, p. 63: existence of the finite real value of the
    displayed metric series. This private witness uses the previously proved
    series bound; public consequences use the abstract formula. Source
    editions: SequenceSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum PositiveIntegerDistance SequenceSpaceUP SequenceMetricBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_sequence_metric_exists]: Federer
    2.2.6, p. 63, supporting construction of the real distance
    value. Finiteness follows from the geometric bound, and the
    abstract specification records its equality to the local sum. *)
Lemma positive_sequence_metric_exists (R : realType) (N : choiceType)
    (coordinate : N -> nat -> nat) : exists d : N -> N -> R,
  is_positive_sequence_metric coordinate d.
Proof.
exists (fun x y => fine (nonnegative_sum setT (fun i =>
  (@sequence_metric_weight R i * positive_integer_distance (coordinate x i) (coordinate y i))%:E))).
move=> x y; apply: esym; apply: fineK.
have [h0 h1] := @sequence_metric_series_bound R N coordinate x y.
rewrite ge0_fin_numE //; exact: le_lt_trans h1 (ltry _).
Qed.
