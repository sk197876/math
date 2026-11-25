(** Federer (1969), 2.2.6, p. 63: the space of all infinite positive-integer
    sequences and its displayed metric. We first specify the coordinate
    representation and distance formula abstractly. Natural coordinate i
    encodes the book's positive index i+1; a coordinate value n encodes the
    positive integer n+1. The shift cancels in coordinate differences. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum PositiveIntegerDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_positive_sequence_representation]: Federer 2.2.6, p. 63,
    the Cartesian product has precisely one element for each full choice of
    positive-integer coordinates. This abstract representation specification
    precedes the function space witness. *)
Record is_positive_sequence_representation (N : choiceType)
    (coordinate : N -> nat -> nat) : Prop := {
  sequence_coordinates_injective : injective coordinate;
  sequence_coordinates_surjective : forall s : nat -> nat, exists n, coordinate n = s
}.

(** Source for [sequence_metric_weight]: Federer 2.2.6,
    p. 63, weight 2^-i in the displayed metric, with the book's
    positive i represented by the natural index i-1. *)
Definition sequence_metric_weight (R : realType) (i : nat) : R := ((2^-1)^+i.+1)%R.
Arguments sequence_metric_weight {R} i.

(** Source for [is_positive_sequence_metric]: Federer 2.2.6,
    p. 63, abstract specification of the exact printed distance:
    the sum of weighted bounded coordinate distances equals the
    finite real distance. The sum is the sealed local operator of
    2.1.1. No metric existence is assumed by this definition. *)
Definition is_positive_sequence_metric (R : realType) (N : choiceType)
    (coordinate : N -> nat -> nat) (d : N -> N -> R) :=
  forall x y, nonnegative_sum setT (fun i =>
    (sequence_metric_weight i * positive_integer_distance (coordinate x i) (coordinate y i))%:E) = (d x y)%:E.

(** Source for [positive_sequence_metric_unique]: Federer
    2.2.6, p. 63, supporting uniqueness from the displayed
    series formula, without inspecting a distance construction. *)
Lemma positive_sequence_metric_unique (R : realType) (N : choiceType)
    (coordinate : N -> nat -> nat) (d e : N -> N -> R) :
  is_positive_sequence_metric coordinate d -> is_positive_sequence_metric coordinate e -> d = e.
Proof.
move=> hd he; apply: funext=> x; apply: funext=> y; apply/eqP.
have h := eq_trans (esym (hd x y)) (he x y).
by move/eqP: h; rewrite eqe.
Qed.
