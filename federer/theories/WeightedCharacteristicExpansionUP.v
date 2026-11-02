(** Federer (1969), 2.3.3, p. 76: representation of a nonnegative
    extended-real measurable function by a prescribed divergent sequence of
    positive weights tending to zero. The local Federer erratum, p. 1, book
    p. 76 line 3, italicizes “and”; it does not alter the mathematical
    hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP NonnegativeSum ExtendedRealOrderLimit CharacteristicFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_positive_vanishing_divergent_sequence]: direct
    three weight hypotheses in Federer 2.3.3, p. 76.
    Convergence uses the project's order-neighborhood specification;
    positive real weights have their usual finite extended-real values. *)
Record is_positive_vanishing_divergent_sequence (R : realType) (r : nat -> R) : Prop := {
  (** Source for [expansion_weights_positive]: positive weights
      in the opening sentence of Federer 2.3.3, p. 76. *)
  expansion_weights_positive : forall n, (0 < r n)%R;
  (** Source for [expansion_weights_vanish]: the zero-limit
      hypothesis in the first display of Federer 2.3.3, p. 76. *)
  expansion_weights_vanish : extended_order_limit (fun n => (r n)%:E) 0;
  (** Source for [expansion_weights_diverge]: the divergent-sum
      hypothesis in the first display of Federer 2.3.3, p. 76. *)
  expansion_weights_diverge : nonnegative_sum setT (fun n => (r n)%:E) = +oo
}.

(** Source for [is_weighted_characteristic_expansion]: abstract
    conclusion of Federer 2.3.3, p. 76, including measurable
    sets, their characteristic functions, and pointwise equality at
    every point, rather than only almost everywhere. *)
Record is_weighted_characteristic_expansion (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : X -> \bar R) (r : nat -> R)
    (A : nat -> set X) (g : nat -> X -> R) : Prop := {
  (** Source for [expansion_sets_measurable]: measurable sets in
      the conclusion of Federer 2.3.3, p. 76. *)
  expansion_sets_measurable : forall n, measure_measurable mu (A n);
  (** Source for [expansion_characteristic_laws]: characteristic
      functions associated with these sets in Federer 2.3.3, p. 76. *)
  expansion_characteristic_laws : forall n, is_characteristic_function (A n) (g n);
  (** Source for [expansion_pointwise_sum]: the displayed pointwise
      representation in Federer 2.3.3, p. 76. All weights
      are finite, so multiplication by zero is defined even when f is infinite. *)
  expansion_pointwise_sum : forall x,
    nonnegative_sum setT (fun n => (r n * g n x)%R%:E) = f x
}.

(** Source for [is_greedy_characteristic_expansion]: the inductive choice of
    sets in the proof of Federer 2.3.3, p. 76 *)
Definition is_greedy_characteristic_expansion (R : realType) (X : Type)
    (f : X -> \bar R) (r : nat -> R) (A : nat -> set X) (g : nat -> X -> R) :=
  forall n x, A n x <->
    ((r n + \sum_(j < n) r j * g j x)%R%:E <= f x).
