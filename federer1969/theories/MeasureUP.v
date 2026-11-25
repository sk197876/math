(** Federer (1969), 2.1.2, pp. 53-54: measures on all subsets and
    Caratheodory measurability. The ambient type represents X. A measure
    means an outer measure, with its nonnegative value specified on every
    subset of X. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_measure]: Federer 2.1.2, p. 53, first displayed
    inequality; nonnegative values and domination by the sum over every
    countable covering family. Empty value and monotonicity are
    consequences, not extra defining laws. *)
Record is_measure (R : realType) (I : choiceType)
    (mu : set I -> \bar R) : Prop := {
  measure_nonnegative : forall A, 0 <= mu A;
  measure_countable_cover : forall (A : set I) (F : set (set I)),
    countable F -> A `<=` \bigcup_(B in F) B -> mu A <= nonnegative_sum F mu
}.

(** Source for [measure_measurable]: Federer 2.1.2, p. 54, opening display;
    Caratheodory splitting for every test set. The measure laws are separate
    hypotheses in subsequent theorems. *)
Definition measure_measurable (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (A : set I) :=
  forall T, mu T = mu (T `&` A) + mu (T `\` A).
