(** Federer (1969), 2.6.1, pp. 114–115: the Cartesian product is the largest
    measure bounded on measurable rectangles by the product of the factor
    measures. We take this extremal property as its abstract specification;
    the countable-cover construction proves existence, and its infimum
    formula is derived separately. Extended multiplication uses the printed
    convention zero times infinity equals zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_product_measure]: abstract characterisation of the
    Cartesian product in Federer 2.6.1, p. 115, last paragraph This is a
    predicate of proved laws, not a project axiom. *)
Record is_product_measure (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (nu : set (X * Y) -> \bar R) : Prop := {
  (** Source for [product_measure_measure_law]: Federer 2.6.1,
      p. 115: the product measures the Cartesian product space. *)
  product_measure_measure_law : is_measure nu;
  (** Source for [product_measure_rectangle_bound_law]: Federer
      2.6.1, p. 115, displayed inequality for measurable rectangles. *)
  product_measure_rectangle_bound_law : forall A B,
    measure_measurable alpha A -> measure_measurable beta B -> nu (A `*` B) <= alpha A * beta B;
  (** Source for [product_measure_greatest_law]: Federer 2.6.1,
      p. 115: largest measure satisfying the rectangle inequality. *)
  product_measure_greatest_law : forall eta, is_measure eta ->
    (forall A B, measure_measurable alpha A -> measure_measurable beta B ->
      eta (A `*` B) <= alpha A * beta B) -> forall S, eta S <= nu S
}.

(** Source for [product_measure_unique]: supporting uniqueness from the
    largest-measure characterisation in Federer 2.6.1, p. 115 *)
Lemma product_measure_unique (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (nu eta : set (X * Y) -> \bar R) :
  is_product_measure alpha beta nu -> is_product_measure alpha beta eta -> nu=eta.
Proof.
move=> hn he; apply: funext=> S; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (product_measure_greatest_law he (product_measure_measure_law hn)
    (product_measure_rectangle_bound_law hn) S).
- exact: (product_measure_greatest_law hn (product_measure_measure_law he)
    (product_measure_rectangle_bound_law he) S).
Qed.
