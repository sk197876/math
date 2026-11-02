(** Federer (1969), 2.6.3(1), p. 117: the two section measures of the
    diagonal are respectively zero and the characteristic function of [0,1].
    This file proves the section identities for any set under an atomless
    measure and counting measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic CountingMeasure CountingMeasureBorel
  ProductSections ProductAssociativityObstruction CharacteristicFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [restricted_diagonal_vertical_on]: supporting
    singleton section of the diagonal in Federer 2.6.3(1),
    p. 117, at a point of its base set. *)
Lemma restricted_diagonal_vertical_on (X : Type) (A : set X) x :
  A x -> product_vertical_section (restricted_diagonal A) x = [set x].
Proof.
move=> hx; apply/seteqP; split=> y.
- by move=> [_ he]; exact: esym he.
- by move=> ->; split.
Qed.

(** Source for [restricted_diagonal_vertical_off]: supporting
    empty section outside the base set, Federer 2.6.3(1),
    p. 117. *)
Lemma restricted_diagonal_vertical_off (X : Type) (A : set X) x :
  ~ A x -> product_vertical_section (restricted_diagonal A) x = set0.
Proof. move=> hx; apply/seteqP; split=> y //; move=> [ha _]; exact: hx ha. Qed.

(** Source for [restricted_diagonal_horizontal_on]: supporting
    singleton first-coordinate section of the diagonal in
    Federer 2.6.3(1), p. 117. *)
Lemma restricted_diagonal_horizontal_on (X : Type) (A : set X) y :
  A y -> product_horizontal_section (restricted_diagonal A) y = [set y].
Proof.
move=> hy; apply/seteqP; split=> x.
- by move=> [_ he].
- by move=> ->; split.
Qed.

(** Source for [restricted_diagonal_horizontal_off]: supporting
    empty first-coordinate section outside the base set,
    Federer 2.6.3(1), p. 117. *)
Lemma restricted_diagonal_horizontal_off (X : Type) (A : set X) y :
  ~ A y -> product_horizontal_section (restricted_diagonal A) y = set0.
Proof.
move=> hy; apply/seteqP; split=> x //; move=> [ha he].
have heq : x = y := he; apply: hy; by rewrite -heq.
Qed.

(** Source for [atomless_diagonal_horizontal_zero]: the first
    inner integral is identically zero in Federer 2.6.3(1),
    p. 117, since Lebesgue singletons are null. *)
Lemma atomless_diagonal_horizontal_zero (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) :
  (forall x, mu [set x] = 0) -> forall y,
  mu (product_horizontal_section (restricted_diagonal A) y) = 0.
Proof.
move=> hz y; case: (pselect (A y))=> hy.
- by rewrite (restricted_diagonal_horizontal_on hy) hz.
- by rewrite (restricted_diagonal_horizontal_off hy) (measure_empty hm).
Qed.

(** Source for [counting_diagonal_vertical_value]: the other
    inner integral is the characteristic function of the
    base interval in Federer 2.6.3(1), p. 117. *)
Lemma counting_diagonal_vertical_value (R : realType) (X : choiceType) (A : set X) (s : X -> R) :
  is_characteristic_function A s -> forall x,
  @counting_measure R X (product_vertical_section (restricted_diagonal A) x) = (s x)%:E.
Proof.
move=> hs x; case: (pselect (A x))=> hx.
- by rewrite (restricted_diagonal_vertical_on hx) counting_singleton (characteristic_on_set hs hx).
- by rewrite (restricted_diagonal_vertical_off hx) (measure_empty (counting_measure_is_measure R X))
    (characteristic_off_set hs hx).
Qed.
