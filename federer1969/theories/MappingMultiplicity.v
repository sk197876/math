(** Federer (1969), 2.10.9, p. 175: N(f,y) is the number, possibly infinite,
    of points in the inverse image of y. Its restricted form N(f|A,y) occurs
    in 2.10.10, p. 176, and in the geometric example of 2.5.10, p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import CountingMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [mapping_fibre]: the inverse-image set
    of f restricted to A, supporting the definition
    of multiplicity in Federer 2.10.9, p. 175. *)
Definition mapping_fibre (X Y : Type) (f : X -> Y) (A : set X) y :=
  [set x | A x /\ f x=y].

(** Source for [mapping_multiplicity]: direct counting
    definition of N(f|A,y) in Federer 2.10.9–10,
    pp. 175–176. The actual sealed counting measure
    is used, including for uncountable fibres. *)
Definition mapping_multiplicity (R : realType) (X : choiceType) (Y : Type)
    (f : X -> Y) (A : set X) y := counting_measure (R:=R) (mapping_fibre f A y).

(** Source for [mapping_multiplicity_nonnegative]:
    nonnegativity of the counting integrand in Federer
    2.10.10, p. 176, from 2.1.2, p. 54. *)
Lemma mapping_multiplicity_nonnegative (R : realType) (X : choiceType) (Y : Type)
    (f : X -> Y) (A : set X) y : 0<=@mapping_multiplicity R X Y f A y.
Proof. exact (@measure_nonnegative R X _ (counting_measure_is_measure R X) _). Qed.

(** Source for [mapping_multiplicity_empty]: the empty
    restricted fibre has count zero, the boundary case
    in Federer 2.10.9–10, pp. 175–176. *)
Lemma mapping_multiplicity_empty (R : realType) (X : choiceType) (Y : Type)
    (f : X -> Y) y : @mapping_multiplicity R X Y f set0 y=0.
Proof.
have he : mapping_fibre f set0 y=set0.
  apply/seteqP; split; first by move=> x [[] _].
  by move=> x [].
rewrite /mapping_multiplicity he; exact: measure_empty (counting_measure_is_measure R X).
Qed.
