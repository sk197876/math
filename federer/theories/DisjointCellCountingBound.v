(** Counting the nonempty cells of a disjoint family, supporting the
    partition-multiplicity limit in Federer (1969), 2.10.10, p. 176, and the
    functional in 2.5.10, p. 101. the elementary selection argument below is
    infrastructure, not a separately stated theorem there. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import CountingMeasure CountingInjectionBound MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [disjoint_cells_counting_bound]: the
    number of partition cells meeting a set cannot exceed
    its counting measure, supporting the increasing multiplicity
    assertion in Federer 2.10.10, p. 176.
    The index family and the point set may be uncountable;
    no finiteness or nonemptiness premise is imposed. *)
Theorem disjoint_cells_counting_bound (R : realType) (X J : choiceType)
    (D : set J) (P : J -> set X) (A : set X) :
  (forall i j x, D i -> D j -> P i x -> P j x -> i=j) ->
  counting_measure (R:=R) [set j | D j /\ (A `&` P j) !=set0]<=counting_measure (R:=R) A.
Proof.
move=> hdis.
case: (pselect (A !=set0))=> [[x0 hx0]|hzero].
- have hex j : exists x, (D j /\ (A `&` P j) !=set0 -> A x /\ P j x).
    case: (pselect (D j /\ (A `&` P j) !=set0))=> [[hj [x hx]]|hn].
    + by exists x.
    + exists x0=> h; exact: False_ind _ (hn h).
  pose f j := projT1 (cid (hex j)).
  have hf j : D j /\ (A `&` P j) !=set0 -> A (f j) /\ P j (f j).
    exact: projT2 (cid (hex j)).
  apply: (@counting_measure_injection_bound R J X
    [set j | D j /\ (A `&` P j) !=set0] A f).
  + move=> j hj; exact: (hf j hj).1.
  + move=> i j hi hj hij.
    apply: (hdis i j (f i) hi.1 hj.1 (hf i hi).2).
    by rewrite hij; exact: (hf j hj).2.
- have he : [set j | D j /\ (A `&` P j) !=set0]=set0.
    apply/seteqP; split=> j; last by [].
    move=> [_ [x [hx _]]]; exfalso; apply: hzero; by exists x.
  rewrite he (measure_empty (counting_measure_is_measure R J)).
  exact (@measure_nonnegative R X (@counting_measure R X) (counting_measure_is_measure R X) A).
Qed.
