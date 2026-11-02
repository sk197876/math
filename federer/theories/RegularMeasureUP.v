(** Federer (1969), 2.1.5, pp. 56-57: regularity of measures. Regularity
    here means measurable supersets of equal measure, not topological
    regularity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureHull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_regular_measure]: Federer 2.1.5, p. 56, opening
    definition; every subset has a measurable superset of equal measure. The
    measure laws are separate from this regularity predicate. *)
Definition is_regular_measure (R : realType) (I : choiceType)
    (mu : set I -> \bar R) := forall A, exists B,
  A `<=` B /\ measure_measurable mu B /\ mu A = mu B.

(** Source for [regular_measure_finite_hull]: Federer 2.1.5(2), p. 56, with
    proof p. 57; finite-measure sets have hulls by applying 2.1.4 to the
    equal-measure measurable superset. *)
Theorem regular_measure_finite_hull (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) :
  is_regular_measure mu -> forall A, mu A < +oo ->
  exists B, is_measure_hull mu A B.
Proof.
move=> hr A hf; have [B [hAB [hB he]]] := hr A.
exists B; exact: (@measure_hull_of_finite_equal_measure R I mu hm A B hAB hB he hf).
Qed.
