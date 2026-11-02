(** Federer (1969), 2.5.3, p. 94: L regularity is specified by
    finite-measure F2 hulls. Both predicates are kept distinct here. They
    specify laws, without adding axioms or presupposing that every measure
    satisfies them. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic ExtendedRealBoundsUP FunctionLatticeUP
  FunctionLatticeLevelFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_function_lattice_regular]: direct equivalence defining L
    regularity in Federer 2.5.3, p. 94. Paraphrase: precisely the
    finite-measure sets admit an F2 superset of equal finite measure. *)
Definition is_function_lattice_regular (R : realType) (X : choiceType)
    (L : set (X -> R)) (mu : set X -> \bar R) :=
  forall S, mu S < +oo <-> exists W,
    S `<=` W /\ function_lattice_finite_hulls L mu W /\ mu S=mu W /\ mu W < +oo.

(** Source for [is_function_lattice_outer_regular]: Supporting Federer
    2.5.3, pp. 94–95. *)
Definition is_function_lattice_outer_regular (R : realType) (X : choiceType)
    (L : set (X -> R)) (mu : set X -> \bar R) :=
  (forall S, function_lattice_strict_levels L S ->
    measure_measurable mu S /\ mu S < +oo) /\
  (forall S V, S `<=` V -> function_lattice_increasing_levels L V -> mu S <= mu V) /\
  (forall S b, (forall V, S `<=` V -> function_lattice_increasing_levels L V -> b <= mu V) -> b <= mu S).

(** Source for [function_lattice_regular_hull]: direct extraction of the
    equal-mass finite hull in Federer 2.5.3, p. 94 This is a consequence of
    the abstract specification, not an existence construction. *)
Lemma function_lattice_regular_hull (R : realType) (X : choiceType)
    (L : set (X -> R)) (mu : set X -> \bar R) :
  is_function_lattice_regular L mu -> forall S, mu S < +oo ->
  exists W, S `<=` W /\ function_lattice_finite_hulls L mu W /\ mu S=mu W /\ mu W < +oo.
Proof. move=> h S; exact: (h S).1. Qed.

(** Source for [empty_function_lattice_not_regular]: necessary boundary
    qualification of the constructed-measure regularity assertion in Federer
    2.5.3, p. 94. A measure gives the empty set finite mass, making its
    required F2 hull impossible. This is a local boundary clarification, not
    an entry in Federer's erratum. *)
Theorem empty_function_lattice_not_regular (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  ~ is_function_lattice_regular (set0 : set (X -> R)) mu.
Proof.
move=> h.
have hfinite : mu set0 < +oo by rewrite (measure_empty hm) ltry.
have [W [_ [hW _]]] := (h set0).1 hfinite.
by rewrite empty_function_lattice_has_no_finite_hulls in hW.
Qed.
