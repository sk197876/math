(** Federer (1969), 2.5.1, p. 92: integration gives a real-valued map on
    every sublattice of summable functions. The abstract specification
    concerns only members of L; values of the ambient representative off L
    are immaterial. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_real_integral_functional]: the map sending f to integral
    f in Federer 2.5.1, p. 92 *)
Definition is_real_integral_functional (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (L : set (X -> R)) (A : (X -> R) -> R) :=
  forall f, L f -> is_measure_integral mu (real_total_integrand f) (A f)%:E.

(** Source for [real_integral_functional_unique_on_lattice]:
    well-definedness of the integral map in Federer 2.5.1, p. 92 Only values
    on the specified domain L are asserted unique. *)
Lemma real_integral_functional_unique_on_lattice (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (L : set (X -> R)) (A B : (X -> R) -> R) :
  is_real_integral_functional mu L A -> is_real_integral_functional mu L B ->
  forall f, L f -> A f=B f.
Proof.
move=> hA hB f hf; have he := measure_integral_unique (hA f hf) (hB f hf).
by injection he.
Qed.
