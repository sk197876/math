(** Federer (1969), 2.4.10, p. 85: the set function psi(A) is the upper
    integral of g over A. The density need only be nonnegative almost
    everywhere for psi to be a measure. Measurability is a separate premise
    for the change-of-density formula. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_measure_density]: abstract set-function
    specification in Federer 2.4.10, p. 85, second
    display. Nonnegativity and the measure laws are proved
    separately; this definition imposes no extra global axiom. *)
Definition is_measure_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (g : partial_function X (extended_real_line R))
    (nu : set X -> \bar R) := forall A, nu A = measure_subset_upper_integral mu A g.

(** Source for [measure_density_unique]: uniqueness of the
    set function prescribed in Federer 2.4.10, p. 85. *)
Lemma measure_density_unique (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (g : partial_function X (extended_real_line R))
    (nu xi : set X -> \bar R) :
  is_measure_density mu g nu -> is_measure_density mu g xi -> forall A, nu A=xi A.
Proof. by move=> hn hx A; rewrite (hn A) (hx A). Qed.
