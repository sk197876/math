(** Federer (1969), 2.5.14, p. 108: scalar component densities for the Radon
    modification of 2.5.12, p. 104. The laws require actual integral
    representations, measurability, and a pointwise bound; they deliberately
    do not require the countably measurable support built into Federer's
    L-infinity space. Such representatives are obtained from 2.5.10. Source
    context: RadonVectorComponentDensity.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP RealLatticeDensityUP VectorDaniellDensities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_bounded_component_density_family]: abstract
    component laws supporting Federer 2.5.14, p. 108,
    in place of the countable-support component formulation in
    2.5.12, p. 104. Existence is proved separately. *)
Definition is_bounded_component_density_family (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (L : set (X -> R))
    (T : (X -> E) -> R) (phi : set X -> \bar R) (k : E -> X -> R) :=
  forall y, is_real_lattice_density phi (positive_function_lattice L) (component_integral T y) (k y) /\
    forall x, Num.norm (k y x)<=N y.
