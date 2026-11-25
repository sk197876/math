(** Federer (1969), 2.5.2, pp. 92–93: the measure representing the lattice
    functional, together with its suiting-sequence characterisation in the
    nonempty case. This is an abstract specification; a subsequent existence
    proof supplies every law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP RealIntegralFunctionalUP DaniellCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_monotone_daniell_measure]: abstract laws of the
    representing measure constructed in Federer 2.5.2, pp. 92–93 The cover
    characterisation is required only for a nonempty lattice; no uniqueness
    of arbitrary representing measures is asserted. *)
Record is_monotone_daniell_measure (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu : set X -> \bar R) : Prop := {
  (** Source for [monotone_daniell_measure_laws]: the measure conclusion of
    Federer 2.5.2, p. 92 *)
  monotone_daniell_measure_laws : is_measure mu;
  (** Source for [monotone_daniell_measure_integral]: the representation
    equality in Federer 2.5.2, p. 92, proved on p. 93 *)
  monotone_daniell_measure_integral : is_real_integral_functional mu L A;
  (** Source for [monotone_daniell_measure_cover]: suiting-sequence formula in
    Federer 2.5.2, p. 92 This law supports the analysis in 2.5.3. *)
  monotone_daniell_measure_cover : (exists f, L f) -> is_daniell_cover_envelope L A mu
}.
