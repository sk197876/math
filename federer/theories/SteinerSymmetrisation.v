(** Public Steiner symmetrisation for Federer (1969), 2.10.30, p. 195. The
    operation is specified by laws; its private existence witness cannot be
    unfolded here. Source context: SteinerSymmetrisationUP.v *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerMetric OrthonormalFamilies CoveringFamilyUP
  SteinerSymmetrisationUP SteinerSymmetrisationLaws SteinerSymmetrisationSealed UnitNormalGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_symmetrisation]: direct operation
    defined in 2.10.30, p. 195, for the
    hyperplane orthogonal to the supplied unit normal.
    Boundedness and unit-normal proofs ensure existence;
    uniqueness will make their choice immaterial. *)
Definition steiner_symmetrisation (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (hu : B u u= 1) (S : set (inner_metric_space hB))
    (hb : metric_set_bounded S) := @SteinerSymmetrisation.value R V B hB u hu S hb.

Arguments steiner_symmetrisation {R V B} hB {u} hu {S} hb.

(** Source for [steiner_symmetrisation_specification]: direct
    unit-normal and equal-length line-section laws in
    2.10.30, p. 195, supplied by the opaque
    existence proof. *)
Lemma steiner_symmetrisation_specification (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (hu : B u u= 1) (S : set (inner_metric_space hB))
    (hb : metric_set_bounded S) :
  is_steiner_symmetrisation hB u S (steiner_symmetrisation hB hu hb).
Proof. exact: SteinerSymmetrisation.laws. Qed.

Arguments steiner_symmetrisation_specification {R V B} hB {u} hu {S} hb.

(** Source for [steiner_symmetrisation_proof_independent]: supporting
    well-definedness of the operation of 2.10.30,
    p. 195, from uniqueness of its section laws. *)
Lemma steiner_symmetrisation_proof_independent (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (hu hv : B u u= 1) (S : set (inner_metric_space hB))
    (hb hc : metric_set_bounded S) :
  steiner_symmetrisation hB hu hb=steiner_symmetrisation hB hv hc.
Proof.
exact (steiner_symmetrisation_unique (steiner_symmetrisation_specification hB hu hb)
  (steiner_symmetrisation_specification hB hv hc)).
Qed.

(** Source for [steiner_symmetrisation_reflection]: direct rho_u(T)=T in
    2.10.30, p. 195 The proof uses only the sealed section laws. *)
Theorem steiner_symmetrisation_reflection (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (hu : B u u= 1) (S : set (inner_metric_space hB))
    (hb : metric_set_bounded S) :
  normal_reflection hB u @` steiner_symmetrisation hB hu hb=steiner_symmetrisation hB hu hb.
Proof. exact (steiner_reflection_image (steiner_symmetrisation_specification hB hu hb)). Qed.
