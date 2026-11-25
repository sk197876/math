(** Federer (1969), 2.10.30, p. 195: abstract specification of Steiner
    symmetrisation by all perpendicular line sections. The unit normal
    specifies an arbitrary orthogonal hyperplane, rather than a chosen
    coordinate hyperplane. Compactness, convexity and whole-space volume
    equality are conclusions to prove, not specification fields. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import InnerProductUP OrthonormalFamilies RealMetricBackground CenteredSectionUP UnitNormalGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normal_scalar_section]: direct scalar representation of S
    intersected with the normal line through y in 2.10.30, p. 195 The point
    y is required to lie in the hyperplane by the subsequent specification. *)
Definition normal_scalar_section (R : realType) (V : lmodType R)
    (u : V) (S : set V) (y : V) : set (real_line_metric R) :=
  [set t | S (y+t*:u)].

(** Source for [is_steiner_symmetrisation]: direct
    characterisation by the two line-section alternatives
    in 2.10.30, p. 195. The unit normal is
    part of the hypotheses; boundedness will establish
    existence, without imposing measurability of S. *)
Record is_steiner_symmetrisation (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (S T : set V) : Prop := {
  (** Source for [steiner_unit_normal_law]: direct unit
      normal used in 2.10.30, p. 195. The orthogonal
      hyperplane is the kernel of x mapped to x.u. *)
  steiner_unit_normal_law : B u u= 1;
  (** Source for [steiner_normal_sections_law]: direct
      empty-section and centred equal-length segment laws
      in 2.10.30, p. 195, for every normal line. *)
  steiner_normal_sections_law : forall y, inner_coordinate hB u y=0 ->
    is_centered_section (normal_scalar_section u S y) (normal_scalar_section u T y)
}.
