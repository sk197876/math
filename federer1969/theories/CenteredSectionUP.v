(** Federer (1969), 2.10.30, p. 195: Steiner symmetrisation replaces every
    nonempty normal line section by a centred closed segment of the same
    length, and leaves empty sections empty. This scalar specification
    isolates those laws before the existence construction. Scalar Lebesgue
    length is identified with Hausdorff length in 2.10.7, pp. 174–175. The
    local erratum has no mathematical correction to this definition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_centered_section]: direct scalar
    interpretation of the two alternatives in Federer
    2.10.30, p. 195. The support law distinguishes an
    empty section from a nonempty null section; the shape
    and length laws allow a degenerate closed segment. *)
Record is_centered_section (R : realType) (A B : set (real_line_metric R)) : Prop := {
  (** Source for [centered_section_support_law]: direct preservation of empty
    and nonempty line sections in 2.10.30, p. 195 *)
  centered_section_support_law : A !=set0 <-> B !=set0;
  (** Source for [centered_section_shape_law]: direct
      centred closed-segment alternative in 2.10.30,
      p. 195, including radius zero. *)
  centered_section_shape_law : B !=set0 ->
    exists r : R, 0<=r /\ B=`[-r,r];
  (** Source for [centered_section_length_law]: direct equality of section
    lengths in 2.10.30, p. 195, using the scalar interpretation justified. *)
  centered_section_length_law : lebesgue_scalar_measure B=lebesgue_scalar_measure A
}.
