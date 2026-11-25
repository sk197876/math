(** Public centred scalar sections for Federer (1969), 2.10.30, p. 195. All
    consequences use the specification through the opaque interface. Source
    editions: CenteredSectionUP.v *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CoveringFamilyUP CenteredSectionUP
  CenteredSectionLaws CenteredSectionSealed LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [centered_section]: direct scalar
    replacement operation on each normal line in
    2.10.30, p. 195. Its boundedness proof
    is auxiliary to the abstract characterisation. *)
Definition centered_section (R : realType) (A : set (real_line_metric R))
  (hb : metric_set_bounded A) := @CenteredSection.value R A hb.

(** Source for [centered_section_specification]: direct
    defining laws of the line replacement in 2.10.30,
    p. 195, supplied by its sealed existence proof. *)
Lemma centered_section_specification (R : realType) (A : set (real_line_metric R))
  (hb : metric_set_bounded A) : is_centered_section A (centered_section hb).
Proof. exact: CenteredSection.laws. Qed.

(** Source for [centered_section_proof_independent]: supporting
    well-definedness of the operation in 2.10.30,
    p. 195. Different boundedness witnesses yield the
    same set, by uniqueness of the abstract section laws. *)
Lemma centered_section_proof_independent (R : realType) (A : set (real_line_metric R))
  (hb hc : metric_set_bounded A) : centered_section hb=centered_section hc.
Proof. exact: centered_section_unique (centered_section_specification hb) (centered_section_specification hc). Qed.

(** Source for [centered_section_length]: direct preservation of normal-line
    length in 2.10.30, p. 195 *)
Lemma centered_section_length (R : realType) (A : set (real_line_metric R))
  (hb : metric_set_bounded A) :
  lebesgue_scalar_measure (centered_section hb)=lebesgue_scalar_measure A.
Proof. exact: centered_section_length_law (centered_section_specification hb). Qed.
