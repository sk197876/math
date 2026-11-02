(** Opaque scalar-section existence witness for Federer (1969), 2.10.30, p.
    195. The public interface exposes only the characterising laws. Source
    editions: CenteredSectionUP.v *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CenteredSectionUP CenteredSectionConstruction CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type CENTERED_SECTION.
(** Source for [value]: scalar section replacement
    in 2.10.30, p. 195, specified independently
    of the hidden length-halving witness. *)
Parameter value : forall (R : realType) (A : set (real_line_metric R)),
  metric_set_bounded A -> set (real_line_metric R).
(** Source for [laws]: the empty-section, segment
    and length laws of 2.10.30, p. 195. *)
Parameter laws : forall (R : realType) (A : set (real_line_metric R))
  (hb : metric_set_bounded A), is_centered_section A (@value R A hb).
End CENTERED_SECTION.

Module CenteredSection : CENTERED_SECTION.
(** Source for [value]: proved existence witness
    for 2.10.30, p. 195, hidden by opaque
    module ascription; not a new project axiom. *)
Definition value (R : realType) (A : set (real_line_metric R))
  (hb : metric_set_bounded A) :=
  projT1 (cid (@centered_section_exists R A hb)).
(** Source for [laws]: proved defining section laws
    supporting 2.10.30, p. 195. *)
Lemma laws (R : realType) (A : set (real_line_metric R))
  (hb : metric_set_bounded A) : is_centered_section A (@value R A hb).
Proof. exact: (projT2 (cid (@centered_section_exists R A hb))). Qed.
End CenteredSection.
