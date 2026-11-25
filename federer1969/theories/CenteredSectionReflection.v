(** Reversing scalar section coordinates for Federer (1969), 2.10.30, p.
    195. The two oriented coordinates on the same perpendicular line specify
    the same centred segment. Source context: CenteredSectionUP.v and
    ScalarReflectionMeasure.v *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CenteredSectionUP CenteredSectionLaws
  ScalarReflectionMeasure LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [centered_section_reverse_coordinates]: supporting
    invariance of the defining alternatives in 2.10.30,
    p. 195, when the normal is reversed.
    The empty and nonempty null cases remain distinct. *)
Lemma centered_section_reverse_coordinates (R : realType) (A B : set (real_line_metric R)) :
  is_centered_section A B ->
  is_centered_section ((fun t : real_line_metric R=> -t) @^-1` A)
    ((fun t : real_line_metric R=> -t) @^-1` B).
Proof.
move=> h.
have hBe : ((fun t : real_line_metric R=> -t) @^-1` B)=B.
  apply/seteqP; split=> t; [exact: (centered_section_reflection h t).1|exact: (centered_section_reflection h t).2].
rewrite hBe; constructor.
- split.
  + move=> [t ht]; apply: (centered_section_support_law h).1; by exists (-t).
  + move=> hne; have [t ht] := (centered_section_support_law h).2 hne.
    exists (-t); by rewrite /= opprK.
- exact: centered_section_shape_law h.
- by rewrite scalar_reflection_preserves_length; exact: centered_section_length_law h.
Qed.
