(** Supporting topology of the four-digit regrouping used for Federer
    (1969), 2.2.9, p. 65. Both directions are continuous because each output
    coordinate depends on finitely many input coordinates. This preserves
    the exact positive-sequence topology of 2.2.6, p. 63. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceCoordinateContinuity
  SequenceFourBlocks HomeomorphismOnto.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [sequence_group_four_continuous]: supporting
    continuity of the grouping used with the continued fraction
    in Federer 2.2.9, p. 65. *)
Lemma sequence_group_four_continuous (R : realType) :
  continuous (@sequence_group_four R).
Proof.
apply/(proj2 (positive_sequence_coordinate_continuous _))=> x k.
have h0 := positive_sequence_coordinate_neighborhood x (k*4+0).
have h1 := positive_sequence_coordinate_neighborhood x (k*4+1).
have h2 := positive_sequence_coordinate_neighborhood x (k*4+2).
have h3 := positive_sequence_coordinate_neighborhood x (k*4+3).
apply: filterS (filterI h0 (filterI h1 (filterI h2 h3)))=> y [e0 [e1 [e2 e3]]].
change (positive_sequence_coordinates (sequence_group_four y) k =
  positive_sequence_coordinates (sequence_group_four x) k).
by rewrite /sequence_group_four !positive_sequence_coordinatesK /sequence_four_digits
  e0 e1 e2 e3.
Qed.

(** Source for [sequence_ungroup_four_continuous]: supporting
    continuity of the inverse regrouping for Federer 2.2.9,
    p. 65: a single block determines each ordinary digit. *)
Lemma sequence_ungroup_four_continuous (R : realType) :
  continuous (@sequence_ungroup_four R).
Proof.
apply/(proj2 (positive_sequence_coordinate_continuous _))=> x i.
apply: filterS (positive_sequence_coordinate_neighborhood x (i %/ 4))=> y he.
change (positive_sequence_coordinates (sequence_ungroup_four y) i =
  positive_sequence_coordinates (sequence_ungroup_four x) i).
by rewrite /sequence_ungroup_four !positive_sequence_coordinatesK he.
Qed.

(** Source for [sequence_group_four_open]: supporting relative
    openness for the ordinary-digit continued-fraction map of
    Federer 2.2.9, p. 65. Images under the regrouping
    are inverse images under its continuous inverse. *)
Lemma sequence_group_four_open (R : realType) (O : set (positive_sequence_space R)) :
  open O -> open (sequence_group_four @` O).
Proof.
move=> hO.
have he : sequence_group_four @` O = @sequence_ungroup_four R @^-1` O.
  apply/seteqP; split.
  - move=> y [x hx <-]; change (O (sequence_ungroup_four (sequence_group_four x))).
    by rewrite sequence_group_fourK.
  - move=> y hy; exists (sequence_ungroup_four y)=> //.
    exact: sequence_ungroup_fourK.
rewrite he.
exact: ((proj1 (continuousP _)) (@sequence_ungroup_four_continuous R) O hO).
Qed.

(** Source for [sequence_group_four_homeomorphism]: supporting
    homeomorphism between ordinary digits and four-digit block
    indices for Federer 2.2.9, p. 65. It is a
    reindexing device and does not change the represented fraction. *)
Theorem sequence_group_four_homeomorphism (R : realType) :
  is_homeomorphism_onto setT (@sequence_group_four R).
Proof.
constructor.
- exact: can_inj (@sequence_group_fourK R).
- apply/seteqP; split; first by move=> y _.
  move=> y _; exists (sequence_ungroup_four y); first exact Logic.I.
  exact: sequence_ungroup_fourK.
- exact: sequence_group_four_continuous.
- move=> O hO; exists (sequence_group_four @` O); split.
  + exact: sequence_group_four_open hO.
  + by rewrite setTI.
Qed.
