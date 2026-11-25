(** Public interface for Federer (1969), 2.8.13, pp. 149–150: select a
    controlled subset covering every original center. The maximal
    construction is sealed; only the abstract selection laws are used here.
    Source context: ControlledCenterSelectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import MetricClosedBalls ControlledBallParameters
  RadiusCoverSelectionUP ControlledCenterSelectionUP ControlledCenterSelectionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [controlled_center_selection]: the selected
    controlled parameter set in Federer 2.8.13, p. 149,
    exposed through its abstract laws and an opaque module. *)
Definition controlled_center_selection (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X*R)) (ht : 1 < tau) (hm : 0 < mu)
    (hQ : is_bounded_positive_radius_family mu Q) :=
  @ControlledCenterSelection.value R X tau mu Q ht hm hQ.

(** Source for [controlled_center_selection_specification]: the
    membership, controlledness and center coverage conclusions
    of Federer 2.8.13, pp. 149–150, with strict radius
    comparisons retained. *)
Lemma controlled_center_selection_specification (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X*R)) (ht : 1 < tau) (hm : 0 < mu)
    (hQ : is_bounded_positive_radius_family mu Q) :
  is_controlled_center_selection tau Q (@controlled_center_selection R X tau mu Q ht hm hQ).
Proof. exact: ControlledCenterSelection.laws. Qed.

(** Source for [federer_2_8_13]: the complete lemma in
    Federer 2.8.13, pp. 149–150. For tau>1, mu>0 and
    eligible radii 0<r<mu, a controlled subset covers all
    eligible centers with its closed balls. No countability,
    measure or nonempty-family premise is added. *)
Theorem federer_2_8_13 (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X*R)) :
  1 < tau -> 0 < mu -> is_bounded_positive_radius_family mu Q ->
  exists P, is_controlled_center_selection tau Q P.
Proof.
move=> ht hm hQ; exists (@controlled_center_selection R X tau mu Q ht hm hQ).
exact: controlled_center_selection_specification.
Qed.

(** Source for [controlled_selection_covers_centers]: the
    displayed set inclusion in Federer 2.8.13, p. 149:
    original centers lie in the union of selected closed balls.
    This equivalent set form follows from the abstract coverage law. *)
Lemma controlled_selection_covers_centers (R : realType) (X : metricType R)
    (tau : R) (Q P : set (X*R)) :
  is_controlled_center_selection tau Q P ->
  ((fun q : X*R => q.1) @` Q) `<=` \bigcup_(p in P) parameter_closed_ball p.
Proof.
move=> hs x [q hq <-].
have [p [hp hnear]] := @controlled_center_selection_covers R X tau Q P hs q hq.
by exists p.
Qed.
