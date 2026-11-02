(** Federer (1969), 2.2.10, p. 66: every open subset of a metric space has a
    univalent closed-projection representation. Only abstract distance laws
    and the sealed real parametrisation are used here. Source context:
    SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground SequenceSpace SuslinSetUP ClosedSetProjection
  MetricSetDistanceUP MetricSetDistanceSealed DistanceReciprocalGraph
  ClosedSequenceBijectionUP ClosedRealParametrisation ClosedProjectionTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [open_set_univalent_closed_projection]: direct open-set
    assertion in Federer 2.2.10, p. 66. For a proper open S use the closed
    equation t*dist(x,X minus S)=1 and transfer its real coordinate to the
    closed sequence domain. The whole space is represented by its product
    with a singleton. *)
Theorem open_set_univalent_closed_projection (R : realType) (T : metricType R)
    (S : set T) : open S -> has_univalent_closed_projection R S.
Proof.
move=> hS; case: (pselect (S = setT))=> [->|hproper].
  exact: closed_set_univalent_projection closedT.
have hn : (~` S) !=set0.
  apply: contrapT=> hempty; apply: hproper; apply/seteqP; split=> // x _.
  apply: contrapT=> hx; apply: hempty; by exists x.
pose d := @MetricSetDistance.value R T (~` S) hn.
have hd : is_metric_set_distance (~` S) d := @MetricSetDistance.laws R T (~` S) hn.
have [B [psi hpsi]] := @closed_real_sequence_parametrisation R.
apply: (@closed_projection_transfer R T (real_line_metric R) S (distance_reciprocal_graph d) B psi hpsi).
- exact: distance_reciprocal_graph_closed hd.
- exact: distance_reciprocal_graph_image hd hS.
- exact: distance_reciprocal_graph_injective.
Qed.

(** Source for [open_set_suslin]: consequence of the open-set
    representation in Federer 2.2.10, p. 66: forget
    univalence of the closed witness to obtain a Suslin set. *)
Lemma open_set_suslin (R : realType) (T : metricType R) (S : set T) :
  open S -> is_suslin_set R S.
Proof.
move=> hS; apply: univalent_closed_projection_is_suslin.
exact: (@open_set_univalent_closed_projection R T S hS).
Qed.
