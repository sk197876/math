(** Federer (1969), 2.2.10, p. 66: every Borel set in a metric space is a
    univalent projection of a closed subset of X times N, and hence is
    Suslin. The Borel generation criterion is the locally proved and sealed
    2.2.1; no external descriptive-set-theory theorem is imported. Source
    editions: SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SuslinSetUP ClosedSetProjection OpenSetClosedProjection
  ClosedProjectionUnion ClosedProjectionIntersection CountablyClosedSequenceCriterion
  CountablyClosedFamilyUP GeneratedClosed TopologicalBorel MetricBorelGeneration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [univalent_closed_projection_family_laws]: the two closure
    properties of the family F used in Federer 2.2.10, p. 66. The
    disjoint-union and nonempty-intersection requirements agree with the
    weaker generation criterion of 2.2.1. *)
Lemma univalent_closed_projection_family_laws (R : realType) (T : topologicalType) :
  is_countably_closed_family true setT (@has_univalent_closed_projection R T).
Proof.
apply: disjoint_sequence_closure_family.
- exact: closed_set_univalent_projection closed0.
- exact: univalent_closed_projection_disjoint_sequence_union.
- exact: univalent_closed_projection_sequence_intersection.
Qed.

(** Source for [metric_borel_univalent_closed_projection]: direct conclusion
    of the family F argument in Federer 2.2.10, p. 66: every Borel subset of
    a metric space is the one-to-one projection of a closed subset of X
    times N. There is no separability or completeness premise on the ambient
    metric space. *)
Theorem metric_borel_univalent_closed_projection (R : realType) (T : metricType R)
    (S : set T) : borel_set S -> has_univalent_closed_projection R S.
Proof.
have hopen : forall A : set T, open A -> A `<=` setT by move=> A _; exact: subsetT.
pose F := generated_closed_family true hopen.
have hF := generated_closed_family_specification true hopen.
have he : F = @borel_set T := @metric_borel_generated_by_open_closure true R T F hF.
rewrite -he; apply: (@generated_closed_family_minimal true T setT (@open T) hopen).
- exact: univalent_closed_projection_family_laws.
- exact: open_set_univalent_closed_projection.
Qed.

(** Source for [metric_borel_suslin]: direct final consequence on Federer p.
    66 in 2.2.10: every Borel set in a metric space is Suslin, by forgetting
    projection univalence. *)
Theorem metric_borel_suslin (R : realType) (T : metricType R) (S : set T) :
  borel_set S -> is_suslin_set R S.
Proof.
move=> hS; apply: univalent_closed_projection_is_suslin.
exact: (@metric_borel_univalent_closed_projection R T S hS).
Qed.
