(** Cofinal covering cutoffs of Federer (1969), 2.10.1,
    p. 170, used for the section limit in 3.2.45, p. 280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealBoundsUP MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleEnvelopeLaws
  CaratheodoryLimitUP CaratheodoryBorelRegular RealLatticeTruncationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_scale_reciprocal_increasing]: supporting
    increasing section cutoffs in Federer 3.2.45,
    p. 280. The existing reciprocal order and
    covering-infimum cutoff order apply to every
    original covering family. No source measurability
    or finite measure is required. *)
Lemma metric_scale_reciprocal_increasing (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (A : set X) n m :
  (n<=m)%N ->
  metric_scale_envelope S c (((n.+1)%:R : R)^-1)%R%:E A<=
    metric_scale_envelope S c (((m.+1)%:R : R)^-1)%R%:E A.
Proof.
move=> hNM.
apply: (@metric_scale_envelope_antitone_cutoff R X J S c
  (((m.+1)%:R : R)^-1)%R%:E (((n.+1)%:R : R)^-1)%R%:E _ _
  (metric_scale_envelope_specification _ _ _) (metric_scale_envelope_specification _ _ _))=> //.
rewrite lee_fin; exact: positive_reciprocal_nat_antitone hNM.
Qed.

(** Source for [caratheodory_reciprocal_cutoff_supremum]: supporting
    recovery of the actual final section measure in
    Federer 3.2.45, p. 280, from the original
    supremum laws of 2.10.1, p. 170. The
    proved reciprocal cutoffs are cofinal among every
    positive finite or infinite original cutoff. Their
    pointwise supremum is therefore the original measure,
    including empty targets and infinite mass. *)
Theorem caratheodory_reciprocal_cutoff_supremum (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (mu : set X -> \bar R) (A : set X) :
  is_caratheodory_limit S c mu ->
  is_extended_real_supremum
    ((fun n : nat => metric_scale_envelope S c (((n.+1)%:R : R)^-1)%R%:E A) @` setT) (mu A).
Proof.
move=> hMu; constructor.
- move=> z [n _ <-].
  exact: (@caratheodory_limit_upper R X J S c mu hMu A _ _
    (@reciprocal_metric_cutoff_positive R n) (metric_scale_envelope_specification _ _ _)).
- move=> b hB; apply: (caratheodory_limit_least hMu)=> delta nu hDelta hNu.
  have [n hCutoff] := reciprocal_metric_cutoffs_cofinal hDelta.
  have h := @metric_scale_envelope_antitone_cutoff R X J S c
    (((n.+1)%:R : R)^-1)%R%:E delta _ nu (metric_scale_envelope_specification _ _ _) hNu hCutoff A.
  apply: le_trans h _; apply: hB; by exists n.
Qed.
