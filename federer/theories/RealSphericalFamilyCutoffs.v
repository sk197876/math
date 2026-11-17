(** Federer (1969), 2.10.27, p. 190: supporting cutoff limits for the masses
    of sections, following the last step of 2.10.25, p. 189. Apply the
    existing sealed Hausdorff covering-infimum operator to any family of
    sets, and derive monotonicity and supremum from its abstract laws. No
    family measurability is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation
  RealHausdorffMeasureLaws MetricRealPowerCost RealPower RealPowerNaturalHausdorff
  MetricDiameterMaps RealHausdorffFibreCost RealHausdorffFibreCutoffs
  RealHausdorffProperWeighted RealHausdorffWeightedSigmaFinite ExtendedRealOrderTopology ExtendedRealBoundsUP MetricScaleEnvelopeUP
  MetricScaleEnvelope MetricScaleEnvelopeLaws HausdorffLengthUP HausdorffDiameterCost
  HausdorffMeasureUP HausdorffMeasure CaratheodoryLimitUP CaratheodoryBorelRegular HausdorffFibreCutoffs.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_spherical_set_family_cutoff]: supporting
    reciprocal-cutoff masses of sections in 2.10.27,
    p. 190, through the cutoff argument of
    2.10.25, p. 189. This applies an existing
    opaque operator and does not construct a new measure. *)
Definition real_spherical_set_family_cutoff (R : realType) (I : Type) (Z : metricType R)
    (F : I -> set Z) (k : R) (hk : (0<=k)%R) (n : nat) (i : I) : extended_real_line R :=
  @metric_scale_envelope R Z (@positive_closed_metric_balls R Z) (fun j=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (val j)) ((n.+1%:R : R)^-1)%R%:E (F i).

(** Source for [real_spherical_set_family_cutoff_nonnegative]:
    supporting nonnegative section integrands for
    2.10.27, p. 190, from the infimum laws
    of 2.10.1, p. 170. *)
Lemma real_spherical_set_family_cutoff_nonnegative (R : realType) (I : Type) (Z : metricType R)
    (F : I -> set Z) (k : R) (hk : (0<=k)%R) n i : 0<=real_spherical_set_family_cutoff F hk n i.
Proof.
rewrite /real_spherical_set_family_cutoff.
exact: (@metric_scale_envelope_nonnegative R Z _ _ _ _ _
  (metric_scale_envelope_specification _ _ _) (F i)).
Qed.

(** Source for [real_spherical_set_family_cutoffs_increasing]:
    supporting increasing cutoff approximants for the
    section estimate 2.10.27, p. 190, following
    the proof of 2.10.25, p. 189. *)
Lemma real_spherical_set_family_cutoffs_increasing (R : realType) (I : Type) (Z : metricType R)
    (F : I -> set Z) (k : R) (hk : (0<=k)%R) n m : (n<=m)%N -> forall i,
  real_spherical_set_family_cutoff F hk n i<=real_spherical_set_family_cutoff F hk m i.
Proof.
move=> hnm i.
exact: (@metric_scale_envelope_antitone_cutoff R Z (@positive_closed_metric_balls R Z)
  (fun j=>val j) (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (val j)) ((m.+1%:R : R)^-1)%R%:E
  ((n.+1%:R : R)^-1)%R%:E _ _ (metric_scale_envelope_specification _ _ _)
  (metric_scale_envelope_specification _ _ _) (@fibre_reciprocal_cutoff_antitone R n m hnm) (F i)).
Qed.

(** Source for [real_spherical_set_family_cutoffs_supremum]: supporting
    recovery of section masses in 2.10.27, p. 190,
    from the limit used in 2.10.25, p. 189.
    The abstract supremum includes infinite masses. *)
Theorem real_spherical_set_family_cutoffs_supremum (R : realType) (I : Type) (Z : metricType R)
    (F : I -> set Z) (k : R) (hk : (0<=k)%R) i :
  is_extended_real_supremum ((fun n=>real_spherical_set_family_cutoff F hk n i) @` setT)
    (@real_spherical_measure R Z k hk (F i)).
Proof.
pose S := fun j : @positive_closed_metric_balls R Z=>val j.
pose c := fun j : @positive_closed_metric_balls R Z=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (val j).
have hpsi := @real_spherical_measure_specification R Z k hk.
constructor.
- move=> z [n _ <-].
  exact: (@caratheodory_limit_upper R Z _ S c (@real_spherical_measure R Z k hk) hpsi
    (F i) _ _ (@reciprocal_metric_cutoff_positive R n) (metric_scale_envelope_specification _ _ _)).
- move=> b hb; apply: (caratheodory_limit_least hpsi)=> delta nu hd hn.
  have [n hcut] := reciprocal_metric_cutoffs_cofinal hd.
  have hh := @metric_scale_envelope_antitone_cutoff R Z _ S c
    ((n.+1%:R : R)^-1)%R%:E delta _ nu (metric_scale_envelope_specification _ _ _) hn hcut (F i).
  apply: le_trans hh _; apply: hb; by exists n.
Qed.
