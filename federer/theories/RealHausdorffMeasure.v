(** Federer 2.10.2, p. 171: Hausdorff and spherical measures in every
    nonnegative real dimension, with the actual Gamma normalization.
    Independent covering specifications precede the public values; values
    use only the sealed, already constructed covering objects. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealHausdorffNormalisation RealPowerCoverVariants
  MetricRealPowerCost MetricRealPowerMeasureUP MetricRealPowerMeasure
  MetricRealPowerClosedCovers RealPowerNaturalHausdorff HausdorffMeasureUP
  HausdorffMeasure HausdorffCountingMeasure CountingMeasure
  CaratheodoryLimitUP CaratheodoryLimitUniqueness MeasureUP BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_real_hausdorff_measure]: Federer 2.10.2(1), p. 171;
    all nonempty generators, actual diameter, real degree and Gamma cost. *)
Definition is_real_hausdorff_measure (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R) (mu:set X->\bar R):Prop:=
  is_metric_real_power_measure (real_hausdorff_normalisation hp) p mu.

(** Source for [is_real_spherical_measure]: Federer 2.10.2(2), p. 171;
    independently specified positive-radius closed-ball generators. *)
Definition is_real_spherical_measure (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R) (mu:set X->\bar R):Prop:=
  is_spherical_metric_real_power_measure (real_hausdorff_normalisation hp) p mu.

(** Source for [real_hausdorff_measure]: Federer 2.10.2(1), p. 171;
    public Gamma-normalized value of the sealed unrestricted measure. *)
Definition real_hausdorff_measure (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R):=
  @metric_real_power_measure R X (real_hausdorff_normalisation hp) p.

(** Source for [real_spherical_measure]: Federer 2.10.2(2), p. 171;
    public Gamma-normalized value of the sealed closed-ball construction. *)
Definition real_spherical_measure (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R):=
  @spherical_metric_real_power_measure R X (real_hausdorff_normalisation hp) p.

(** Source for [real_hausdorff_measure_specification]: Federer 2.10.2(1),
    p. 171; the actual real-dimensional measure satisfies its stated laws. *)
Lemma real_hausdorff_measure_specification (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R):
  is_real_hausdorff_measure hp (@real_hausdorff_measure R X p hp).
Proof. exact:metric_real_power_measure_specification. Qed.

(** Source for [real_spherical_measure_specification]: Federer 2.10.2(2),
    p. 171; the spherical measure satisfies its independently stated laws. *)
Lemma real_spherical_measure_specification (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R):
  is_real_spherical_measure hp (@real_spherical_measure R X p hp).
Proof. exact:spherical_metric_real_power_specification. Qed.

(** Source for [real_hausdorff_measure_is_measure]: Federer 2.10.2(1),
    p. 171; the real-dimensional Hausdorff object is a measure. *)
Lemma real_hausdorff_measure_is_measure (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R):is_measure (@real_hausdorff_measure R X p hp).
Proof. apply:metric_real_power_measure_is_measure; exact:ltW (real_hausdorff_normalisation_positive hp). Qed.

(** Source for [real_hausdorff_measure_borel_regular]: Federer 2.10.2(1),
    p. 171; Borel regularity follows from closed-cover replacement. *)
Lemma real_hausdorff_measure_borel_regular (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R):is_borel_regular_measure (@real_hausdorff_measure R X p hp).
Proof. apply:metric_real_power_measure_borel_regular; exact:ltW (real_hausdorff_normalisation_positive hp). Qed.

(** Source for [real_hausdorff_measure_natural]: Federer 2.10.2(1),
    p. 171, consistency with 3.2.13. Equality holds on every original set
    in every metric space, including infinite masses and natural degree zero. *)
Theorem real_hausdorff_measure_natural (R:realType) (X:metricType R)
    (m:nat) (hp:(0<=m%:R :> R)%R) (A:set X):
  @real_hausdorff_measure R X m%:R hp A=@hausdorff_measure R X m A.
Proof.
apply:(metric_real_power_measure_unique
  (@real_hausdorff_measure_specification R X m%:R hp)).
rewrite real_hausdorff_normalisation_natural.
apply:hausdorff_natural_real_power_laws; exact:hausdorff_measure_specification.
Qed.

(** Source for [real_hausdorff_zero_counting]: Federer 2.10.2(1), p. 171;
    the actual real-degree zero case is counting measure on arbitrary sets. *)
Theorem real_hausdorff_zero_counting (R:realType) (X:metricType R)
    (hp:(0<=0 :> R)%R) (A:set X):
  @real_hausdorff_measure R X 0 hp A=@counting_measure R X A.
Proof.
rewrite -[0%R]/(0%:R:R) real_hausdorff_measure_natural.
exact:hausdorff_zero_counting_measure.
Qed.
