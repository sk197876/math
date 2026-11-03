(** Federer 2.10.2, p. 171: the printed measure comparisons and
    covering alternatives for every nonnegative real dimension, now with
    the actual Gamma normalization. Use only independent covering laws
    and their proved generic real-power consequences. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealHausdorffNormalisation RealHausdorffMeasure
  RealPowerCoverVariants RealPowerOpenCovers RealPowerConvexCovers
  RealPowerSphericalComparison RealPowerOpenBallAgreement RealPowerDimensionDrop
  MetricRealPowerMeasure MetricRealPowerMeasureUP MetricRealPowerClosedCovers
  RealPowerNaturalHausdorff RealPower MetricRealPowerCost
  HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost HausdorffConvexCovers
  CaratheodoryLimitUP CaratheodoryLimitUniqueness CaratheodoryLimitMeasure MeasureUP
  RealNormUP NormMetric EuclideanInnerProduct InnerMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_spherical_measure_is_measure]: Federer 2.10.2(2),
    p. 171; the real-dimensional spherical covering object is a measure. *)
Lemma real_spherical_measure_is_measure (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R):is_measure (@real_spherical_measure R X p hp).
Proof.
apply:(caratheodory_limit_is_measure (@real_spherical_measure_specification R X p hp))=>S.
exact:metric_real_diameter_cost_ge0 (ltW (real_hausdorff_normalisation_positive hp)).
Qed.

(** Source for [real_hausdorff_closed_cover_equality]: Federer 2.10.2(1),
    p. 171; unrestricted and independently specified closed covers agree. *)
Theorem real_hausdorff_closed_cover_equality (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R) (A:set X):
  @real_hausdorff_measure R X p hp A=
    @closed_metric_real_power_measure R X (real_hausdorff_normalisation hp) p A.
Proof.
apply:metric_real_power_closed_measure_equality.
exact:ltW (real_hausdorff_normalisation_positive hp).
Qed.

(** Source for [real_hausdorff_open_cover_equality]: Federer 2.10.2(1),
    p. 171; final open and unrestricted measures agree. Fixed-cutoff
    equality is not asserted by this theorem. *)
Theorem real_hausdorff_open_cover_equality (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R) (A:set X):
  @real_hausdorff_measure R X p hp A=
    @open_metric_real_power_measure R X (real_hausdorff_normalisation hp) p A.
Proof.
exact:(metric_real_power_open_measure_equality
  (real_hausdorff_normalisation_positive hp) hp A).
Qed.

(** Source for [real_hausdorff_convex_cover_laws]: Federer 2.10.2(1),
    p. 171; the actual normalized measure satisfies convex-cover laws
    on every original normed space, without finite dimension. *)
Theorem real_hausdorff_convex_cover_laws (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (p:R) (hp:(0<=p)%R):
  @is_convex_metric_real_power_measure R V N hN
    (real_hausdorff_normalisation hp) p
    (@real_hausdorff_measure R (real_norm_metric_space hN) p hp).
Proof.
exact:(@metric_real_power_convex_cover_specification R V N hN
  (real_hausdorff_normalisation hp) p (real_hausdorff_normalisation_positive hp)).
Qed.

(** Source for [real_hausdorff_le_spherical]: Federer 2.10.2(2), p. 171;
    the first comparison H^p <= S^p holds on every set and metric space. *)
Theorem real_hausdorff_le_spherical (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R) (A:set X):
  @real_hausdorff_measure R X p hp A<=@real_spherical_measure R X p hp A.
Proof.
exact:(metric_real_power_le_spherical (real_hausdorff_normalisation_positive hp) hp A).
Qed.

(** Source for [real_spherical_le_double_hausdorff]: Federer 2.10.2(2),
    p. 171; S^p <= 2^p H^p with the actual real power and Gamma
    normalization. Zero diameters, zero degree and infinite masses remain. *)
Theorem real_spherical_le_double_hausdorff (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R) (A:set X):
  @real_spherical_measure R X p hp A<=
    (real_power 2 p)%:E*@real_hausdorff_measure R X p hp A.
Proof.
exact:(spherical_metric_real_power_le_double (real_hausdorff_normalisation_positive hp) hp A).
Qed.

(** Source for [real_euclidean_spherical_open_ball_equality]: Federer
    2.10.2(2), p. 171; Euclidean open-ball and closed-ball generators
    give the same normalized measure at every nonnegative real degree,
    including the zero-dimensional ambient space. *)
Theorem real_euclidean_spherical_open_ball_equality (R:realType) (n:nat)
    (p:R) (hp:(0<=p)%R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  @real_spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) p hp A=
    @open_ball_metric_real_power_measure R (inner_metric_space (@euclidean_inner_productP R n))
      (real_hausdorff_normalisation hp) p A.
Proof.
exact:(@euclidean_metric_real_power_open_ball_equality R n
  (real_hausdorff_normalisation hp) p (real_hausdorff_normalisation_positive hp) hp A).
Qed.

(** Source for [real_spherical_measure_natural]: Federer 2.10.2(2),
    p. 171; real and existing natural spherical measures agree with the
    same positive-radius convention on arbitrary original sets. *)
Theorem real_spherical_measure_natural (R:realType) (X:metricType R)
    (m:nat) (hp:(0<=m%:R :> R)%R) (A:set X):
  @real_spherical_measure R X m%:R hp A=@spherical_measure R X m A.
Proof.
have hr:=@real_spherical_measure_specification R X m%:R hp.
have hcost:(fun S:@positive_closed_metric_balls R X=>
    metric_real_diameter_cost (real_hausdorff_normalisation hp) m%:R (val S))=
    (fun S:@positive_closed_metric_balls R X=>hausdorff_diameter_cost m (val S)).
  apply:funext=>S; rewrite real_hausdorff_normalisation_natural.
  exact:real_power_natural_hausdorff_cost.
rewrite /is_real_spherical_measure /is_spherical_metric_real_power_measure hcost in hr.
exact:(caratheodory_limit_unique hr (@spherical_measure_specification R X m) A).
Qed.

(** Source for [real_hausdorff_finite_higher_degree_zero]: Federer
    2.10.2(1), p. 171; finite H^p mass implies H^q nullity for every
    nonnegative real p<q, without measurability, boundedness or separability. *)
Theorem real_hausdorff_finite_higher_degree_zero (R:realType) (X:metricType R)
    (p q:R) (hp:(0<=p)%R) (hq:(0<=q)%R) (A:set X):
  (p<q)%R -> @real_hausdorff_measure R X p hp A< +oo ->
    @real_hausdorff_measure R X q hq A = 0.
Proof.
move=>hpq; exact:(@metric_real_power_finite_higher_degree_zero R X
  (real_hausdorff_normalisation hp) (real_hausdorff_normalisation hq) p q
  (real_hausdorff_normalisation_positive hp)
  (real_hausdorff_normalisation_positive hq) hp hpq A).
Qed.
