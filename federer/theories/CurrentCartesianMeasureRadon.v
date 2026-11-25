(** Federer (1969), 4.1.8, p. 361: the original
    product measure is Radon on the original open Euclidean
    product domain. Transport the already proved original
    Radon product through its actual coordinate homeomorphism. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentDomain CurrentDomainGeometry CurrentCartesianDomain
  MetricSubsetBackground MetricProductBackground RealMetricBackground
  MeasureUP ProductMeasure MeasureBijectionUP MeasurePushforward RadonMeasureUP
  HomeomorphismUP EquivariantPushforward RadonProperPushforward
  CurrentCartesianDomainMapsSealed CurrentCartesianDomainMapsLaws
  CurrentCartesianDomainRadonProduct CurrentCartesianMeasureSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section CurrentCartesianMeasureRadon.
Variable R:realType.
Variables m n:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation AT := [the metricType R of (metric_subset (A:set (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))))].
Local Notation BT := [the metricType R of (metric_subset (B:set (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))))].
Local Notation P := [the metricType R of (metric_product AT BT)].
Local Notation CT := [the metricType R of (metric_subset (AB:set (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R (m+n))))))].
Local Notation J := (@CartesianCurrentDomain.join R m n A B).
Local Notation D := (@CartesianCurrentDomain.split R m n A B).
Variables (alpha:set (current_domain R m A)->\bar R) (beta:set (current_domain R n B)->\bar R).
Hypothesis hAlpha:is_measure alpha.
Hypothesis hBeta:is_measure beta.
Local Notation lambda := (@CartesianCurrentMeasure.value R m n A B alpha beta hAlpha hBeta).

(** Source for [current_cartesian_measure_is_measure]: the
    original transported product satisfies the measure laws,
    supporting Federer 4.1.8, p. 361. *)
Lemma current_cartesian_measure_is_measure:is_measure lambda.
Proof. exact:(@CartesianCurrentMeasure.laws R m n A B alpha beta hAlpha hBeta).1. Qed.

(** Source for [current_cartesian_measure_bijection]: every set
    has its original product value under the actual coordinate
    bijection, supporting Federer 4.1.8, p. 361. *)
Lemma current_cartesian_measure_bijection:
  is_measure_bijection (product_measure hAlpha hBeta) lambda J D.
Proof. exact:(@CartesianCurrentMeasure.laws R m n A B alpha beta hAlpha hBeta).2. Qed.

(** Source for [current_cartesian_measure_radon]: the original
    product Radon measure is Radon on the actual original
    open Euclidean product domain, Federer 4.1.8, p. 361.
    Neither factor needs finite total mass. *)
Theorem current_cartesian_measure_radon:
  is_radon_measure alpha->is_radon_measure beta->is_radon_measure lambda.
Proof.
move=>hRA hRB.
have hProduct:=@current_domain_radon_product R m n A B hA hB alpha beta hAlpha hBeta hRA hRB.
have hHomeo:=@current_cartesian_domain_homeomorphism R m n A B.
have hRadon:=@proper_continuous_radon_pushforward R P CT (product_measure hAlpha hBeta)
  (product_measure_is_measure hAlpha hBeta) hProduct J
  (@metric_hausdorff R CT) (@current_domain_locally_compact R (m+n) AB hAB)
  (@current_cartesian_domain_join_continuous R m n A B)
  (homeomorphism_with_inverse_proper hHomeo).
by rewrite (measure_bijection_pushforward current_cartesian_measure_bijection) in hRadon.
Qed.
End CurrentCartesianMeasureRadon.
