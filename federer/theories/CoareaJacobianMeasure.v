(** Federer (1969), 3.2.11, p. 249: the target-degree Jacobian
    integral over a set is a measure, by 2.4.10,
    p. 85. This is the existing opaque density measure;
    equality with the fibre integral is proved later. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanTargetJacobianMeasurable LipschitzUP
  ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP PartialExtendedOrderLoci MeasureIntegralUP MeasureSubsetIntegral
  MeasureDensityUP MeasureDensity MeasureDensityNullSets DensityCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_euclidean_coarea_measure]: the measure
    with density J_n f in the partition argument of Federer
    3.2.11, p. 249, specified by the abstract subset
    upper-integral law of 2.4.10, p. 85. *)
Definition is_euclidean_coarea_measure (R:realType) m n
    (f:R_n R m->R_n R n) (nu:set (R_n R m)->\bar R):=
  is_measure_density (@euclidean_lebesgue_measure R m) (extended_euclidean_target_jacobian f) nu.

(** Source for [euclidean_coarea_measure]: the density
    measure used in Federer 3.2.11, p. 249. Reuse
    the existing opaque witness of 2.4.10; no new choice
    or construction is exposed. *)
Definition euclidean_coarea_measure (R:realType) m n (f:R_n R m->R_n R n):=
  measure_with_density (@euclidean_lebesgue_measure R m) (extended_euclidean_target_jacobian f).

(** Source for [euclidean_coarea_measure_laws]: the
    defining subset-integral law for the Jacobian density
    measure used in Federer 3.2.11, p. 249. *)
Lemma euclidean_coarea_measure_laws (R:realType) m n (f:R_n R m->R_n R n):
  is_euclidean_coarea_measure f (euclidean_coarea_measure f).
Proof. exact:measure_with_density_laws. Qed.

(** Source for [euclidean_coarea_jacobian_nonnegative_almost]: the
    nonnegative conull integrand used in Federer 3.2.11,
    p. 249. Rademacher supplies the actual domain. *)
Lemma euclidean_coarea_jacobian_nonnegative_almost (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  is_metric_lipschitz setT f ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    (partial_extended_nonnegative_locus (extended_euclidean_target_jacobian f)).
Proof.
move=>hLip; have hJ:=extended_euclidean_target_jacobian_measurable hLip.
apply:(@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R m) _ _ _
  (measurable_function_domain hJ))=>x [j hj].
exists j; split; first exact hj; exact (extended_euclidean_target_jacobian_nonnegative hj).
Qed.

(** Source for [euclidean_coarea_measure_is_measure]:
    the countably additive Jacobian measure in the partition
    argument of Federer 3.2.11, p. 249. *)
Theorem euclidean_coarea_measure_is_measure (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  is_metric_lipschitz setT f -> is_measure (euclidean_coarea_measure f).
Proof.
move=>hLip; exact (measure_with_density_is_measure (euclidean_lebesgue_is_measure R m)
  (euclidean_coarea_jacobian_nonnegative_almost hLip)).
Qed.

(** Source for [euclidean_coarea_measure_measurable]:
    every Lebesgue-measurable subset remains measurable for
    the Jacobian measure used in Federer 3.2.11, p. 249. *)
Lemma euclidean_coarea_measure_measurable (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  measure_measurable (euclidean_coarea_measure f) A.
Proof.
move=>hLip hA; exact (measure_with_density_measurable (euclidean_lebesgue_is_measure R m)
  (euclidean_coarea_jacobian_nonnegative_almost hLip) hA).
Qed.

(** Source for [euclidean_coarea_measure_integral]: the
    Jacobian measure equals the actual subset integral,
    as used when summing the partition in Federer 3.2.11,
    p. 249. Infinite integral values are allowed. *)
Lemma euclidean_coarea_measure_integral (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  is_measure_subset_integral (@euclidean_lebesgue_measure R m) A (extended_euclidean_target_jacobian f)
    (euclidean_coarea_measure f A).
Proof.
move=>hLip hA.
exact (@measurable_density_subset_integral R _ _ _ (euclidean_lebesgue_is_measure R m)
  (extended_euclidean_target_jacobian f) A (euclidean_coarea_measure_laws f)
  (euclidean_coarea_jacobian_nonnegative_almost hLip) (extended_euclidean_target_jacobian_measurable hLip) hA).
Qed.

(** Source for [euclidean_coarea_measure_null]: the
    null-set reductions of Federer 3.2.11, p. 249,
    also hold for the Jacobian density measure. *)
Lemma euclidean_coarea_measure_null (R:realType) m n (f:R_n R m->R_n R n) A:
  euclidean_lebesgue_measure m A=0 -> euclidean_coarea_measure f A=0.
Proof.
move=>hA; exact (@measure_density_null_set R _ _ _ (euclidean_lebesgue_is_measure R m)
  (extended_euclidean_target_jacobian f) A (euclidean_coarea_measure_laws f) hA).
Qed.
