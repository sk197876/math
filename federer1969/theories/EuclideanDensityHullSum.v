(** Federer (1969), 3.2.41, printed p. 278, last proof sentence:
    the actual density-one hulls satisfy A*+B* subset (A+B)*.
    All independent hull laws used in the abstract additive argument
    are discharged for the existing Euclidean Lebesgue density. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals
  constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  CenteredBallRelations MeasureDensityPoints VectorSetSum IdempotentHullVectorSum
  EuclideanDensityOneHull EuclideanDensityOneTranslation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_density_one_hull_vector_sum]: direct
    last inclusion in Federer 3.2.41, p. 278. Original arbitrary
    nonmeasurable and unbounded sets are retained; no finite-volume
    premise or assertion of null hull excess is introduced. *)
Theorem euclidean_density_one_hull_vector_sum (R:realType) n
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))):
  let Leb:=@euclidean_lebesgue_measure R n in
  let V:=@centered_closed_ball_relation R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] in
  vector_set_sum (measure_density_one_points Leb V A) (measure_density_one_points Leb V B)
    `<=` measure_density_one_points Leb V (vector_set_sum A B).
Proof.
move=> Leb V.
apply:idempotent_translation_hull_vector_sum.
- move=> C D; exact:euclidean_density_one_hull_monotone.
- exact:euclidean_density_one_hull_idempotent.
- move=> a C; exact:euclidean_density_one_hull_translation.
Qed.
