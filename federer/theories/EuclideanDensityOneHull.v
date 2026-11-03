(** Federer (1969), 3.2.41, printed p. 278, final paragraph:
    the actual Euclidean density-one hull has the same outer
    volume as the original arbitrary set. No measurability,
    boundedness or finite-volume hypothesis is imposed on it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanNoncenteredVitali EuclideanClosedBallVolume EuclideanApproximateContext CenteredBallRelations
  MeasureUP MeasureDerivationContext DensityMeasurableSets MeasureDensityPoints
  DensityOneMeasureTests DensityOneIdempotence DensityOneMonotonicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section EuclideanDensityHull.
Variable R:realType.
Variable n:nat.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Leb:=(@euclidean_lebesgue_measure R n).
Local Notation V:=(@centered_closed_ball_relation R [the metricType R of E]).

(** Source for [euclidean_density_one_hull_measurable]: supporting
    measurability of S* in Federer 3.2.41, p. 278, by the
    existing complete Euclidean differentiation context and 2.9.11. *)
Lemma euclidean_density_one_hull_measurable (A:set E):
  measure_measurable Leb (measure_density_one_points Leb V A).
Proof.
exact:(@density_one_points_conclusions R [the metricType R of E] Leb V A
  (@euclidean_approximate_context R n)).1.
Qed.

(** Source for [euclidean_density_one_hull_equal_volume]: supporting
    equality of the original outer volume and the volume of S*
    in Federer 3.2.41, p. 278. Infinite values are retained. *)
Lemma euclidean_density_one_hull_equal_volume (A:set E):
  Leb A=Leb (measure_density_one_points Leb V A).
Proof.
exact:(@density_one_points_equal_measure R [the metricType R of E] Leb V A
  (@euclidean_approximate_context R n)).
Qed.

(** Source for [euclidean_density_one_hull_idempotent]: supporting
    exact pointwise idempotence used for the last inclusion in
    Federer 3.2.41, p. 278. No original-set measurability is added. *)
Lemma euclidean_density_one_hull_idempotent (A:set E):
  measure_density_one_points Leb V (measure_density_one_points Leb V A)=
    measure_density_one_points Leb V A.
Proof.
exact:(@density_one_points_idempotent R [the metricType R of E] Leb V A
  (@euclidean_approximate_context R n)).
Qed.

(** Source for [euclidean_density_one_hull_monotone]: supporting
    monotonicity used for A*+B* in Federer 3.2.41, p. 278.
    Actual positive-radius closed balls supply positive finite
    denominators in all natural ambient dimensions. *)
Lemma euclidean_density_one_hull_monotone (A B:set E):
  A `<=` B ->measure_density_one_points Leb V A `<=` measure_density_one_points Leb V B.
Proof.
apply:(@density_one_points_monotone R [the metricType R of E] Leb V A B
  (derivation_context_measure (@euclidean_approximate_context R n))).
move=> x S [r [hr ->]]; split; first exact:euclidean_closed_ball_positive hr.
by rewrite (euclidean_closed_ball_normalized_volume x (ltW hr)) fin_numE.
Qed.
End EuclideanDensityHull.
