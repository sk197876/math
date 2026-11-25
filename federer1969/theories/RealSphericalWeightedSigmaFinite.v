(** Federer (1969), 2.10.24(1), p. 187, and the spherical application on p.
    188. This is the sigma-finite-positive-support case, on an arbitrary
    metric space. The proper-space application without that assumption is
    separate; no Hausdorff-closedness of the ball family is used here. The
    erratum p. 4, book p. 188 line 21, corrects the script S notation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealHausdorffNormalisation RealHausdorffMeasure RealHausdorffMeasureLaws RealPowerCoverVariants MetricRealPowerCost
  RealHausdorffEnlargement RealSphericalEnlargement ExtendedRealOrderTopology PartialFunctionBasic MeasureIntegralBounds
  HausdorffMeasureUP HausdorffMeasure HausdorffDiameterCost SphericalEnlargementUP SphericalEnlargement
  WeightedMetricLimit WeightedSigmaFiniteEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_spherical_weighted_sigma_finite_equality]:
    real-degree spherical instance of 2.10.24(1),
    p. 187, for the measure mentioned on p. 188.
    Positive-radius closed balls retain zero-diameter
    and zero-cost possibilities. The only finite-mass
    cover required is that of the positive support. *)
Theorem real_spherical_weighted_sigma_finite_equality (R : realType) (X : metricType R) (p : R) (hp : (0<=p)%R)
    (f : X -> extended_real_line R) (A : nat -> set X) :
  (forall x, 0<=f x) -> (forall n, (@real_spherical_measure R X p hp) (A n)< +oo) ->
  [set x | 0<f x] `<=` \bigcup_n A n ->
  weighted_metric_limit (fun j : @positive_closed_metric_balls R X=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hp) p (val j)) (@real_spherical_measure R X p hp) f=
      measure_upper_integral (@real_spherical_measure R X p hp) (partial_function_total f).
Proof.
move=> hf hAfin hcover.
exact: (@weighted_metric_limit_sigma_finite_equality R X (@is_positive_metric_closed_ball R X)
  (@metric_real_diameter_cost R X (real_hausdorff_normalisation hp) p) (@real_spherical_measure R X p hp) (@spherical_enlargement R X 1)
  (@real_spherical_enlargement_control R p) _ f A (@real_spherical_enlargement_specification R X (real_hausdorff_normalisation hp) p (ltW (real_hausdorff_normalisation_positive hp)) hp)
  (@real_spherical_measure_specification R X p hp) (weighted_metric_limit_specification _ _ _)
  (fun S hS=>positive_metric_closed_ball_closed hS) hf hAfin hcover).
Qed.
