(** Federer (1969), 3.2.16, p. 254:
    the new notion generalizes the one in 3.1.2.
    This implication retains the older definition's
    actual base point and base value f(a). *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm RealNormUP NormMetric HilbertFormCompactness
  NormFiniteLinearBound NormDifferentialUP EuclideanLebesgueDimensions
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureUP MeasureRestriction MetricDensities MetricDensityZeroUnions
  ApproximateDifferentialUP ApproximateDifferentialRemainder
  EuclideanMetricZeroDensity MeasureApproximateAffineUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_approximate_differential_affine_criterion]:
    the corrected comparison with 3.1.2,
    Federer 3.2.16, p. 254 line 2;
    erratum p. 5. Every old approximate
    differential satisfies the new affine criterion
    with eta=f(a), using the actual restricted graph. *)
Theorem euclidean_approximate_differential_affine_criterion (R : realType) n
    (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY)
    (A : set (R_n R n)) (f : R_n R n -> Y)
    a (D : Hom (R_n R n) Y) :
  has_approximate_differential NY A f a D ->
  has_measure_approximate_affine_criterion NY
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@euclidean_lebesgue_measure R n) n
    (partial_function_source_restrict A (partial_function_total f)) a (f a) D.
Proof.
move=> hD.
pose NX := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
split.
- exact: (@norm_finite_linear_bounded R (R_n R n) Y NX NY hNX hNY n
    (@coordinate_basis R n) (@coordinate_basisP R n) D).
- move=> e he.
  have hOld := @approximate_remainder_exceptional_density R n Y NY hNY A f a D e hD he.
  have hNew := euclidean_relative_zero_metric_zero_density hOld.
  apply: (@metric_restricted_density_zero_subset R (real_norm_metric_space hNX) n
    (@euclidean_lebesgue_measure R n) _ (~` approximate_remainder_good_points NY A f a D e) a
    (euclidean_lebesgue_is_measure R n) _ hNew).
  move=> x hx hgood; apply: hx.
  have [hxA [_ herr]] := hgood.
  exists (f x); split; first by split.
  exact: ltW herr.
Qed.
