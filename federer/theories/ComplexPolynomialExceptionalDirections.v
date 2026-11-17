(** Federer (1969), 3.4.12, p. 339, extending 3.4.7,
    p. 324: both exceptional-direction sets of a nonzero
    complex-valued homogeneous polynomial are null. Reuse the
    real polynomial and radial sphere theorems through an
    actual nonzero real or imaginary homogeneous component. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric PolynomialFunctions HomogeneousPolynomialFunctions ComplexHomogeneousScalarisation
  EuclideanLebesgueDimensions EuclideanPolynomialNull EuclideanPolynomialSphereNull
  HausdorffMeasure MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [complex_polynomial_exceptional_directions_null]: the
    original ambient and unit-sphere nullity in real coordinates,
    3.4.12, p. 339. Zero dimension and degree zero remain. *)
Theorem complex_polynomial_exceptional_directions_null (R:realType) n k
    (P:R_n R n->restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o):
  is_homogeneous_polynomial k P ->(exists v,P v<>0) ->
  @euclidean_lebesgue_measure R n [set v|P v=0] = 0%:E /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (n-1)
    [set v|P v=0 /\inner_norm (@euclidean_inner_productP R n) v= 1] = 0%:E.
Proof.
move=>hP hNonzero.
have [Q [hQ [hNonzeroQ hZeros]]]:=complex_homogeneous_scalarisation hP hNonzero.
split.
- apply:(@measure_null_subset R (Choice.clone (R_n R n) _) (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) [set v|P v=0] [set v|Q v=0]);last
    exact:euclidean_polynomial_zero_set_null hNonzeroQ.
  exact:hZeros.
- apply:(@measure_null_subset R (Choice.clone (inner_metric_space (@euclidean_inner_productP R n)) _)
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (n-1))
    (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) (n-1))
    [set v|P v=0 /\inner_norm (@euclidean_inner_productP R n) v= 1]
    [set v|Q v=0 /\inner_norm (@euclidean_inner_productP R n) v= 1]);last
    exact:euclidean_homogeneous_polynomial_unit_sphere_null hQ hNonzeroQ.
  move=>v [hv hUnit];split;[exact:hZeros v hv|exact:hUnit].
Qed.
