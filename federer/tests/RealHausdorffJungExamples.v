(** Boundary regressions for the original real-degree comparison in
    Federer 2.10.42, p. 201. Include the line, degree zero in every
    ambient dimension, and positive degree in ambient dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RealPower
  RealHausdorffMeasure RealHausdorffMeasureLaws RealHausdorffJungComparison
  JungConstant MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_jung_line_measure_equality]: regression for the
    n=1 endpoint of Federer 2.10.42, p. 201. The printed coefficient
    is one, so the actual spherical and Hausdorff measures agree on
    every subset of the Euclidean line in every nonnegative real degree. *)
Theorem real_jung_line_measure_equality (R : realType) (p : R)
    (hp : (0<=p)%R)
    (A : set (inner_metric_space (@euclidean_inner_productP R 1))) :
    @real_spherical_measure R _ p hp A=@real_hausdorff_measure R _ p hp A.
Proof.
have hb := @positive_euclidean_real_spherical_jung_comparison R 0 p hp A.
rewrite jung_factor_line real_power_one_base mul1e in hb.
apply/eqP; rewrite eq_le hb /=.
exact: real_hausdorff_le_spherical.
Qed.

(** Source for [real_jung_zero_degree_regression]: degree-zero
    regression for Federer 2.10.42, p. 201. The coefficient stays one
    even when the ambient space is zero-dimensional. The canonical
    spherical and Hausdorff counting conventions agree on every set. *)
Theorem real_jung_zero_degree_regression (R : realType) n
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
    @real_spherical_measure R _ 0%R (lexx (0%R : R)) A=
      @real_hausdorff_measure R _ 0%R (lexx (0%R : R)) A.
Proof.
have hb := @federer_2_10_42_real_degree R n 0%R (lexx (0%R : R)) A.
rewrite mul0r real_power_zero_exponent mul1e in hb.
apply/eqP; rewrite eq_le hb /=.
exact: real_hausdorff_le_spherical.
Qed.

(** Source for [real_jung_zero_ambient_positive_degree]: zero-ambient
    regression for Federer 2.10.42, p. 201. Its printed coefficient is
    zero in every positive real degree, and the spherical measure of
    every subset of the zero-dimensional Euclidean space is zero. *)
Theorem real_jung_zero_ambient_positive_degree (R : realType) (p : R)
    (hp : (0<=p)%R)
    (A : set (inner_metric_space (@euclidean_inner_productP R 0))) :
    (0<p)%R -> @real_spherical_measure R _ p hp A=0.
Proof.
move=> hpp.
have hb := @federer_2_10_42_real_degree R 0 p hp A.
have hhalf : (0<p/2)%R by rewrite divr_gt0 // ltr0n.
rewrite mulr0 mul0r (real_power_zero_base (lt0r_neq0 hhalf)) mul0e in hb.
apply/eqP; rewrite eq_le hb /=.
exact: (@measure_nonnegative R _ _ (@real_spherical_measure_is_measure R _ p hp) A).
Qed.
