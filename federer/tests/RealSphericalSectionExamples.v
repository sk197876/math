(** Concrete endpoint tests for Federer 2.10.27, p. 191.
    Distinguish zero-degree and positive real-degree tangent costs,
    and retain the unit mass of the zero-dimensional base. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric EuclideanOneCoordinate EuclideanRealPlane RealMetricBackground
  EuclideanBallVolume EuclideanLebesgueDimensions RealHausdorffBallCoefficient
  RealPower RealEuclideanBallSectionProfileUP RealEuclideanBallSectionProfile
  RealBallSectionProfileIntegral RealEuclideanSphericalSections
  MeasureIntegralUP PartialFunctionBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [zero_degree_tangent_profile_regression]: a checked
    boundary test for the closed projected ball in Federer
    2.10.27, p. 191. The tangent profile has cost one
    at degree zero, so replacing the closed projection by its
    interior would change the actual pointwise profile. *)
Example zero_degree_tangent_profile_regression (R:realType) (hk:(0<=0:>R)):
  @real_euclidean_ball_section_profile R 1 0 hk 0 1 (euclidean_one_embed (1:R))= 1%E.
Proof.
pose x:=euclidean_one_embed (1:R).
have hd:mdist (0:inner_metric_space (@euclidean_inner_productP R 1)) x= 1.
  rewrite euclidean_one_project_distance /euclidean_one_project /x
    /euclidean_one_embed !ffunE real_line_metric_distanceE sub0r normrN normr1;by [].
have hp:=@real_euclidean_ball_section_profile_specification R 1 0 hk 0 1.
have hx:(mdist (0:inner_metric_space (@euclidean_inner_productP R 1)) x<= 1) by rewrite hd.
rewrite (real_ball_section_profile_inside hp hx) real_power_zero_exponent mulr1
  (@real_hausdorff_ball_coefficient_natural R 0 hk) euclidean_unit_ball_volume0;by [].
Qed.

(** Source for [positive_half_tangent_profile_regression]: concrete
    fractional-degree tangent test for Federer 2.10.27, p. 191.
    At degree 1/2 the same zero-radius section has cost zero. *)
Example positive_half_tangent_profile_regression (R:realType) (hk:(0<= 1/2:>R)):
  @real_euclidean_ball_section_profile R 1 (1/2) hk 0 1 (euclidean_one_embed (1:R))=0%E.
Proof.
pose x:=euclidean_one_embed (1:R).
have hd:mdist (0:inner_metric_space (@euclidean_inner_productP R 1)) x= 1.
  rewrite euclidean_one_project_distance /euclidean_one_project /x
    /euclidean_one_embed !ffunE real_line_metric_distanceE sub0r normrN normr1;by [].
have hp:=@real_euclidean_ball_section_profile_specification R 1 (1/2) hk 0 1.
have hx:(mdist (0:inner_metric_space (@euclidean_inner_productP R 1)) x<= 1) by rewrite hd.
have hHalf:(1/2:R)!=0 by apply:lt0r_neq0;lra.
by rewrite (real_ball_section_profile_inside hp hx) hd !expr1n subrr sqrtr0
  real_power_zero_base // mulr0.
Qed.

(** Source for [empty_base_zero_radius_profile_regression]: concrete
    simultaneous zero-base, zero-degree and zero-radius test of
    the full profile integral supporting Federer 2.10.27,
    p. 191. The actual integral equals one under the established
    Euclidean zero-dimensional point-mass convention. *)
Example empty_base_zero_radius_profile_regression (R:realType) (hk:(0<=0:>R)):
  is_measure_integral (@euclidean_lebesgue_measure R 0)
    (partial_function_total (fun y=>(@real_euclidean_ball_section_profile R 0 0 hk 0 0 y:
      extended_real_line R))) 1%E.
Proof.
have hi:=@real_euclidean_ball_section_profile_integral R 0 0 hk 0 0 (lexx 0).
have hAlpha:real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R 0))= 1.
  rewrite (@real_ball_coefficient_equal_degree R (0+0%:R) 0
    (addr_ge0 hk (ler0n R 0)) hk (addr0 0)).
  by rewrite (@real_hausdorff_ball_coefficient_natural R 0 hk) euclidean_unit_ball_volume0.
by rewrite hAlpha add0r real_power_zero_exponent mulr1 in hi.
Qed.
