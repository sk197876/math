(** Federer (1969), 4.1.11, p. 365: the literal
    time integral of (1-t)^i t^j is i!j!/(i+j+1)!.
    The original interval fundamental theorem supplies
    the integral, including both zero exponents. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormDifferentialUP NormHigherCurveDerivativeUP
  NormClassOneUP ScalarUnitMixedPower ScalarBetaCoefficient ScalarBetaPrimitive
  RealClassOneSegmentIntegral RealMetricBackground LebesgueScalarMeasure
  MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_beta_moment]: the exact original
    mixed-power integral on [0,1], used in the equality
    of the two mass bounds in Federer 4.1.11, p. 365. *)
Theorem scalar_beta_moment (R:realType) i j:
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,1]
    (real_total_integrand (@scalar_unit_mixed_power R i j))
    (@scalar_beta_coefficient R i j)%:E.
Proof.
have [P [hD hEndpoints]]:=@scalar_beta_primitive_exists R i j.
have hIntegral:=@real_class_one_segment_integral R P (@scalar_unit_mixed_power R i j)
  0 1 ler01 hD (@scalar_unit_mixed_power_continuous R i j).
by rewrite hEndpoints in hIntegral.
Qed.
