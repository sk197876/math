(** Federer (1969), 2.9.24, p. 169: cell integration and the finite
    telescoping identity give the exact integral values for f_n g'. This
    calculation does not assume f continuous. its second finite sum has the
    endpoint misprint documented in IntegrationByPartsFiniteIdentity.v. The
    local Federer erratum has no entry. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CurveArcLength MeasureIntegralUP
  SummableRealFunctionUP LebesgueScalarMeasure RealAbsoluteContinuityUP
  RealDerivativeRepresentative ACDerivativePrimitiveDensity TaggedStepPrimitiveIntegral
  StieltjesSums StieltjesIntegral StieltjesSubstitution StieltjesIntegrationByParts
  RightStepApproximation IntegrationByPartsFiniteIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [right_step_derivative_integral]: direct cell-sum
    integral calculation for f_n g' in Federer 2.9.24,
    p. 169, with a proof representative of g'. The
    actual partial derivative is restored after bounded convergence. *)
Lemma right_step_derivative_integral (R : realType) (f g : R -> R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) -> a<b ->
  is_absolutely_continuous_real_curve g a b -> forall n : nat,
  is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (fun x => uniform_right_step_approximation f a b n x*
      real_derivative_representative g x))
    (stieltjes_sum f g (uniform_right_tagged a ((b-a)/n.+1%:R) n.+1))%:E.
Proof.
move=> hg hab hAC n.
have hcell := @absolutely_continuous_derivative_primitive_density R g a b hg hab hAC.
have hw := @uniform_right_tagged_is R a b n (ltW hab).
apply: (@tagged_step_primitive_integral R g (real_derivative_representative g)
  a b hcell f _ hw.1)=> t ht.
exact: (@tagged_partition_mem_bounds R a b _ t hw ht).
Qed.

(** Source for [right_step_integration_by_parts_integral]: direct
    finite identity for the integral in Federer 2.9.24,
    p. 169: integral f_n g' equals the boundary product
    difference minus the left-tagged Stieltjes sum of g against f. *)
Lemma right_step_integration_by_parts_integral (R : realType) (f g : R -> R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) -> a<b ->
  is_absolutely_continuous_real_curve g a b -> forall n : nat,
  is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (fun x => uniform_right_step_approximation f a b n x*
      real_derivative_representative g x))
    (f b*g b-f a*g a-stieltjes_sum g f (uniform_partition a b n))%:E.
Proof.
move=> hg hab hAC n.
have hi := @right_step_derivative_integral R f g a b hg hab hAC n.
have htel := @integration_by_parts_uniform_identity R f g a b n.
have he : stieltjes_sum f g (uniform_right_tagged a ((b-a)/n.+1%:R) n.+1)=
    f b*g b-f a*g a-stieltjes_sum g f (uniform_partition a b n) by lra.
by rewrite he in hi.
Qed.
