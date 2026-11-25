(** Federer (1969), 3.1.24, p. 240: the explicit
    analytic scalar inverse proves existence and exponential
    boundedness of the inverse-majorant sequence. This witness
    module is private to its seal and the assumptions audit. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  SymmetricForms HomogeneousPolynomialFunctions NormAnalyticUP NormAnalyticBoundedTaylorForms ScalarAnalyticCoefficientBounds
  ScalarInverseMajorant ScalarMajorantCompositionCoefficients ScalarForwardMajorantDifferentials
  ScalarCoefficientForms ScalarCompositionCoefficient InverseCompositionScalarSum
  InverseMajorantUP InverseMajorantFromComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inverse_majorant_sequence_exists]: the existence
    of lambda_p and a finite c with lambda_p<=c^p in
    Federer 3.1.24, pp. 239–240. Take normalized
    actual derivatives of the printed quadratic scalar inverse.
    The exact composition calculation identifies its recurrence;
    analyticity gives the exponential bound. No recurrence or
    analytic inverse theorem is assumed to prove this witness. *)
Theorem inverse_majorant_sequence_exists (R:realType) (b g:R) :
  0<b -> 0<g -> exists lambda:nat->R,
    is_inverse_majorant_sequence b g lambda /\
    exists C:R,0<C /\ forall p,(1<=p)%N -> lambda p<=C^+p.
Proof.
move=>hb hg.
pose N:=fun t:R^o=>`|t|.
pose hN:=scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i R^o R^o N N hN hN.
pose ev i:=@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN.
pose ZN i:=@ContinuousMultilinear.norm R i R^o R^o N N hN hN.
pose A:=scalar_inverse_majorant_domain b.
pose F:=scalar_inverse_majorant b g.
have hf:=@scalar_inverse_majorant_analytic_zero R b g hb hg.
have [U [c [phi [hc [hU0 [hUA [hOpen [hphi [hNorm hTaylor]]]]]]]]]:=
  @norm_analytic_bounded_taylor_forms R R^o R^o N N hN hN A F 0 hf.
pose lambda m:=sform_polynomial_value (phi m) 1.
have h0:lambda 0%N=0.
  have hh:=@scalar_actual_zero_form_value R Z ev ZN A F 0 (phi 0%N) (hphi 0%N).
  rewrite /F (scalar_inverse_majorant_zero g hb) in hh; exact hh.
have hSum p (hp:(1<=p)%N):inverse_composition_scalar_sum b g lambda p=
    ScalarAffineDifferentials.scalar_affine_derivative_coefficient 1 0 p 0/(p`!)%:R.
  have hEq:=@scalar_majorant_composition_coefficient_identity R b g phi p hb hg hp hphi.
  have hValue:sform_polynomial_value (@CompositionFormCoefficient.composition_differential_form_coefficient
      R R^o R^o R^o p phi (fun i=>scalar_coefficient_form i (scalar_forward_majorant_coefficient b g i)) p) 1=
      inverse_composition_scalar_sum b g lambda p.
    rewrite (@scalar_composition_coefficient_value R (@pchar_num R) p phi
      (fun i=>scalar_coefficient_form i (scalar_forward_majorant_coefficient b g i)) p (leqnn p))
      /inverse_composition_scalar_sum.
    apply:eq_bigr=>a _; by rewrite scalar_coefficient_form_unit.
  by rewrite -hValue.
have hSeq:=@inverse_majorant_from_composition R b g lambda hb hg h0 hSum.
have [C [hC hBound]]:=@scalar_analytic_coefficients_exponential_bound R A F 0 phi hf hphi.
exists lambda; split; first exact hSeq.
exists C; split; first exact hC.
move=>p hp; exact (le_trans (ler_norm (lambda p)) (hBound p hp)).
Qed.
