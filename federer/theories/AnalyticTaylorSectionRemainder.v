(** Supporting Federer (1969), 3.4.8(5), p. 328:
    the remainder of the actual original finite Taylor polynomial
    belongs to the corresponding original vanishing-ideal power.
    Reuse exact interpolation, scalar linearity and the proved jet kernel. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  RingScalarRestriction AnalyticScalarsSealed AnalyticGermRing AnalyticVanishingIdealSealed
  CommutativeIdealPowersSealed PolynomialFunctions FiniteJetDegreeIndices
  AnalyticPolynomialGermUP AnalyticTaylorSectionUP AnalyticFiniteCoefficientsUP
  AnalyticFiniteCoefficientsLinear AnalyticFiniteCoefficientsKernel AnalyticTaylorSectionInterpolation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_finite_taylor_remainder_power]: supporting
    original quotient dimension comparison for Federer 3.4.8(5), p. 328.
    Subtracting the exact finite Taylor polynomial removes every
    derivative below l; the original ideal-power kernel gives the result. *)
Theorem analytic_finite_taylor_remainder_power (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e) l
    (J:PolynomialFunction X R^o->@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)
    (T:{ffun finite_jet_degree_indices n l->R^o}->@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)
    (f:@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0->{ffun finite_jet_degree_indices n l->R^o}):
  is_analytic_polynomial_germ_map J ->is_analytic_finite_taylor_section he J T ->
  is_analytic_finite_coefficient_map e f ->forall z,
  @CommutativeIdealPowers.value
    [the comNzRingType of (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)]
    (@AnalyticVanishingIdeal.value R X (inner_norm hB) (inner_norm_real_norm hB) 0) l
    (z-T (f z)).
Proof.
move=>hJ hT hF z.
apply:(@finite_analytic_coefficient_power_kernel R X (inner_norm hB)
  (inner_norm_real_norm hB) n e he l 0 f hF _).1.
have hLinear:=@analytic_finite_coefficient_linear R X (inner_norm hB)
  (inner_norm_real_norm hB) n e l 0 f hF.
pose V:=[the lmodType R of ring_restricted_space
  (@AnalyticScalars.map R X (inner_norm hB) (inner_norm_real_norm hB) 0)
  (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)^o].
pose W:=[the lmodType R of {ffun finite_jet_degree_indices n l->R^o}].
pose F:{linear V->W}:=HB.pack f (GRing.isLinear.Build R V W *:%R f hLinear).
change (F (z-T (f z)) = 0).
rewrite linearB.
change (f z-f (T (f z)) = 0).
rewrite (@analytic_finite_taylor_section_interpolation R X B hB n e he l J hJ T hT f hF).
exact:subrr.
Qed.
