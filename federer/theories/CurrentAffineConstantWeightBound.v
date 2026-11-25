(** Federer (1969), 4.1.14, p. 370: bound the original
    variation integrals in 4.1.13 by the uniform difference,
    the original K-only derivative cap and the finite masses.
    The variation stays on the original open source. Its
    concentration on the actual support is proved earlier. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentSpaces CurrentIntegrationCriterion CurrentRadonSupport
  CurrentMassSealed CurrentMassRepresentation NormalisedCurrentSealed
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  SummableRealFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralComparison
  MeasureIntegralUniqueness FiniteMeasureBoundedNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nonnegative_affine_weight_cap]: the elementary
    product bound used on the two original integrands in
    Federer 4.1.14, p. 370. Natural exponent zero and zero
    displacement or derivative cap are allowed. *)
Lemma nonnegative_affine_weight_cap (R : realType)
    (a b delta c : R) j :
  0<=a -> 0<=b -> 0<=delta -> 0<=c -> a<=delta -> b<=c ->
  a*b^+j<=delta*c^+j.
Proof.
move=> ha hb hDelta hc hA hB.
have hPower : b^+j<=c^+j by apply: lerXn2r; rewrite ?nnegrE.
have hPowerNonnegative : 0<=b^+j by exact: exprn_ge0 hb.
have hFirst : a*b^+j<=delta*b^+j := ler_wpM2r hPowerNonnegative hA.
have hSecond : delta*b^+j<=delta*c^+j := ler_wpM2l hDelta hPower.
exact: le_trans hFirst hSecond.
Qed.

Section OriginalVariationBound.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Variable T : @current_space R h2 n U hU m.
Hypothesis hT : @is_integration_representable_current R h2 n m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation support := (@current_support R h2 n U hU m T).
Local Notation hm := (distribution_representation_measure
  (normalised_distribution_representation_laws
    (@NormalisedCurrent.laws R h2 n m U hU T hT))).

(** Source for [current_original_variation_bounded_integral]: a
    weight bounded on the original current support has integral
    at most that bound times its finite mass, supporting
    Federer 4.1.14, p. 370, through 2.4.4(5), p. 82.
    No bound on the rest of U or extra integrability hypothesis
    on the weight is imposed. *)
Theorem current_original_variation_bounded_integral
    (mass bound : R) (w : UT -> R) :
  @CurrentMass.value R h2 n m U hU T=mass%:E ->
  (forall x, support (set_val x) -> w x<=bound) ->
  (measure_lower_integral mu (real_total_integrand w)<=
    (bound*mass)%R%:E)%E.
Proof.
move=> hMass hBound.
have hTotal : mu setT=mass%:E.
  by rewrite -(@current_represented_mass_total R h2 n m U hU T hT).
have hConstant := @finite_measure_constant_integral R UT mu hm
  mass bound hTotal.
have hAlmost : measure_almost_everywhere mu
    (partial_extended_le_locus (real_total_integrand w)
      (partial_function_total (fun _ : UT =>
        (bound%:E : extended_real_line R)))).
  apply: (@measure_almost_everywhere_mono R UT mu hm
    [set x | support (set_val x)] _ _
    (@current_radon_outside_support_null R h2 n m U hU T hT)).
  move=> x hx; exists (w x)%:E,bound%:E; split.
  - by apply/real_total_integrand_graph.
  - split; first by [].
    rewrite lee_fin; exact: hBound x hx.
have hComparison := @measure_lower_integral_monotone R UT mu hm
  (real_total_integrand w) _ hAlmost.
have hValue := @measure_lower_integral_unique R UT mu _ _ _
  (measure_lower_integral_specification mu _) hConstant.2.2.
by rewrite hValue in hComparison.
Qed.
End OriginalVariationBound.
