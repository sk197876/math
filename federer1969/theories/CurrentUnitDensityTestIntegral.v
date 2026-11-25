(** Federer (1969), 4.1.7, p. 358:
    bounded multivector densities can be paired
    with every original test. This adapter uses
    the actual L1 pairing already proved in
    4.1.5, p. 350. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentDomain
  CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentMultivectorDual MultivectorDualSealed
  OpenFamilyTopologyMathcomp SmoothFunctionSpaceUP SmoothTestEvaluation DistributionVariationDomain
  DistributionSubspaceTestValues CompactContinuousVectorMeasurable RadonCompactScalarIntegral
  PartialFunctionBasic SummableRealFunctionUP MeasureUP RadonMeasureUP MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralGraphEquivalence AbstractDualPartialPairing AbstractUnitDualPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_unit_density_test_integral_finite]:
    every original test has a finite pairing
    integral against a weakly measurable unit-bounded
    density, supporting Federer 4.1.7, p. 358,
    by 4.1.5, p. 350. The Radon measure
    may have infinite total mass. *)
Theorem current_unit_density_test_integral_finite (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (mu:set (current_domain R n U)->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (w:current_domain R n U->exterior_power (R_n R n) m):
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(w x:open_family_topological_space
      (@current_multivector_weak_laws R n m).1))) ->
  (forall x,@current_vector_mass R h2 n m (w x)<=1) ->
  forall psi:@current_test_space R h2 n U hU m,exists c:R,
    is_measure_integral mu (real_total_integrand (fun x=>@MultivectorDual.evaluation R (R_n R n) m (w x)
      (@current_test_value R h2 n U hU m psi (set_val x)))) c%:E.
Proof.
move=>hW hUnit psi.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose Y:=A_m X R^o m.
pose NY:=@current_form_comass R h2 n m.
pose hNY:=@current_form_comass_real_norm R h2 n m.
pose V:=exterior_power X m.
pose VN:=@current_vector_mass R h2 n m.
pose ed:=@MultivectorDual.evaluation R X m.
pose UT:=current_domain R n U.
pose hE:=@current_smooth_space_laws R h2 n U hU m.
pose dvalues:=@distribution_domain_values R (real_norm_metric_space hNX) U Y
  (@current_test_space R h2 n U hU m) (smooth_test_values_hom hE).
pose F:=@radon_positive_compact_integral R UT mu hm hr.
have hF:=@radon_positive_compact_integral_laws R UT mu hm hr.
have hTest:=@smooth_test_original_continuous_field R X Y NX NY hNX hNY U
  (@current_smooth_space R h2 n U hU m) (@current_smooth_value R h2 n U hU m) hE psi.
have hLone:=@compact_continuous_vector_lone_member R UT Y NY hNY
  (@current_form_separable R h2 n m) mu hm hr F hF (dvalues psi) hTest.
have [_ [c [hIntegral _]]]:=@abstract_unit_dual_pairing_summable R UT Y NY hNY
  (@current_form_separable R h2 n m) V ed VN (@current_multivector_continuous_dual R h2 n m)
  (@current_multivector_weak_opens R n m) (@current_multivector_weak_laws R n m)
  mu hm w hW hUnit _ hLone.
exists c; exact:(measure_integral_graph_equivalent
  (@abstract_dual_partial_pairing_total_graph R UT Y V ed w (dvalues psi)) hIntegral).
Qed.
