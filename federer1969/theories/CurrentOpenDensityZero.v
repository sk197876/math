(** Federer (1969), 4.1.26, pp. 383–384:
    a zero density current has zero density
    almost everywhere. This supplies the scalar
    inference after the original constancy theorem.
    Reuse the all-set variation formula of
    4.1.7 and the earlier zero upper-integral
    theorem; no bounded density is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentCoefficientNorms CurrentDomain CurrentSpaces
  CurrentIntegrationCriterion OpenCurrentDensityUP OpenCurrentDensitySealed
  CurrentDensityVariation CurrentMassSealed CurrentMassRepresentation CurrentMassFiniteAlgebra
  NormalisedCurrentSealed RadonMeasureUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureDensity MeasureSubsetIntegral MeasureIntegralUP MeasureIntegralBounds MeasureBoundGraphEquivalence
  PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionality
  PartialZeroExtension PartialZeroExtensionLaws ExtendedRealOrderTopology
  SummableRealFunctionUP ZeroUpperIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_open_density_zero_almost]: the
    original Radon density is determined almost
    everywhere by its current action, supporting
    the degree constancy conclusion in 4.1.26,
    pp. 383–384. Arbitrary local summability suffices;
    finite total mass is derived from zero. *)
Theorem current_open_density_zero_almost (R:realType)
    (h2:(1+1:R)!=0) n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (gamma:set (current_domain R n U)->\bar R)
    (hGamma:is_measure gamma) (hRadon:is_radon_measure gamma)
    (xi:current_domain R n U->exterior_power (R_n R n) m)
    (hField:@is_locally_integrable_open_current_density R h2 n m U gamma xi):
  @OpenCurrentDensity.value R h2 n m U hU gamma hGamma hRadon xi hField=0->
  measure_almost_everywhere gamma [set x|xi x=0].
Proof.
move=>hZero.
pose UT:=current_domain R n U.
pose T:=@OpenCurrentDensity.value R h2 n m U hU gamma hGamma hRadon xi hField.
pose VN:=@current_vector_mass R h2 n m.
pose H:=real_total_integrand (fun x=>VN (xi x)).
pose lambda:=measure_with_density gamma H.
pose hRepresentation:=@current_open_density_representable
  R h2 n m U hU gamma hGamma hRadon xi hField.
have hVariation:=@current_open_density_variation
  R h2 n m U hU gamma hGamma hRadon xi hField hRepresentation.
have hTotal:=@current_represented_mass_total R h2 n m U hU T hRepresentation.
rewrite hVariation in hTotal.
change (@CurrentMass.value R h2 n m U hU T=lambda setT) in hTotal.
have hLambdaZero:lambda setT=0%E by rewrite -hTotal /T hZero current_mass_zero.
have hExtension:partial_function_zero_extension (0:extended_real_line R) setT H=H.
  apply:partial_function_graph_extensionality=>x z.
  exact:partial_zero_extension_whole_graph.
have hUpper:measure_upper_integral gamma H=0%E.
  have hValue:=@measure_with_density_laws R UT gamma H setT.
  rewrite /measure_subset_upper_integral hExtension in hValue.
  by rewrite -hValue.
pose w:=fun x:UT=>((VN (xi x))%:E:extended_real_line R).
have hWUpper:measure_upper_integral gamma (partial_function_total w)=0%E.
  rewrite -hUpper;apply:measure_upper_integral_graph_equivalent=>x z.
  exact:iff_sym (@real_total_integrand_graph R UT (fun x=>VN (xi x)) x z).
have hPositive:forall x:UT,(0<=w x)%E.
  move=>x;rewrite /w lee_fin.
  exact:real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 n m).1 (xi x).
have hAlmost:=@nonnegative_zero_upper_integral_almost_zero
  R UT gamma hGamma w hPositive hWUpper.
apply:(@measure_almost_everywhere_mono R UT gamma hGamma _ _ _ hAlmost)=>x hx.
have hNorm:VN (xi x)=0:=EFin_inj hx.
exact:(@current_vector_mass_real_norm R h2 n m).2 (xi x) hNorm.
Qed.
