(** Federer (1969), 4.1.7, p. 358:
    compare the bounded multivector densities in
    the exact variation proof. Actual test density
    gives agreement on compact scalar generators;
    the earlier scalar uniqueness theorem and the
    original finite covector basis identify the fields. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Annihilator FiniteCoordinates FiniteDualDimension Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms LinearBasis
  CurrentDomain CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces
  CurrentMultivectorDual MultivectorDualSealed ContinuousDualUP OpenFamilyTopologyMathcomp
  WeakEvaluationMeasurableCoordinates FunctionLatticeUP CompactSupportFunctionUP
  CompactContinuousVectorFields CompactContinuousVectorModule CompactContinuousVectorMeasurable
  VectorDaniellHypotheses PartialFunctionBasic SummableRealFunctionUP MeasureUP MeasureAlmostUP
  MeasurableFunctionUP TotalScalarMeasurability MeasureIntegralUP MeasureIntegralGraphEquivalence
  RadonMeasureUP RadonCompactScalarIntegral RadonLatticeLocalUniqueness RealLatticeDensityUP
  SmoothFunctionSpaceUP SmoothTestEvaluation DistributionVariationDomain DistributionIntegralFieldUP
  AbstractDualPartialPairing DualLoneIntegralSealed BoundedDualTestDensity
  LocallyNullMeasureUP LocallyAlmostMeasureLaws CountablyFiniteLocalNull
  SmoothDomainCompactOpenCover RadonCompactCoverCountablyMeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section BoundedCurrentDensityUniqueness.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation hDual := (@current_multivector_continuous_dual R h2 n m).
Local Notation O := (@current_multivector_weak_opens R n m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Local Notation hSep := (@current_form_separable R h2 n m).
Local Notation hY := (@current_form_complete R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Variable mu:set UT->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hr:is_radon_measure mu.
Variables a b:UT->V.
Hypothesis hA:is_measure_measurable_function mu
  (partial_function_total (fun x=>(a x:open_family_topological_space hO.1))).
Hypothesis hB:is_measure_measurable_function mu
  (partial_function_total (fun x=>(b x:open_family_topological_space hO.1))).
Hypothesis hAUnit:forall x,VN (a x)<=1.
Hypothesis hBUnit:forall x,VN (b x)<=1.
Variable S:Hom DT R^o.
Hypothesis hAAction:is_distribution_integral_action mu ed a dvalues S.
Hypothesis hBAction:is_distribution_integral_action mu ed b dvalues S.
Local Notation I := (@DualLoneIntegral.value R UT Y NY hNY hSep V ed VN hDual O hO mu hm a hA hAUnit).
Local Notation J := (@DualLoneIntegral.value R UT Y NY hNY hSep V ed VN hDual O hO mu hm b hB hBUnit).
Local Notation F := (@radon_positive_compact_integral R UT mu hm hr).
Local Notation hF := (@radon_positive_compact_integral_laws R UT mu hm hr).
Local Notation Kplus := (positive_function_lattice (@compactly_supported_continuous_functions R UT)).

(** Source for [bounded_current_density_locally_unique]:
    the actual bounded multivector densities of
    one current agree locally almost everywhere,
    supporting Federer 4.1.7, p. 358, by
    2.5.9, p. 100, and 4.1.5, p. 350. *)
Theorem bounded_current_density_locally_unique:
  measure_locally_almost_everywhere mu [set x|a x=b x].
Proof.
have hI:=@DualLoneIntegral.laws R UT Y NY hNY hSep V ed VN hDual O hO mu hm a hA hAUnit.
have hJ:=@DualLoneIntegral.laws R UT Y NY hNY hSep V ed VN hDual O hO mu hm b hB hBUnit.
have hEqual:=@bounded_dual_test_lone_integrals_equal R n Y NY hNY hY hSep U hU E ev hE
  V ed VN hDual O hO mu hm hr a b hA hB hAUnit hBUnit S hAAction hBAction.
have hModule:=@compact_continuous_vector_lattice_module R UT Y NY hNY.
have hCoordinate y:measure_locally_almost_everywhere mu [set x|ed (a x) y=ed (b x) y].
  pose A f:=I (partial_function_total (fun x:UT=>(f x*:y:real_norm_metric_space hNY))).
  have hLeft:is_real_lattice_density mu Kplus A (fun x=>ed (a x) y).
    split.
    - apply:(@real_total_scalar_measurable R UT mu hm).
      exact:(@weak_evaluation_measurable_coordinates R UT Y V (fun z y=>ed z y) O hO
        mu hm a hA y).
    - move=>f hf.
      have hW:=@vector_lattice_module_product R UT Y NY hNY
        (@compactly_supported_continuous_functions R UT)
        (@compact_continuous_vector_fields R UT Y NY hNY) hModule f y hf.1.
      have hLone:=@compact_continuous_vector_lone_member R UT Y NY hNY hSep mu hm hr F hF
        (fun x=>f x*:y) hW.
      have hIntegral:=measure_integral_graph_equivalent
        (@abstract_dual_partial_pairing_total_graph R UT Y V ed a (fun x=>f x*:y))
        (@hI _ hLone).
      have hPoint:(fun x=>ed (a x) (f x*:y))=(fun x=>f x*ed (a x) y).
        apply:funext=>x; exact:linearZ.
      by rewrite hPoint in hIntegral.
  have hRight:is_real_lattice_density mu Kplus A (fun x=>ed (b x) y).
    split.
    - apply:(@real_total_scalar_measurable R UT mu hm).
      exact:(@weak_evaluation_measurable_coordinates R UT Y V (fun z y=>ed z y) O hO
        mu hm b hB y).
    - move=>f hf.
      have hW:=@vector_lattice_module_product R UT Y NY hNY
        (@compactly_supported_continuous_functions R UT)
        (@compact_continuous_vector_fields R UT Y NY hNY) hModule f y hf.1.
      have hLone:=@compact_continuous_vector_lone_member R UT Y NY hNY hSep mu hm hr F hF
        (fun x=>f x*:y) hW.
      have hIntegral:=measure_integral_graph_equivalent
        (@abstract_dual_partial_pairing_total_graph R UT Y V ed b (fun x=>f x*:y))
        (@hJ _ hLone).
      have hPoint:(fun x=>ed (b x) (f x*:y))=(fun x=>f x*ed (b x) y).
        apply:funext=>x; exact:linearZ.
      rewrite hPoint -(hEqual _ hLone) in hIntegral; exact:hIntegral.
  exact:(@radon_compact_lattice_density_locally_unique R UT mu hm hr F A
    (fun x=>ed (a x) y) (fun x=>ed (b x) y) hF hLeft hRight).
have [d [e he]]:=@current_form_finite_basis R h2 n m.
have hAll:=@measure_locally_almost_countable R UT [the choiceType of 'I_d] mu hm setT
  (fun i=>[set x|ed (a x) (e i)=ed (b x) (e i)]) (countableP _)
  (fun i _=>hCoordinate (e i)).
apply:(@measure_locally_almost_mono R UT mu hm _ _ _ hAll)=>x hx.
apply:(continuous_dual_injective hDual); apply:hom_ext=>y.
rewrite (@basis_vector_expansion R Y d e he y) !linear_sum.
apply:eq_bigr=>i _;rewrite !linearZ.
exact:(congr1 (fun t:R^o=>(dual_basis he i y:R)*:t) (hx i Logic.I)).
Qed.

(** Source for [bounded_current_density_almost_unique]:
    the original bounded densities agree almost
    everywhere on U, supporting Federer 4.1.7,
    p. 358. The countable compact cover
    removes the local qualification of 2.5.14. *)
Theorem bounded_current_density_almost_unique:
  measure_almost_everywhere mu [set x|a x=b x].
Proof.
have [C [W [hC [hW [hWC [hCover hWCover]]]]]]:=
  @smooth_domain_compact_open_cover R X NX hNX n (@coordinate_basis R n)
    (@coordinate_basisP R n) U hU.
have hCount:=@radon_compact_cover_countably_measurable R UT mu hm hr C hC hCover.
exact:(@countably_finite_locally_null_is_null R UT mu hm _ hCount
  bounded_current_density_locally_unique).
Qed.
End BoundedCurrentDensityUniqueness.
