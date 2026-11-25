(** Federer (1969), 4.1.7, p. 356:
    the Radon measure, associated Daniell integral
    on K(U), and its zero-current have the
    same values on the original scalar tests. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom SmoothTestSpaces RealNormUP NormMetric RealMetricBackground NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero CurrentDomain CurrentSpaces
  CurrentScalarTestMaps CurrentZeroCovectorMaps RadonMeasureCurrent
  Distributions SmoothFunctionSpaceUP SmoothTestEvaluation DistributionVariationDomain DistributionSubspaceTestValues
  CompactContinuousVectorFields ScalarNormExtendedEmbedding CompactSupportFunctionUP CompactSupportFunctionLattice
  RealIntegralFunctional MonotoneDaniellIntegralUP
  MeasureUP RadonMeasureUP RadonCompactScalarIntegral MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RadonDaniellCurrent.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation NS := (fun r:R^o=>`|r|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Local Notation E := (@distribution_smooth_space R X R^o NX NS hNX hNS U hU).
Local Notation ev := (@distribution_smooth_value R X R^o NX NS hNX hNS U hU).
Local Notation hE := (@distribution_smooth_laws R X R^o NX NS hNX hNS U hU).
Local Notation DT := (@current_test_space R h2 n U hU 0%N).
Local Notation coefficient := (fun psi:DT=>fun x:UT=>zero_form_value
  (@current_test_value R h2 n U hU 0%N psi (set_val x))).

(** Source for [current_scalar_test_compact_continuous]:
    the original scalar coefficient of each
    zero-form test lies in K(U), supporting
    Federer's identification in 4.1.7, p. 356.
    The earlier actual inverse scalar test maps
    supply continuity and compact support. *)
Lemma current_scalar_test_compact_continuous psi:
  @compactly_supported_continuous_functions R UT (coefficient psi).
Proof.
pose q:=@current_scalar_test_coefficients R h2 n U hU psi.
pose values:=@distribution_domain_values R XT U R^o (smooth_test_space hE) (smooth_test_values_hom hE).
have hField:=@smooth_test_original_continuous_field R X R^o NX NS hNX hNS U E ev hE q.
have hPoint:values q=coefficient psi.
  apply:funext=>x; exact:(@current_scalar_test_coefficients_values R h2 n U hU psi
    (set_val x) (set_valP x)).
have hSupport:compact (@real_function_support R UT (values q)).
  have h:=hField.2.
  rewrite (@compact_vector_norm_support_identity R UT R^o NS hNS (values q)) in h.
  exact:h.
rewrite -hPoint; split; last exact:hSupport.
move=>x.
exact (@continuous_comp UT [the topologicalType of real_norm_metric_space hNS]
  [the topologicalType of real_line_metric R] (values q) (fun t=>t) x
  (hField.1 x) (@scalar_norm_real_identity_continuous R (values q x))).
Qed.

Variable gamma:set UT->\bar R.
Hypothesis hGamma:is_measure gamma.
Hypothesis hRadon:is_radon_measure gamma.
Local Notation F := (@radon_compact_integral R UT gamma hGamma hRadon).
Local Notation T := (@radon_measure_current R h2 n U hU gamma hGamma hRadon).

(** Source for [radon_current_associated_daniell]: the
    original scalar integral is the associated
    monotone Daniell integral on all of K(U),
    Federer 4.1.7, p. 356, by 2.5.1,
    p. 92. Signed compact tests are included. *)
Theorem radon_current_associated_daniell:
  is_monotone_daniell_integral (@compactly_supported_continuous_functions R UT) F.
Proof.
exact:(@real_integral_functional_is_monotone_daniell R UT gamma hGamma
  (@compactly_supported_continuous_functions R UT) F
  (@compactly_supported_continuous_functions_lattice R UT)
  (@radon_compact_integral_laws R UT gamma hGamma hRadon)).
Qed.

(** Source for [radon_daniell_current_evaluation]: the
    actual zero-current is precisely the restriction
    of the associated Daniell integral on K(U),
    Federer 4.1.7, p. 356. *)
Theorem radon_daniell_current_evaluation psi:
  @current_value R h2 n U hU 0%N T psi=F (coefficient psi).
Proof.
have hOriginal:=@radon_measure_current_integral R h2 n U hU gamma hGamma hRadon psi.
have hDaniell:=@radon_compact_integral_laws R UT gamma hGamma hRadon (coefficient psi)
  (current_scalar_test_compact_continuous psi).
exact:(congr1 (@fine R) (measure_integral_unique hOriginal hDaniell)).
Qed.
End RadonDaniellCurrent.
