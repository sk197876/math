(** Federer (1969), 4.1.18, pp. 374–377: an
    actual smooth Lebesgue-density current has its
    original Radon representation on the actual full
    current domain. The ambient integral is transported
    through the earlier canonical measure copy. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormRegularity NormClassZeroTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  AlternatingPairing CurrentCoefficientNorms CurrentSpaces CurrentEvaluation
  CurrentVectorSpaces CurrentDomain CurrentIntegrationCriterion CurrentMultivectorDual
  MultivectorDualSealed CurrentContinuousOpenDensity OpenCurrentDensitySealed
  DistributionIntegrationRepresentationUP DistributionVariationDomain
  CurrentSmoothLebesgue CurrentDensityAction EuclideanFullDomainMeasure
  EuclideanLebesgueDimensions MeasureIntegralUP MeasureIntegralUniqueness
  SmoothFunctionSpaceUP SmoothTestEvaluation SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSmoothLebesgueFullRepresentation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation FT:=(current_domain R n Full).
Local Notation V:=(@current_vector_smooth_space R h2 n Full hFull m).
Local Notation vv:=(@current_vector_smooth_value R h2 n Full hFull m).
Local Notation hV:=(@current_vector_smooth_space_laws R h2 n Full hFull m).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Local Notation gamma:=(@euclidean_full_domain_measure R n).
Local Notation hm:=(@euclidean_full_domain_measure_laws R n).1.
Local Notation hr:=(@euclidean_full_domain_measure_laws R n).2.
Local Notation L:=(@current_smooth_lebesgue_map R h2 n m).

(** Source for [current_smooth_lebesgue_full_representation]:
    the original smooth density current on R^n
    has exactly the full-domain Lebesgue measure
    and its actual smooth multivector density, supporting
    Federer 4.1.18, pp. 374–377. *)
Theorem current_smooth_lebesgue_full_representation (xi:V):
  @is_current_integration_representation R h2 n m Full hFull (L xi)
    gamma (fun x:FT=>vv xi (set_val x)).
Proof.
pose field:=fun x:FT=>vv xi (set_val x).
have hContinuous:continuous (fun x:FT=>(field x:real_norm_metric_space hVN)).
  exact:(@norm_class_zero_restriction_continuous R X (exterior_power X m)
    NX VN hNX hVN Full (vv xi)
    (norm_class_continuous (smooth_function_evaluation_smooth hV xi 0%N))).
have hField:=@current_continuous_open_density_integrable R h2 n m Full
  gamma hm hr field hContinuous.
pose C:=@OpenCurrentDensity.value R h2 n m Full hFull gamma hm hr field hField.
have hC:=@OpenCurrentDensity.laws R h2 n m Full hFull gamma hm hr field hField.
have hEqual:L xi=C.
  apply:(@current_values_extensional R h2 n m Full hFull)=>psi.
  have hOriginal:=@current_smooth_lebesgue_action R h2 n m xi psi.
  have hFullIntegral:=@euclidean_full_domain_real_integral R n
    (fun x=>pairing (vv xi x) (@current_test_value R h2 n Full hFull m psi x))
    (@current_value R h2 n Full hFull m (L xi) psi)%:E hOriginal.
  have hOpen:=distribution_representation_action hC psi.
  have hFunction:(fun x:FT=>
      @MultivectorDual.evaluation R X m (field x)
        (@current_test_value R h2 n Full hFull m psi (set_val x)))=
      (fun x:FT=>pairing (vv xi (set_val x))
        (@current_test_value R h2 n Full hFull m psi (set_val x))).
    apply:funext=>x;exact:MultivectorDual.laws.
  change (is_measure_integral gamma
    (real_total_integrand (fun x:FT=>@MultivectorDual.evaluation R X m (field x)
      (@current_test_value R h2 n Full hFull m psi (set_val x))))
    (@current_value R h2 n Full hFull m C psi)%:E) in hOpen.
  rewrite hFunction in hOpen.
  exact:(EFin_inj (measure_integral_unique hFullIntegral hOpen)).
by rewrite hEqual.
Qed.

(** Source for [current_smooth_lebesgue_representable]: every
    actual smooth density current is representable
    with no finite global mass condition, supporting
    the variation limit and L1 representation in
    Federer 4.1.18, pp. 374–377. *)
Theorem current_smooth_lebesgue_representable (xi:V):
  @is_integration_representable_current R h2 n m Full hFull (L xi).
Proof.
exists gamma,(fun x:FT=>vv xi (set_val x)).
exact:current_smooth_lebesgue_full_representation.
Qed.
End CurrentSmoothLebesgueFullRepresentation.
