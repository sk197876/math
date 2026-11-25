(** Federer (1969), 4.1.7, pp. 355–358:
    original Radon densities on arbitrary open U
    define actual currents. Apply the checked
    mass/comass duality and the original test-space
    local bound, without extending across the boundary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation CurrentCoefficientNorms
  CurrentCoefficientCompleteness CurrentSpaces MultivectorDualSealed CurrentMultivectorDual
  DistributionVariationDomain DistributionFiniteVariationUP DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP DistributionIntegrationCriterion FiniteDistributionRadonRepresentation CurrentIntegrationCriterion OpenCurrentDensityUP
  OpenDistributionFromField SmoothCompactSet IsotropyGroupTopology MeasureUP RadonMeasureUP MeasureSubsetIntegral
  MeasureIntegralUP SummableRealFunctionUP RealSubsetIntegralGraph PartialFunctionBasic
  OpenFamilyTopologyMathcomp MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OpenCurrentDensityExistence.
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
Local Notation D := (exterior_power X m).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation DN := (@current_vector_mass R h2 n m).
Local Notation hDual := (@current_multivector_continuous_dual R h2 n m).
Local Notation O := (@current_multivector_weak_opens R n m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation C := (@current_space R h2 n U hU m).
Local Notation UT := (set_type (U:set XT)).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Local Notation action := (@current_value R h2 n U hU m).


Variable gamma:set UT->\bar R.
Hypothesis hGamma:is_measure gamma.
Hypothesis hRadon:is_radon_measure gamma.
Variable xi:UT->D.
Hypothesis hField:@is_locally_integrable_open_current_density R h2 n m U gamma xi.

(** Source for [open_current_density_compact_step_integral]:
    the original compact mass integral gives each
    actual fixed-support step's finite majorant,
    supporting Federer 4.1.7, pp. 356–358. *)
Lemma open_current_density_compact_step_integral (K:smooth_compact_set hNX U):
  exists b:R,is_measure_integral gamma (real_total_integrand
    (fun x:UT=>if pselect (smooth_compact_carrier K (set_val x)) then DN (xi x) else 0)) b%:E.
Proof.
pose S:set UT:=set_val @^-1` smooth_compact_carrier K.
have hCompact:compact S:=@set_type_compact_preimage XT U (smooth_compact_carrier K)
  (smooth_compact_is_compact K) (smooth_compact_in_domain K).
have hLocal:forall A:set UT,compact A->exists b:R,
    is_measure_subset_integral gamma A (real_total_integrand (fun x=>DN (xi x))) b%:E:=hField.2.
have [b hB]:=@hLocal S hCompact.
pose g (x:UT):=if pselect (smooth_compact_carrier K (set_val x)) then DN (xi x) else 0.
have hOn x:S x->g x=DN (xi x) by move=>hx;rewrite /g;case:pselect=>//hn;exact:False_ind _ (hn hx).
have hOff x:~S x->g x=0 by move=>hx;rewrite /g;case:pselect=>//hn;exact:False_ind _ (hx hn).
exists b;exact:((@real_subset_integral_total R UT gamma S (fun x=>DN (xi x)) g b%:E hOn hOff).1 hB).
Qed.

(** Source for [open_current_from_density_exists]: the
    original locally mass-integrable Radon density
    on U defines an actual integration-representable
    current, Federer 4.1.7, pp. 355–358.
    Current continuity is proved, not assumed. *)
Theorem open_current_from_density_exists:
  exists T:C,@is_current_integration_representation R h2 n m U hU T gamma xi.
Proof.
have [T hAction]:=@open_distribution_from_dual_field_exists R X Y NX NY hNX hNY U E ev hE
  (@current_smooth_derivatives R h2 n U hU m) (@current_smooth_derivative_laws R h2 n U hU m)
  D ed DN hDual (@current_form_separable R h2 n m) O hO gamma hGamma hRadon xi hField.1 hU
  open_current_density_compact_step_integral.
exists T;constructor.
- exact:hGamma.
- exact:hRadon.
- exact:hField.1.
- exact:hField.2.
- exact:hAction.
Qed.
End OpenCurrentDensityExistence.
