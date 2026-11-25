(** Federer (1969), 4.1.12, pp. 367–368: the
    action of a finite-mass current supported in K
    is bounded by its mass times nu_K^0. Reuse
    the original Radon support and L1 extension
    from 4.1.5 and 4.1.7. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms CurrentCoefficientNorms CurrentCoefficientCompleteness
  CurrentSpaces CurrentDomain CurrentMultivectorDual MultivectorDualSealed
  CurrentIntegrationCriterion CurrentFiniteMassRepresentation CurrentMassSealed
  CurrentMassRepresentation NormalisedCurrentSealed CurrentRadonSupport
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  CurrentOriginalBallFormula CurrentLoneExtension CurrentLoneOriginalAgreement
  SmoothCompactSet SmoothFunctionTopology SmoothFunctionSeminormFamily
  SmoothDerivativeSeminormUP SmoothTestSpaces SmoothTestEvaluation
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureLpMembershipUP MeasureLpConvergence DualLoneIntegralUP DualLoneIntegralSealed
  DualLoneIntegralLipschitz FiniteMeasureLoneUniformBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactMassAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation hDual := (@current_multivector_continuous_dual R h2 n m).
Local Notation O := (@current_multivector_weak_opens R n m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation UT := (current_domain R n U).
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation D := (@current_smooth_derivatives R h2 n U hU m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation nu := (smooth_function_derivative_seminorm hD).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation value := (@current_test_value R h2 n U hU m).
Local Notation C := (@current_space R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation M := (@CurrentMass.value R h2 n m U hU).

(** Source for [current_compact_mass_action_bound]: the
    original inequality |T(phi)|<=M(T) nu_K^0(phi)
    for a current supported in K, used in the
    minimum formula of Federer 4.1.12, pp. 367–368.
    Finite mass is expressed by its exact real value;
    no positivity or special density is assumed. *)
Theorem current_compact_mass_action_bound (T:C) mass:
  M T=mass%:E->
  @current_support R h2 n U hU m T `<=` smooth_compact_carrier K->
  forall phi:DT,`|action T phi|<=mass * nu K 0%N (inc phi).
Proof.
move=>hMass hSupport phi.
have hFinite:(M T < +oo)%E by rewrite hMass;exact:ltry.
have hT:=@current_finite_mass_representation R h2 n m U hU T hFinite.
pose mu:=@NormalisedCurrent.measure R h2 n m U hU T hT.
pose eta:=@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT.
have hRepresentation:=@NormalisedCurrent.laws R h2 n m U hU T hT.
have hBase:=normalised_distribution_representation_laws hRepresentation.
have hm:=distribution_representation_measure hBase.
have hTotal:mu setT=mass%:E.
  by rewrite /mu -(@current_represented_mass_total R h2 n m U hU T hT) hMass.
pose I:=@current_representation_lone_integral R h2 n m U hU T mu eta hRepresentation.
pose total:=fun psi:DT=>partial_function_total
  (fun x:UT=>(value psi (set_val x):real_norm_metric_space hNY)).
have hPhi:=@current_original_test_lone_member R h2 n m U hU T mu eta hRepresentation phi.
have hZero:=@current_original_test_lone_member R h2 n m U hU T mu eta hRepresentation (0:DT).
have hAlmostSupport:measure_almost_everywhere mu
    [set x:UT|@current_support R h2 n U hU m T (set_val x)].
  exact:(@current_radon_outside_support_null R h2 n m U hU T hT).
have hPoint:measure_almost_everywhere mu
    [set x:UT|NY (value phi (set_val x)-value (0:DT) (set_val x))<=nu K 0%N (inc phi)].
  apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hAlmostSupport)=>x hx.
  have hZeroValue:value (0:DT)=(fun _=>0).
    exact:(linear0 (smooth_test_values_hom hE)).
  rewrite /= hZeroValue /= subr0.
  have h:=@smooth_derivative_seminorm_bound R X Y NX NY hNX hNY U E D K 0%N
    (nu K 0%N) (smooth_function_derivative_seminorm_laws hD K 0%N)
    (inc phi) 0%N (leqnn 0%N) (set_val x) (hSupport (set_val x) hx).
  rewrite (@smooth_derivative_zero_norm R X Y NX NY hNX hNY U E ev D hD
    (inc phi) (set_val x) (set_valP x)) in h.
  exact:h.
have hDistance:=@finite_measure_lone_almost_uniform_bound R UT Y NY hNY mu hm mass
  (nu K 0%N (inc phi))
  (fun x:UT=>(value phi (set_val x):real_norm_metric_space hNY))
  (fun x:UT=>(value (0:DT) (set_val x):real_norm_metric_space hNY))
  hTotal hPhi.2.1 hZero.2.1 hPoint.
have hI:@is_dual_lone_integral R UT Y NY hNY V ed eta mu I by exact:DualLoneIntegral.laws.
have hLipschitz:=@dual_lone_integral_lipschitz R UT Y NY hNY (@current_form_separable R h2 n m)
  V ed VN hDual O hO mu hm eta (distribution_representation_weak_measurable hBase)
  (normalised_distribution_density_unit_bound hRepresentation) I
 hI
  (total phi) (total (0:DT)) hPhi hZero.
have hBound:=le_trans hLipschitz hDistance.
rewrite /I /total !current_lone_extension_original linear0 subr0 lee_fin in hBound.
by rewrite mulrC in hBound.
Qed.
End CurrentCompactMassAction.
