(** Federer (1969), 4.1.7, pp. 358–359:
    where an original represented current annihilates
    all supported tests, its original Radon
    variation measure vanishes. The proof uses
    the literal scalar-test gauge from 4.1.5
    and the earlier compact positive-test supremum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology functions.
From Federer Require Import IsotropyGroupTopology Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentCoefficientNorms
  CurrentDomain CurrentDomainGeometry CurrentSpaces CurrentIntegrationCriterion CurrentMultivectorDual MultivectorDualSealed
  NormalisedCurrentSealed SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothFunctionSupport
  FunctionalSupportUP NormDominatedFunctionSupport OpenSubspaceExtension CompactScalarOpenSupport
  FunctionLatticeUP CompactSupportFunctionUP CompactOpenContentUP ExtendedSupremumUP ExtendedRealBoundsUP
  DistributionVariationDomain DistributionVariationUP DistributionVariationBasic DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP NormalisedDistributionScalarIntegral NormalisedScalarIntegralGauge
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness RadonMeasureUP RadonPositiveCompactOpenContent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentRadonAnnihilation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation V := (exterior_power X m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation DN := (@current_vector_mass R h2 n m).
Local Notation hDual := (@current_multivector_continuous_dual R h2 n m).
Local Notation O := (@current_multivector_weak_opens R n m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation value := (@current_test_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Local Notation action := (@current_value R h2 n U hU m).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation k := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Let hBase:=normalised_distribution_representation_laws hRepresentation.
Let hm:=distribution_representation_measure hBase.
Let hr:=distribution_representation_radon hBase.
Local Notation F := (@normalised_distribution_scalar_integral R UT Y NY hNY V ed DN hDual O hO
  DT dvalues (action T) mu k hRepresentation).

(** Source for [current_radon_annihilation_null]: an
    original open annihilation region has zero
    variation measure, supporting the compact-support
    and proper-pushforward assertions in Federer
    4.1.7, pp. 358–359. *)
Theorem current_radon_annihilation_null (W:set X):
  @smooth_functional_annihilation_open R X Y NX hNX U DT value (action T) W->
  mu (set_val @^-1` W)=0.
Proof.
move=>[hW hZero].
have hOpenU:@open XT U.
  rewrite openE=>x hx;exact:(norm_domain_interior_neighbourhood hNX U x).1 (@hU x hx).
have hOpenW:open (set_val @^-1` W:set UT).
  exact:((@continuousP UT XT set_val).1
    (@set_type_val_continuous XT U) W hW).
have hOutside:forall phi:DT,forall x:X,~U x->values phi x=0.
  move=>phi x hx;exact:(@smooth_test_value_outside R X Y NX NY hNX hNY U
    (@current_smooth_space R h2 n U hU m) (@current_smooth_value R h2 n U hU m) hE phi x hx).
have hContent:=@radon_positive_compact_open_content R UT mu hm hr F
  (@current_domain_locally_compact R n U hU)
  (@normalised_distribution_scalar_integral_laws R UT Y NY hNY V ed DN hDual O hO
    DT dvalues (action T) mu k hRepresentation).
apply/eqP;rewrite eq_le (measure_nonnegative hm) andbT.
apply:(extended_real_supremum_least (@hContent (set_val @^-1` W) hOpenW))=>a [f [hTest ->]].
have hPositive:positive_function_lattice (@compactly_supported_continuous_functions R UT) f.
  split;first exact:hTest.1.
  move=>x;exact:(andP (hTest.2.1 x)).1.
have hGauge:=@normalised_scalar_integral_original_gauge R UT Y NY hNY V ed DN hDual O hO
  DT dvalues (action T) mu k hRepresentation f hPositive.
apply:(extended_supremum_least hGauge)=>b [phi [hPhi <-]].
have hAmbient:=(@distribution_domain_gauge_admissible R XT U Y NY hNY DT values hOutside phi f).1 hPhi.
have hSupport:=@norm_dominated_function_support R X Y NX NY hNX hNY U DT values phi
  (@open_extension R XT U f) hAmbient.
have hScalar:=@compact_scalar_open_extension_support R XT (@metric_hausdorff R XT) U hOpenU f hTest.1.
have hInW:@smooth_function_support R X Y NX hNX U DT value phi `<=` W.
  move=>x hx.
  have[z hz hzx]:=hScalar x (hSupport x hx).
  rewrite -hzx;exact:(hTest.2.2 z hz).
by rewrite (@hZero phi hInW).
Qed.
End CurrentRadonAnnihilation.
