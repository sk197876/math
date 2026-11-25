(** Federer (1969), 4.1.7, pp. 355–357:
    integration representation for actual currents.
    Apply the proved 4.1.5 criterion with the
    original mass/comass dual identification. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation CurrentCoefficientNorms
  CurrentCoefficientCompleteness CurrentSpaces MultivectorDualSealed CurrentMultivectorDual
  DistributionVariationDomain DistributionFiniteVariationUP DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP DistributionIntegrationCriterion FiniteDistributionRadonRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentIntegrationCriterion.
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
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation C := (@current_space R h2 n U hU m).
Local Notation UT := (set_type (U:set XT)).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Local Notation action := (@current_value R h2 n U hU m).

(** Source for [is_current_integration_representation]: the
    original Radon integral action of a current with
    an actual multivector density, Federer 4.1.7,
    pp. 355–357, through the laws of 4.1.5. *)
Definition is_current_integration_representation (T:C)
    (rho:set UT->\bar R) (xi:UT->D):Prop:=
  @is_distribution_integration_representation R UT Y NY hNY D ed DN hDual
    O hO DT dvalues (action T) rho xi.

(** Source for [is_integration_representable_current]: a
    current is representable by the original Radon
    pairing integral, Federer 4.1.7, pp. 355–357. *)
Definition is_integration_representable_current (T:C):Prop:=
  exists rho:set UT->\bar R,exists xi:UT->D,is_current_integration_representation T rho xi.

(** Source for [is_locally_finite_current_variation]:
    the literal original compact scalar-test gauge
    is finite, as required by 4.1.5 in Federer
    4.1.7, pp. 355–357. *)
Definition is_locally_finite_current_variation (T:C):Prop:=
  @is_finite_distribution_variation R XT U Y NY DT values (action T).

(** Source for [is_normalised_current_representation]:
    the original variation Radon measure and the
    actual mass-one density almost everywhere,
    Federer 4.1.7, p. 357. *)
Definition is_normalised_current_representation (T:C)
    (rho:set UT->\bar R) (xi:UT->D):Prop:=
  @is_normalised_distribution_representation R UT Y NY hNY D ed DN hDual
    O hO DT dvalues (action T) rho xi.

(** Source for [current_integration_finite_gauge_criterion]:
    the original 4.1.5 criterion applies to actual
    mass/comass-normed currents, Federer 4.1.7,
    pp. 355–357. Every Banach and separability
    premise is discharged for the finite covectors. *)
Theorem current_integration_finite_gauge_criterion (T:C):
  is_locally_finite_current_variation T <->is_integration_representable_current T.
Proof.
exact:(@distribution_integration_criterion R n Y NY hNY
  (@current_form_complete R h2 n m) (@current_form_separable R h2 n m)
  U hU E ev hE (action T) D ed DN hDual O hO).
Qed.

(** Source for [normalised_current_representation_exists]:
    the original variation measure represents the
    current with an actual multivector density of
    mass one almost everywhere, Federer 4.1.7,
    p. 357, using 4.1.5. *)
Theorem normalised_current_representation_exists (T:C):
  is_integration_representable_current T ->
  exists rho:set UT->\bar R,exists xi:UT->D,is_normalised_current_representation T rho xi.
Proof.
move=>hRep.
have hFinite:=(current_integration_finite_gauge_criterion T).2 hRep.
exact:(@finite_distribution_radon_representation R n Y NY hNY
  (@current_form_complete R h2 n m) (@current_form_separable R h2 n m)
  U hU E ev hE (action T) D ed DN hDual O hO hFinite).
Qed.

End CurrentIntegrationCriterion.
