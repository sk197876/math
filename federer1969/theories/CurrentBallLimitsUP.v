(** Federer (1969), 4.1.7, p. 357: independent
    definition of the original maximal orienting field
    by all characteristic-ball quotients. Undefined
    division is retained, following 2.1.1, p. 51;
    a chosen conull set is not used as the domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentCoefficientNorms
  CurrentDomain CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed CurrentOriginalBallFormula
  MultivectorDualSealed PartialFunctionUP PartialFunctionBasic MeasureLpMembershipUP
  MetricSubsetBackground MetricClosedBalls CharacteristicFunctionSealed PositiveScalarGraphLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentBallLimitsUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation V := (exterior_power X m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (metric_subset (U:set (real_norm_metric_space hNX))).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation k := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Local Notation I := (@current_representation_lone_integral R h2 n m U hU T mu k hRepresentation).
Local Notation ed := (@MultivectorDual.evaluation R X m).

(** Source for [current_ball_characteristic_field]: the
    original b_(x,r)y, viewed in the actual partial-
    function L1 domain used in Federer 4.1.7,
    p. 357, through 4.1.5, p. 350. *)
Definition current_ball_characteristic_field (y:Y) (x:UT) (r:R):
    partial_function UT (real_norm_metric_space hNY):=
  partial_function_total (fun z:UT=>
    ((@CharacteristicFunction.value R UT (metric_closed_ball x r) z)*:y:real_norm_metric_space hNY)).

(** Source for [is_current_ball_quotient]: the original
    S(b_(x,r)y)/||S|| B(x,r) with its genuine
    domain of definedness, supporting Federer 4.1.7,
    p. 357. Positive finite mass and actual L1
    membership are required before using the numerator. *)
Definition is_current_ball_quotient (y:Y) (x:UT) (r q:R):Prop:=
  0<r /\exists mass:R,mu (metric_closed_ball x r)=mass%:E /\0<mass /\
    is_measure_lp_function mu 1 (current_ball_characteristic_field y x r) /\
    q=I (current_ball_characteristic_field y x r)/mass.

(** Source for [is_current_ball_scalar_limit]: the
    original positive-radius quotient limit for one
    covector, supporting Federer 4.1.7, p. 357. *)
Definition is_current_ball_scalar_limit (y:Y) (x:UT) (l:R):Prop:=
  positive_scalar_graph_limit (fun r q=>is_current_ball_quotient y x r q) l.

(** Source for [current_ball_limit_locus]: exactly the
    points where the original scalar limit exists
    for every covector, the domain specified in
    Federer 4.1.7, p. 357. *)
Definition current_ball_limit_locus:set UT:=
  [set x|forall y:Y,exists l:R,is_current_ball_scalar_limit y x l].

(** Source for [is_original_current_orienting_field]: the
    original maximal partial multivector field, defined
    by all of its actual covector pairings,
    Federer 4.1.7, p. 357. Existence, measurability,
    unit mass and the integration action are
    conclusions to prove separately. *)
Definition is_original_current_orienting_field (v:partial_function UT V):Prop:=
  (forall x,partial_function_domain v x<->current_ball_limit_locus x) /\
  (forall x a,partial_function_graph v x a<->
    forall y:Y,is_current_ball_scalar_limit y x (ed a y)).
End CurrentBallLimitsUP.
