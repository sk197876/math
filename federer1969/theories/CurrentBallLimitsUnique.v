(** Federer (1969), 4.1.7, p. 357: the
    original scalar ball quotients and their limits
    are single-valued. Use the actual positive finite
    measure value and the earlier norm-limit theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentCoefficientNorms
  CurrentDomain CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed CurrentOriginalBallFormula
  MultivectorDualSealed PartialFunctionUP PartialFunctionBasic MeasureLpMembershipUP
  MetricSubsetBackground MetricClosedBalls CharacteristicFunctionSealed PositiveScalarGraphLimit CurrentBallLimitsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentBallLimitsUnique.
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


Local Notation Q := (@is_current_ball_quotient R h2 n m U hU T hT).
Local Notation L := (@is_current_ball_scalar_limit R h2 n m U hU T hT).

(** Source for [current_ball_quotient_unique]: the
    original finite ball measure determines the
    quotient uniquely, supporting Federer 4.1.7,
    p. 357. Undefined quotients are not assigned
    a value by this assertion. *)
Theorem current_ball_quotient_unique y x r a b:
  Q y x r a->Q y x r b->a=b.
Proof.
move=>[hr [mass [hMass [hPositive [hMember hA]]]]]
  [hr' [mass' [hMass' [hPositive' [hMember' hB]]]]].
have hMassEqual:mass=mass' by injection (eq_trans (esym hMass) hMass').
by rewrite hA hB hMassEqual.
Qed.

(** Source for [current_ball_scalar_limit_unique]: the
    original limit for each covector is unique,
    supporting Federer 4.1.7, p. 357. *)
Theorem current_ball_scalar_limit_unique y x a b:
  L y x a->L y x b->a=b.
Proof.
exact:(@positive_scalar_graph_limit_unique R (fun r q=>Q y x r q)
  (fun r p q=>@current_ball_quotient_unique y x r p q) a b).
Qed.
End CurrentBallLimitsUnique.
