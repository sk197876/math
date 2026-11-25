(** Federer (1969), 4.1.7, p. 357: the
    original covector ball limits are linear. The
    quotient identity holds on the actual common
    L1 domain before the positive-radius limit
    is taken. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentCoefficientNorms
  CurrentDomain CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed CurrentOriginalBallFormula
  MultivectorDualSealed PartialFunctionUP PartialFunctionBasic MeasureLpMembershipUP
  MetricSubsetBackground MetricClosedBalls CharacteristicFunctionSealed PositiveScalarGraphLimit
  PositiveScalarGraphLinearLimits CurrentBallLimitsUP CurrentBallLimitsUnique CurrentBallQuotientLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentBallLimitsLinear.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation Q := (@is_current_ball_quotient R h2 n m U hU T hT).
Local Notation L := (@is_current_ball_scalar_limit R h2 n m U hU T hT).

(** Source for [current_ball_scalar_limit_linear]:
    linearity of the scalar limits defining the
    original orienting field in Federer 4.1.7,
    p. 357. No quotient outside its original
    domain is used. *)
Theorem current_ball_scalar_limit_linear c y z x a b:
  L y x a->L z x b->L (c*:y+z) x (c*a+b).
Proof.
exact:(@positive_scalar_graph_limit_linear R
  (fun r q=>Q y x r q) (fun r q=>Q z x r q)
  (fun r q=>Q (c*:y+z) x r q)
  (fun r p q=>@current_ball_quotient_unique R h2 n m U hU T hT y x r p q)
  (fun r p q=>@current_ball_quotient_unique R h2 n m U hU T hT z x r p q)
  c (fun r p q=>@current_ball_quotient_linear R h2 n m U hU T hT c y z x r p q) a b).
Qed.

(** Source for [current_ball_limit_functional_exists]:
    at every point of the original maximal
    limit locus, all limits form one actual
    linear covector functional, supporting Federer
    4.1.7, p. 357. Existence is proved
    from the original scalar limits. *)
Theorem current_ball_limit_functional_exists x:
  @current_ball_limit_locus R h2 n m U hU T hT x->
  exists ell:Hom Y R^o,forall y:Y,L y x (ell y).
Proof.
move=>hLocus.
pose f (y:Y):R^o:=projT1 (cid (hLocus y)).
have hF y:L y x (f y):=projT2 (cid (hLocus y)).
have hLinear:@hom_pred R Y R^o f.
  apply/asboolP=>c y z.
  exact:(@current_ball_scalar_limit_unique R h2 n m U hU T hT (c*:y+z) x
    (f (c*:y+z)) (c*f y+f z) (hF (c*:y+z))
    (@current_ball_scalar_limit_linear c y z x (f y) (f z) (hF y) (hF z))).
exists (@HomMap R Y R^o f hLinear);exact:hF.
Qed.
End CurrentBallLimitsLinear.
