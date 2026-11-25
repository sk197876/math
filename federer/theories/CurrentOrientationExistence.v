(** Federer (1969), 4.1.7, p. 357: existence
    of the original maximal orienting field. At
    each point of the exact scalar-limit locus,
    finite covector duality supplies a multivector;
    the original quotient limits determine it uniquely. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentCoefficientNorms
  CurrentDomain CurrentSpaces CurrentVectorSpaces CurrentIntegrationCriterion CurrentMultivectorDual
  NormalisedCurrentSealed CurrentOriginalBallFormula MultivectorDualSealed FiniteMultivectorDual
  ContinuousDualUP PartialFunctionUP PartialFunctionBasic PartialFunctionExtensionality MeasureLpMembershipUP
  MetricSubsetBackground MetricClosedBalls CharacteristicFunctionSealed PositiveScalarGraphLimit
  CurrentBallLimitsUP CurrentBallLimitsUnique CurrentBallLimitsLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentOrientationExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation V := (exterior_power X m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (metric_subset (U:set (real_norm_metric_space hNX))).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation L := (@is_current_ball_scalar_limit R h2 n m U hU T hT).
Local Notation locus := (@current_ball_limit_locus R h2 n m U hU T hT).
Local Notation spec := (@is_original_current_orienting_field R h2 n m U hU T hT).

(** Source for [current_orientation_graph_single_valued]:
    all original covector limits determine at
    most one multivector at each point,
    supporting Federer 4.1.7, p. 357. *)
Theorem current_orientation_graph_single_valued x (v w:V):
  (forall y:Y,L y x (ed v y))->(forall y:Y,L y x (ed w y))->v=w.
Proof.
move=>hv hw.
apply:(continuous_dual_injective (@current_multivector_continuous_dual R h2 n m)).
apply:hom_ext=>y.
exact:(@current_ball_scalar_limit_unique R h2 n m U hU T hT y x
  (ed v y) (ed w y) (hv y) (hw y)).
Qed.

(** Source for [current_orientation_value_exists]:
    every point where all the original scalar
    quotients converge has a multivector value,
    supporting Federer 4.1.7, p. 357.
    The earlier finite-dimensional duality theorem
    applies to the proved limit functional. *)
Theorem current_orientation_value_exists x:
  locus x->exists v:V,forall y:Y,L y x (ed v y).
Proof.
move=>hx.
have[ell hEll]:=@current_ball_limit_functional_exists R h2 n m U hU T hT x hx.
have[d [b hb]]:=@current_vector_finite_basis R h2 n m.
have[v hv]:=@finite_multivector_dual_surjective R X m [the finType of 'I_d] b hb ell.
exists v;by rewrite hv.
Qed.

(** Source for [original_current_orienting_field_exists]:
    the original orienting field exists with
    precisely its printed maximal domain, Federer
    4.1.7, p. 357. The graph construction
    proves existence and is hidden by the
    subsequent opaque interface. *)
Theorem original_current_orienting_field_exists:
  exists v:partial_function UT V,spec v.
Proof.
pose G:=fun (x:UT) (a:V)=>forall y:Y,L y x (ed a y).
have hG:forall x a b,G x a->G x b->a=b.
  exact:current_orientation_graph_single_valued.
pose v:=@Build_partial_function UT V G hG.
exists v;split.
- move=>x;split.
  + move=>[a ha] y;exists (ed a y);exact:ha y.
  + exact:current_orientation_value_exists.
- by move=>x a.
Qed.

(** Source for [original_current_orienting_field_unique]:
    the original exact-domain field is unique,
    supporting Federer 4.1.7, p. 357.
    Undefined points remain outside both graphs. *)
Theorem original_current_orienting_field_unique (v w:partial_function UT V):
  spec v->spec w->v=w.
Proof.
move=>[_ hv] [_ hw];apply:partial_function_graph_extensionality=>x a.
by rewrite hv hw.
Qed.
End CurrentOrientationExistence.
