(** Federer (1969), 4.1.14, p. 372: finite-mass
    continuous-form actions pass through uniformly convergent
    pullbacks. This sequence adapter reuses the original
    one-Lipschitz L1 action and the finite-measure uniform
    bound from 4.1.5 and 4.1.7. No normality,
    smoothness or compact support of the fields is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal lra topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentDomain CurrentMultivectorDual
  MultivectorDualSealed CurrentIntegrationCriterion CurrentOriginalBallFormula
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureLpMembershipUP MeasureLpConvergence
  DualLoneIntegralUP DualLoneIntegralSealed DualLoneIntegralLipschitz
  FiniteMeasureLoneUniformBound PositiveNormLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLoneSequenceLimit.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
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
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Variable T:@current_space R h2 n U hU m.
Variable mu:set UT->\bar R.
Variable eta:UT->V.
Hypothesis hRepresentation:@is_normalised_current_representation R h2 n m U hU T mu eta.
Local Notation hBase := (normalised_distribution_representation_laws hRepresentation).
Local Notation hm := (distribution_representation_measure hBase).
Local Notation I := (@current_representation_lone_integral R h2 n m U hU T mu eta hRepresentation).
Let total (f:UT->Y):=partial_function_total (fun x=>(f x:real_norm_metric_space hNY)).

(** Source for [current_lone_almost_uniform_action_bound]:
    the original L1 action error is bounded by total variation
    times an almost-everywhere uniform field error, supporting
    Federer 4.1.14, p. 372. The original actual
    normalised representation is arbitrary and both summable
    fields retain their full partial-function domains. *)
Theorem current_lone_almost_uniform_action_bound mass bound (f g:UT->Y):
  mu setT=mass%:E->
  is_measure_lp_function mu 1 (total f)->
  is_measure_lp_function mu 1 (total g)->
  measure_almost_everywhere mu [set x|NY (f x-g x)<=bound]->
  `|I (total f)-I (total g)|<=bound*mass.
Proof.
move=>hMass hf hg hPoint.
have hDistance:=@finite_measure_lone_almost_uniform_bound R UT Y NY hNY mu hm mass bound
  (fun x=>(f x:real_norm_metric_space hNY))
  (fun x=>(g x:real_norm_metric_space hNY)) hMass hf.2.1 hg.2.1 hPoint.
have hI:=@DualLoneIntegral.laws R UT Y NY hNY (@current_form_separable R h2 n m)
  V ed VN hDual O hO mu hm eta (distribution_representation_weak_measurable hBase)
  (normalised_distribution_density_unit_bound hRepresentation).
have hLipschitz:=@dual_lone_integral_lipschitz R UT Y NY hNY (@current_form_separable R h2 n m)
  V ed VN hDual O hO mu hm eta (distribution_representation_weak_measurable hBase)
  (normalised_distribution_density_unit_bound hRepresentation) I hI (total f) (total g) hf hg.
have hBound:=le_trans hLipschitz hDistance.
by rewrite lee_fin in hBound.
Qed.

(** Source for [current_lone_almost_uniform_sequence_limit]:
    almost-everywhere uniform convergence gives convergence of
    the actual finite-variation L1 values used in the last
    class-one identity of Federer 4.1.14, p. 372.
    The argument is the preceding one-Lipschitz action law;
    the approximating fields need only be L1 members. *)
Theorem current_lone_almost_uniform_sequence_limit mass (f:UT->Y) (g:nat->UT->Y):
  mu setT=mass%:E->
  is_measure_lp_function mu 1 (total f)->
  (forall k,is_measure_lp_function mu 1 (total (g k)))->
  (forall epsilon:R,0<epsilon->exists k,forall L,(k<=L)%N->
    measure_almost_everywhere mu [set x|NY (g L x-f x)<epsilon])->
  forall epsilon:R,0<epsilon->exists k,forall L,(k<=L)%N->
    `|I (total (g L))-I (total f)|<epsilon.
Proof.
move=>hMass hf hg hUniform epsilon hEpsilon.
have hMassNonnegative:0<=mass.
  have h:=measure_nonnegative hm setT;by rewrite hMass lee_fin in h.
have hDen:0<mass+1 by lra.
pose tolerance:=epsilon/(mass+1).
have hTolerance:0<tolerance by rewrite /tolerance divr_gt0.
have[k hApprox]:=hUniform tolerance hTolerance.
exists k=>L hL.
have hPoint:measure_almost_everywhere mu [set x|NY (g L x-f x)<=tolerance].
  apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ (hApprox L hL))=>x hx.
  exact:ltW hx.
have hBound:=current_lone_almost_uniform_action_bound hMass (hg L) hf hPoint.
apply:le_lt_trans hBound _.
have hStrict:tolerance*mass<tolerance*(mass+1) by rewrite ltr_pM2l // ltrDl.
by rewrite /tolerance divfK ?gt_eqF // in hStrict.
Qed.
End CurrentLoneSequenceLimit.
