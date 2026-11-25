(** Federer (1969), 4.1.7, p. 358:
    uniform compact approximations pass through
    the original L1 extensions of normal
    currents and their boundaries. This adapter
    uses finite total variation and the
    already proved one-Lipschitz law of
    4.1.5, p. 350. *)
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
Section CurrentLoneUniformLimit.
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

(** Source for [current_lone_almost_uniform_limit]: the
    original L1 extension preserves uniform
    limits of its summable fields when
    the original variation has finite total
    mass, supporting the class-one boundary
    passage in Federer 4.1.7, p. 358.
    No sequence replaces the original positive
    convolution-radius limit. *)
Theorem current_lone_almost_uniform_limit mass radius (f:UT->Y) (g:R->UT->Y):
  mu setT=mass%:E->0<radius->
  is_measure_lp_function mu 1 (total f)->
  (forall e,0<e->e<radius->is_measure_lp_function mu 1 (total (g e)))->
  (forall epsilon:R,0<epsilon->exists d:R,0<d /\forall e,0<e->e<d->
    measure_almost_everywhere mu [set x|NY (g e x-f x)<epsilon])->
  positive_norm_limit (fun t:R^o=>`|t|) (fun e=>I (total (g e))) (I (total f)).
Proof.
move=>hMass hRadius hf hg hUniform epsilon hEpsilon.
have hMassNonnegative:0<=mass.
  have h:=measure_nonnegative hm setT;by rewrite hMass lee_fin in h.
have hDen:0<mass+1 by lra.
pose tolerance:=epsilon/(mass+1).
have hTolerance:0<tolerance by rewrite /tolerance divr_gt0.
have [d [hd hApprox]]:=hUniform tolerance hTolerance.
exists (Num.min d radius);split;first by rewrite lt_min hd hRadius.
move=>e he hSmall.
have /andP [hed her]:(e<d)&&(e<radius) by rewrite -lt_min.
have hge:=hg e he her.
have hPointBound:measure_almost_everywhere mu [set x|NY (g e x-f x)<=tolerance].
  apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ (hApprox e he hed))=>x hx.
  exact:ltW hx.
have hDistance:=@finite_measure_lone_almost_uniform_bound R UT Y NY hNY mu hm mass tolerance
  (fun x=>(g e x:real_norm_metric_space hNY)) (fun x=>(f x:real_norm_metric_space hNY))
  hMass hge.2.1 hf.2.1 hPointBound.
have hI:=@DualLoneIntegral.laws R UT Y NY hNY (@current_form_separable R h2 n m)
  V ed VN hDual O hO mu hm eta (distribution_representation_weak_measurable hBase)
  (normalised_distribution_density_unit_bound hRepresentation).
have hLipschitz:=@dual_lone_integral_lipschitz R UT Y NY hNY (@current_form_separable R h2 n m)
  V ed VN hDual O hO mu hm eta (distribution_representation_weak_measurable hBase)
  (normalised_distribution_density_unit_bound hRepresentation) I hI (total (g e)) (total f) hge hf.
have hBound:`|I (total (g e))-I (total f)|<=tolerance*mass.
  have h:=le_trans hLipschitz hDistance;by rewrite lee_fin in h.
apply:le_lt_trans hBound _.
have hStrict:tolerance*mass<tolerance*(mass+1) by rewrite ltr_pM2l // ltrDl.
by rewrite /tolerance divfK ?gt_eqF // in hStrict.
Qed.

(** Source for [current_lone_uniform_limit]: the
    everywhere uniform version of the same
    original L1 limit, supporting the
    boundary approximation in Federer 4.1.7,
    p. 358. *)
Theorem current_lone_uniform_limit mass radius (f:UT->Y) (g:R->UT->Y):
  mu setT=mass%:E->0<radius->
  is_measure_lp_function mu 1 (total f)->
  (forall e,0<e->e<radius->is_measure_lp_function mu 1 (total (g e)))->
  (forall epsilon:R,0<epsilon->exists d:R,0<d /\forall e,0<e->e<d->
    forall x,NY (g e x-f x)<epsilon)->
  positive_norm_limit (fun t:R^o=>`|t|) (fun e=>I (total (g e))) (I (total f)).
Proof.
move=>hMass hRadius hf hg hUniform.
apply:(current_lone_almost_uniform_limit hMass hRadius hf hg)=>epsilon hEpsilon.
have [d [hd hBound]]:=hUniform epsilon hEpsilon.
exists d;split=>// e he hed.
apply:(@measure_almost_everywhere_mono R UT mu hm setT _ _
  (measure_almost_everywhere_true hm))=>x _;exact:hBound e he hed x.
Qed.
End CurrentLoneUniformLimit.
