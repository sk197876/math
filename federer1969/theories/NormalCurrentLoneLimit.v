(** Federer (1969), 4.1.7, p. 358:
    convergence on the original compact
    support of a normal current suffices
    for convergence of its actual L1
    values. The variation is carried by
    that support and has finite total
    mass, by the preceding original laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology functions.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  CurrentCoefficientNorms CurrentSpaces CurrentDomain CurrentIntegrationCriterion NormalCurrentsUP
  NormalisedCurrentSealed CurrentRadonSupport CurrentMassBasic CurrentMassRepresentation CompactRepresentedCurrentMass
  NormalCurrentContinuousLoneMember CurrentOriginalBallFormula CurrentLoneUniformLimit
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionBasic MeasureAlmostUP MeasureAlmostBasic PositiveNormLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NormalCurrentLoneLimit.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:X->Prop.
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Variable T:@current_space R h2 n U hU m.
Hypothesis hNormal:@is_normal_current R h2 n U hU m T.
Local Notation hT := (hNormal.1.1).
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Local Notation hm := (distribution_representation_measure
  (normalised_distribution_representation_laws hRepresentation)).
Local Notation I := (@current_representation_lone_integral R h2 n m U hU T mu eta hRepresentation).
Let total (f:X->Y):=partial_function_total (fun x:UT=>(f (set_val x):real_norm_metric_space hNY)).

(** Source for [normal_current_lone_limit_on_support]:
    the original L1 extension of a
    normal current preserves uniform convergence
    on its own support, supporting the
    all-class-one boundary formula in Federer
    4.1.7, p. 358. Every original
    continuous form is allowed; compact support
    of the forms is unnecessary. *)
Theorem normal_current_lone_limit_on_support radius (f:X->Y) (g:R->X->Y):
  0<radius->norm_class_zero (inner_norm (@euclidean_inner_productP R n)) NY U f->
  (forall e,0<e->e<radius->norm_class_zero (inner_norm (@euclidean_inner_productP R n)) NY U (g e))->
  (forall epsilon:R,0<epsilon->exists d:R,0<d /\forall e,0<e->e<d->
    forall x,@current_support R h2 n U hU m T x->NY (g e x-f x)<epsilon)->
  positive_norm_limit (fun t:R^o=>`|t|) (fun e=>I (total (g e))) (I (total f)).
Proof.
move=>hRadius hf hg hUniform.
have hFinite:=@compact_represented_current_finite_mass R h2 n m U hU T hT hNormal.2.
have [mass [hMassNonnegative hMass]]:=@current_finite_mass_value R h2 n m U hU T hFinite.
have hMeasureMass:mu setT=mass%:E.
  by rewrite -(@current_represented_mass_total R h2 n m U hU T hT) hMass.
have hMemberF:=@normal_current_continuous_lone_member R h2 n m U hU T hNormal f hf.
have hMemberG e (he:0<e) (her:e<radius):=
  @normal_current_continuous_lone_member R h2 n m U hU T hNormal (g e) (hg e he her).
have hSupportAlmost:measure_almost_everywhere mu
    [set x:UT|@current_support R h2 n U hU m T (set_val x)].
  exact:(@current_radon_outside_support_null R h2 n m U hU T hT).
apply:(@current_lone_almost_uniform_limit R h2 n m U hU T mu eta hRepresentation mass radius
  (fun x:UT=>f (set_val x)) (fun e (x:UT)=>g e (set_val x))
  hMeasureMass hRadius hMemberF hMemberG)=>epsilon hEpsilon.
have [d [hd hBound]]:=hUniform epsilon hEpsilon.
exists d;split=>// e he hed.
apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hSupportAlmost)=>x hx.
exact:hBound e he hed (set_val x) hx.
Qed.
End NormalCurrentLoneLimit.
