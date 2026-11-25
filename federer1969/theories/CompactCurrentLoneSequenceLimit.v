(** Federer (1969), 4.1.14, p. 372: the final
    class-one identity is tested on every continuous form.
    Uniform convergence on the actual current support passes
    through its original L1 action using finite variation,
    without normality, global bounds or compactly supported
    continuous forms. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology functions.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  CurrentCoefficientNorms CurrentSpaces CurrentDomain CurrentIntegrationCriterion NormalCurrentsUP
  NormalisedCurrentSealed CurrentRadonSupport CurrentMassBasic CurrentMassRepresentation CompactRepresentedCurrentMass
  CompactCurrentContinuousLoneMember CurrentOriginalBallFormula CurrentLoneSequenceLimit
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionBasic MeasureAlmostUP MeasureAlmostBasic PositiveNormLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactCurrentLoneSequenceLimit.
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
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Hypothesis hCompact:@compact (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n U hU m T).
Local Notation support := (@current_support R h2 n U hU m T).
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Local Notation hm := (distribution_representation_measure
  (normalised_distribution_representation_laws hRepresentation)).
Local Notation I := (@current_representation_lone_integral R h2 n m U hU T mu eta hRepresentation).
Let total (f:X->Y):=partial_function_total (fun x:UT=>(f (set_val x):real_norm_metric_space hNY)).

(** Source for [compact_current_lone_almost_uniform_sequence_limit_on_support]:
    almost-everywhere uniform convergence on the original
    support suffices for convergence of the actual L1
    actions in Federer 4.1.14, p. 372. The
    continuous fields may be unbounded off the compact
    support. The current need not be normal. *)
Theorem compact_current_lone_almost_uniform_sequence_limit_on_support
    (f:X->Y) (g:nat->X->Y):
  norm_class_zero (inner_norm (@euclidean_inner_productP R n)) NY U f->
  (forall k,norm_class_zero (inner_norm (@euclidean_inner_productP R n)) NY U (g k))->
  (forall epsilon:R,0<epsilon->exists k,forall L,(k<=L)%N->
    measure_almost_everywhere mu
      [set x:UT|support (set_val x)->NY (g L (set_val x)-f (set_val x))<epsilon])->
  forall epsilon:R,0<epsilon->exists k,forall L,(k<=L)%N->
    `|I (total (g L))-I (total f)|<epsilon.
Proof.
move=>hf hg hUniform.
have hFinite:=@compact_represented_current_finite_mass R h2 n m U hU T hT hCompact.
have[mass [hMassNonnegative hMass]]:=@current_finite_mass_value R h2 n m U hU T hFinite.
have hMeasureMass:mu setT=mass%:E.
  by rewrite -(@current_represented_mass_total R h2 n m U hU T hT) hMass.
have hMemberF:=@compact_represented_current_continuous_lone_member
  R h2 n m U hU T hT hCompact f hf.
have hMemberG k:=@compact_represented_current_continuous_lone_member
  R h2 n m U hU T hT hCompact (g k) (hg k).
have hSupportAlmost:measure_almost_everywhere mu
    [set x:UT|support (set_val x)].
  exact:(@current_radon_outside_support_null R h2 n m U hU T hT).
apply:(@current_lone_almost_uniform_sequence_limit R h2 n m U hU T mu eta
  hRepresentation mass (fun x:UT=>f (set_val x))
  (fun k (x:UT)=>g k (set_val x)) hMeasureMass hMemberF hMemberG)=>epsilon hEpsilon.
have[k hBound]:=hUniform epsilon hEpsilon.
exists k=>L hL.
have hBoth:=@measure_almost_everywhere_and R UT mu hm _ _ hSupportAlmost (hBound L hL).
apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hBoth)=>x [hSupport hPoint].
exact:hPoint hSupport.
Qed.

(** Source for [compact_current_lone_sequence_limit_on_support]:
    uniform convergence on every point of the original
    current support gives convergence of the full continuous
    form actions, supporting the last sentence of Federer
    4.1.14, p. 372. Neither smoothness nor compact
    support of the continuous forms is assumed. Empty
    supports and zero-dimensional coefficient spaces are retained. *)
Theorem compact_current_lone_sequence_limit_on_support (f:X->Y) (g:nat->X->Y):
  norm_class_zero (inner_norm (@euclidean_inner_productP R n)) NY U f->
  (forall k,norm_class_zero (inner_norm (@euclidean_inner_productP R n)) NY U (g k))->
  (forall epsilon:R,0<epsilon->exists k,forall L,(k<=L)%N->
    forall x,support x->NY (g L x-f x)<epsilon)->
  forall epsilon:R,0<epsilon->exists k,forall L,(k<=L)%N->
    `|I (total (g L))-I (total f)|<epsilon.
Proof.
move=>hf hg hUniform.
apply:(compact_current_lone_almost_uniform_sequence_limit_on_support hf hg)=>epsilon hEpsilon.
have[k hBound]:=hUniform epsilon hEpsilon.
exists k=>L hL.
apply:(@measure_almost_everywhere_mono R UT mu hm setT _ _
  (measure_almost_everywhere_true hm))=>x _ hSupport.
exact:hBound L hL (set_val x) hSupport.
Qed.
End CompactCurrentLoneSequenceLimit.
