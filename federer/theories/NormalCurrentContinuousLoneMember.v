(** Federer (1969), 4.1.7, p. 358:
    every continuous form belongs to the
    variation L1 space of a normal
    current. The form need not have
    compact support or a global bound.
    The current's original compact support
    supplies the required almost-everywhere bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology functions.
From Federer Require Import PartialFunctionPreimages RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormClassZeroTopology
  NormCompactFunctionBound InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentDomain
  NormalCurrentsUP CurrentIntegrationCriterion NormalisedCurrentSealed CurrentRadonSupport
  CurrentMassBasic CurrentMassRepresentation CompactRepresentedCurrentMass
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  RadonMeasureUP MeasurableFunctionUP MeasurableNormedFunctionUP SeparableTargetNormedMeasurability
  MeasureLpMembershipUP FiniteMeasureBoundedNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NormalCurrentContinuousLoneMember.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Variable T:@current_space R h2 n U hU m.
Hypothesis hNormal:@is_normal_current R h2 n U hU m T.
Local Notation hT := (hNormal.1.1).
Local Notation support := (@current_support R h2 n U hU m T).
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Local Notation hBase := (normalised_distribution_representation_laws hRepresentation).
Local Notation hm := (distribution_representation_measure hBase).
Local Notation hr := (distribution_representation_radon hBase).

(** Source for [normal_current_continuous_lone_member]:
    every original continuous form on U
    is in L1(||T||) when T is
    normal, supporting the all-class-one boundary
    equation in Federer 4.1.7, p. 358.
    Only compact support of T is
    used; the form retains its full
    original domain. *)
Theorem normal_current_continuous_lone_member (w:X->Y):
  norm_class_zero NX NY U w->
  is_measure_lp_function mu 1 (partial_function_total
    (fun x:UT=>(w (set_val x):real_norm_metric_space hNY))).
Proof.
move=>hContinuous.
have hFinite:=@compact_represented_current_finite_mass R h2 n m U hU T hT hNormal.2.
have [mass [hMassNonnegative hMass]]:=@current_finite_mass_value R h2 n m U hU T hFinite.
have hMeasureMass:mu setT=mass%:E.
  by rewrite -(@current_represented_mass_total R h2 n m U hU T hT) hMass.
have [bound [hBoundPositive hBound]]:=@norm_class_zero_compact_bounded R X Y NX NY hNX hNY
  U support w hNormal.2 (fun x hx=>hx.1) hContinuous.
have hMap:continuous (fun x:UT=>(w (set_val x):real_norm_metric_space hNY)).
  exact:(@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY U w hContinuous).
have hMeas:is_measure_measurable_function mu (partial_function_total
    (fun x:UT=>(w (set_val x):real_norm_metric_space hNY))).
  constructor.
  - rewrite partial_function_total_domain;exact:measure_almost_everywhere_true hm.
  - move=>G hG;rewrite partial_function_total_preimage.
    exact:(@radon_open_measurable R UT mu hr
      ((fun x:UT=>(w (set_val x):real_norm_metric_space hNY)) @^-1` G)
      ((@continuousP UT (real_norm_metric_space hNY) _).1 hMap G hG)).
have [C [hCountable hDense]]:=@current_form_separable R h2 n m.
have hNormed:=@separable_target_measurable_normed R UT Y NY hNY C mu hm
  (partial_function_total (fun x:UT=>(w (set_val x):real_norm_metric_space hNY)))
  hCountable hDense hMeas.
have hSupportAlmost:measure_almost_everywhere mu [set x:UT|support (set_val x)].
  exact:(@current_radon_outside_support_null R h2 n m U hU T hT).
have hBoundAlmost:measure_almost_everywhere mu
    (partial_function_preimage (partial_function_total
      (fun x:UT=>(w (set_val x):real_norm_metric_space hNY))) [set y|NY y<=bound]).
  apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hSupportAlmost)=>x hx.
  exists (w (set_val x));split;first by [].
  exact:hBound (set_val x) hx.
exact:(@finite_measure_bounded_norm_lp_one R UT Y NY hNY mu hm mass bound
  (partial_function_total (fun x:UT=>(w (set_val x):real_norm_metric_space hNY)))
  hMeasureMass hNormed hBoundAlmost).
Qed.
End NormalCurrentContinuousLoneMember.
