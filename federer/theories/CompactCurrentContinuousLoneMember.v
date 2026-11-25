(** Federer (1969), 4.1.14, p. 372: the last
    class-one identity evaluates a finite-mass compact flat
    current on every continuous form. Compact support of the
    represented current, rather than normality, supplies the
    almost-everywhere bound in the preceding L1 argument
    of 4.1.7, pp. 356–358. The form retains its
    original domain and need not have compact support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology functions.
From Federer Require Import PartialFunctionPreimages RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormClassZeroTopology
  NormCompactFunctionBound InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentDomain
  NormalCurrentsUP CurrentIntegrationCriterion NormalisedCurrentSealed CurrentRadonSupport
  CurrentMassSealed CurrentMassBasic CurrentMassRepresentation CompactRepresentedCurrentMass
  CurrentFiniteMassRepresentation
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
Section CompactCurrentContinuousLoneMember.
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
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Hypothesis hCompact:@compact (real_norm_metric_space hNX)
  (@current_support R h2 n U hU m T).
Local Notation support := (@current_support R h2 n U hU m T).
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Local Notation hBase := (normalised_distribution_representation_laws hRepresentation).
Local Notation hm := (distribution_representation_measure hBase).
Local Notation hr := (distribution_representation_radon hBase).

(** Source for [compact_represented_current_continuous_lone_member]:
    every original continuous form on U is in L1(||T||)
    for an actual compactly supported represented current,
    supporting the last assertion of Federer 4.1.14,
    p. 372. Normality is not used. The preceding
    Radon support and one-Lipschitz extension laws supply
    the finite integral on the full original domain. *)
Theorem compact_represented_current_continuous_lone_member (w:X->Y):
  norm_class_zero NX NY U w->
  is_measure_lp_function mu 1 (partial_function_total
    (fun x:UT=>(w (set_val x):real_norm_metric_space hNY))).
Proof.
move=>hContinuous.
have hFinite:=@compact_represented_current_finite_mass R h2 n m U hU T hT hCompact.
have [mass [hMassNonnegative hMass]]:=@current_finite_mass_value R h2 n m U hU T hFinite.
have hMeasureMass:mu setT=mass%:E.
  by rewrite -(@current_represented_mass_total R h2 n m U hU T hT) hMass.
have [bound [hBoundPositive hBound]]:=@norm_class_zero_compact_bounded R X Y NX NY hNX hNY
  U support w hCompact (fun x hx=>hx.1) hContinuous.
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
End CompactCurrentContinuousLoneMember.

(** Source for [finite_mass_compact_current_continuous_lone_member]:
    finite mass and compact support suffice for the continuous
    form action in Federer 4.1.14, p. 372. The
    earlier finite-mass representation theorem supplies the
    original representation; no premise about its existence
    or normality is added to the finite-mass statement. *)
Theorem finite_mass_compact_current_continuous_lone_member
    (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hFinite:(@CurrentMass.value R h2 n m U hU T< +oo)%E)
    (hCompact:@compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n U hU m T))
    (w:R_n R n->A_m (R_n R n) R^o m):
  norm_class_zero (inner_norm (@euclidean_inner_productP R n))
    (@current_form_comass R h2 n m) U w->
  is_measure_lp_function
    (@NormalisedCurrent.measure R h2 n m U hU T
      (@current_finite_mass_representation R h2 n m U hU T hFinite))
    1 (partial_function_total (fun x:current_domain R n U=>
      (w (set_val x):real_norm_metric_space (@current_form_comass_real_norm R h2 n m)))).
Proof.
exact:(@compact_represented_current_continuous_lone_member R h2 n m U hU T
  (@current_finite_mass_representation R h2 n m U hU T hFinite) hCompact w).
Qed.
