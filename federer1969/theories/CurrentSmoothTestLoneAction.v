(** Federer (1969), 4.1.14, p. 372: first prove
    the class-one action formula on original compact target
    tests. For a smooth approximating map, the earlier
    pushforward integral of 4.1.7, p. 359, is
    exactly the original L1 action of its pointwise
    pullback. No normality of the current is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading ExteriorMaps AlternatingForms AlternatingDual
  AlternatingPairing CurrentCoefficientNorms CurrentSpaces CurrentDomain
  CurrentMapDifferential CurrentMapDifferentialNormContinuity
  CurrentIntegrationCriterion NormalisedCurrentSealed MultivectorDualSealed
  CurrentOriginalBallFormula CurrentLoneExtension CompactCurrentContinuousLoneMember
  CurrentContinuousPullbackUniform CurrentImageDensityPairing
  CurrentPushforwardIntegralAction CurrentCompactMapProper CurrentCompactPushforwardAlgebra
  SmoothTestSpaces SmoothTestEvaluation PartialFunctionBasic
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentSmoothTestLoneAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation A := (A_m X R^o m).
Local Notation PN := (@current_form_comass R h2 n m).
Local Notation hPN := (@current_form_comass_real_norm R h2 n m).
Local Notation QN := (@current_form_comass R h2 nu m).
Variables (U:X->Prop) (V:Y->Prop).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hSmooth:norm_class_all_orders hNX hNY U f.
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Hypothesis hCompact:@compact (real_norm_metric_space hNX)
  (@current_support R h2 n U hU m T).
Local Notation UT := (current_domain R n U).
Local Notation mu := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Local Notation I := (@current_representation_lone_integral R h2 n m U hU T
  mu xi hRepresentation).
Local Notation D := (@current_map_differential R n nu U f).
Local Notation value := (@current_test_value R h2 nu V hV m).

(** Source for [current_smooth_test_lone_pullback_action]:
    the original smooth image action on every actual
    compact target test is exactly T of its pointwise
    pullback in the original L1 extension, supporting
    Federer 4.1.14, p. 372, by 4.1.7, p. 359.
    The source current is any compact represented current. *)
Theorem current_smooth_test_lone_pullback_action
    (psi:@current_test_space R h2 nu V hV m):
  I (partial_function_total (fun x:UT=>
      (A_m_dual (hom_as_linear (D (set_val x)))
        (value psi (f (set_val x))):real_norm_metric_space hPN)))=
  @current_value R h2 nu V hV m
    (@current_compact_map_pushforward R h2 n nu U V hU hV f hImage hSmooth
      m T hCompact) psi.
Proof.
pose w:=fun x=>A_m_dual (hom_as_linear (D x)) (value psi (f x)).
have hPsi:norm_class_zero NY QN V (value psi).
  exact:(norm_class_continuous
    (@smooth_test_value_smooth R Y (A_m Y R^o m) NY QN hNY
      (@current_form_comass_real_norm R h2 nu m) V
      (@current_smooth_space R h2 nu V hV m)
      (@current_smooth_value R h2 nu V hV m)
      (@current_smooth_space_laws R h2 nu V hV m) psi 0%N)).
have hD:=@current_class_one_differential_continuous R n nu U f (hSmooth 1%N).
have hW:norm_class_zero NX PN U w.
  exact:(@current_continuous_pullback_class R h2 n nu m U V f D hImage
    (norm_class_continuous (hSmooth 0%N)) hD (value psi) hPsi).
have hMember:=@compact_represented_current_continuous_lone_member R h2 n m
  U hU T hT hCompact w hW.
have hLone:=@current_representation_lone_total_action R h2 n m U hU
  T mu xi hRepresentation (fun x:UT=>w (set_val x)) hMember.
pose hp:=@current_compact_map_proper R h2 n nu m U V hU T f hImage
  (norm_class_continuous (hSmooth 0%N)) hCompact.
have hOriginal:=@current_pushforward_original_integral_action R h2 n nu m
  U V hU hV T hT f hImage hSmooth hp psi.
have hPairing:(fun x:UT=>@MultivectorDual.evaluation R X m (xi x) (w (set_val x)))=
    (fun x:UT=>pairing (@current_image_density R n nu m U f xi x)
      (value psi (f (set_val x)))).
  apply:funext=>x.
  by rewrite /w (@MultivectorDual.laws R X m) A_m_dual_pairing.
rewrite hPairing in hLone.
exact:(EFin_inj (measure_integral_unique hLone hOriginal)).
Qed.
End CurrentSmoothTestLoneAction.
