(** Federer (1969), 4.1.14, p. 372: for the
    original global flat current T with finite mass,
    a class-one f satisfies (f#T)(phi)=T(f#phi) for
    every continuous target form. Apply the candidate law
    through the actual opaque global image. A compact
    index is selected only inside the proof. *)
From mathcomp Require Import all_boot all_order all_algebra functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct LipschitzUP AlternatingForms AlternatingDual
  CurrentCoefficientNorms CurrentSpaces CurrentDomain CurrentMapDifferential
  CurrentMassSealed CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentOriginalBallFormula FlatCurrentsUP CurrentFlatLipschitzPushforwardUP
  CurrentFlatLipschitzPushforwardSealed CurrentClassOneCandidateContinuousAction
  PartialFunctionBasic MeasureUP MeasureLpMembershipUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentFlatLipschitzClassOneAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation PN := (@current_form_comass R h2 n m).
Local Notation QN := (@current_form_comass R h2 nu m).
Local Notation hPN := (@current_form_comass_real_norm R h2 n m).
Local Notation hQN := (@current_form_comass_real_norm R h2 nu m).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Hypothesis hClass:norm_class_one NX NY U f.
Variable T:@current_space R h2 n U hU m.
Hypothesis hFlat:@is_flat_current R h2 n m U hU T.
Hypothesis hFinite:(@CurrentMass.value R h2 n m U hU T< +oo)%E.
Local Notation Q := (@CurrentFlatLipschitzPushforward.value R h2 n nu m
  U V hU hV f hImage hLocal T hFlat).
Local Notation UT := (current_domain R n U).
Local Notation VT := (current_domain R nu V).
Local Notation D := (@current_map_differential R n nu U f).
Local Notation totalT w := (partial_function_total
  (fun x:UT=>(w (set_val x):real_norm_metric_space hPN))).
Local Notation totalQ w := (partial_function_total
  (fun y:VT=>(w (set_val y):real_norm_metric_space hQN))).
Local Notation muT hT := (@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation xiT hT := (@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation repT hT := (@NormalisedCurrent.laws R h2 n m U hU T hT).
Local Notation muQ hQ := (@NormalisedCurrent.measure R h2 nu m V hV Q hQ).
Local Notation xiQ hQ := (@NormalisedCurrent.auxiliary_density R h2 nu m V hV Q hQ).
Local Notation repQ hQ := (@NormalisedCurrent.laws R h2 nu m V hV Q hQ).
Local Notation IT hT := (@current_representation_lone_integral R h2 n m U hU T
  (muT hT) (xiT hT) (repT hT)).
Local Notation IQ hQ := (@current_representation_lone_integral R h2 nu m V hV Q
  (muQ hQ) (xiQ hQ) (repQ hQ)).
Local Notation pull phi := (fun x=>A_m_dual (hom_as_linear (D x)) (phi (f x))).

(** Source for [current_flat_lipschitz_class_one_continuous_action]:
    the literal final class-one continuous-form identity
    of Federer 4.1.14, p. 372, on all original
    F_m(U) with finite mass. Both L1 memberships and
    finite image mass are conclusions, with every original
    representation witness. No compact index, normality,
    form smoothness or form support is an extra premise. *)
Theorem current_flat_lipschitz_class_one_continuous_action:
  (@CurrentMass.value R h2 nu m V hV Q< +oo)%E /\
  forall (hT:@is_integration_representable_current R h2 n m U hU T)
    (hQ:@is_integration_representable_current R h2 nu m V hV Q)
    (phi:Y->A_m Y R^o m),
    norm_class_zero NY QN V phi->
    is_measure_lp_function (muQ hQ) 1 (totalQ phi) /\
    is_measure_lp_function (muT hT) 1 (totalT (pull phi)) /\
    IQ hQ (totalQ phi)=IT hT (totalT (pull phi)).
Proof.
have[K hK]:=hFlat.
have hPoint:=(@CurrentFlatLipschitzPushforward.laws R h2 n nu m
  U V hU hV f hImage hLocal T hFlat).2 K hK.
exact:(@current_class_one_candidate_continuous_action R h2 n nu m
  U V hU hV f hImage hLocal hClass K T hK hFinite Q hPoint).
Qed.
End CurrentFlatLipschitzClassOneAction.
