(** Federer (1969), 4.1.7, p. 359:
    f#(T restricted to f inverse B)
    equals f#T restricted to B for
    every original Borel subset B of V.
    The preceding bounded Baire projection theorem
    is applied to the actual characteristic
    zero-form, with no finite-measure hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero CurrentDomain CurrentCoefficientNorms
  CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed CurrentProperSupport CurrentProperSupportDomain
  CurrentPushforwardSealed CurrentPushforwardVariation CurrentPushforwardBaireProjection CurrentPushforwardCongruence
  CurrentFormPullbackOnDomain CurrentBorelZeroForm CurrentCharacteristicContraction CurrentMeasurableRestriction
  CurrentMeasurableProducts DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP RadonMeasureUP RadonBorelRegularity BorelRegularMeasureUP TopologicalBorel BorelFunctionBasic
  CharacteristicFunctionUP CharacteristicFunctionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardBorelRestriction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Local Notation UT := (current_domain R v U).
Local Notation VT := (current_domain R n V).
Variable T:@current_space R h2 v U hU m.
Hypothesis hT:@is_integration_representable_current R h2 v m U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 v m U hU T hT).
Local Notation hRT := (@NormalisedCurrent.laws R h2 v m U hU T hT).
Let hm:=distribution_representation_measure (normalised_distribution_representation_laws hRT).
Let hr:=distribution_representation_radon (normalised_distribution_representation_laws hRT).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hp:@is_current_proper_on_support R h2 v n m U hU V T f hImage.
Local Notation fU := (@current_map_on_domain R v n U V f hImage).
Local Notation S := (@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hp).
Let hS:=@current_pushforward_representable R h2 v n m U V hU hV T hT f hImage hf hp.
Local Notation rho := (@NormalisedCurrent.measure R h2 n m V hV S hS).
Local Notation hRS := (@NormalisedCurrent.laws R h2 n m V hV S hS).
Let hn:=distribution_representation_measure (normalised_distribution_representation_laws hRS).
Let hs:=distribution_representation_radon (normalised_distribution_representation_laws hRS).
Variable B:set VT.
Hypothesis hB:borel_set B.
Local Notation A := (fU @^-1` B).
Let hF:=@current_map_on_domain_continuous R v n U V f hImage (norm_class_continuous (hf 0%N)).
Let hAM:measure_measurable mu A:=@borel_regular_borel_measurable R UT mu hm
  (radon_borel_regular hm hr) A (borel_function_preimage (continuous_borel_function hF) hB).
Let hBM:measure_measurable rho B:=@borel_regular_borel_measurable R VT rho hn
  (radon_borel_regular hn hs) B hB.
Local Notation psi := (@current_borel_zero_form R n V B).
Let hPsi:=@current_borel_zero_form_baire R h2 n V B hB.
Let hBound:=@current_borel_zero_form_bound R h2 n V B.
Local Notation CS := (@current_baire_source_contraction R h2 v n 0%N m U V hU hV
  T hT f hImage hf psi 1 hPsi ler01 hBound).
Local Notation CT := (@current_baire_target_contraction R h2 v n 0%N m U V hU hV
  T hT f hImage hf hp psi 1 hPsi ler01 hBound).
Let hCS:=@current_baire_source_contraction_proper R h2 v n 0%N m U V hU hV
  T hT f hImage hf hp psi 1 hPsi ler01 hBound.
Local Notation RS := (@current_measurable_restriction R h2 v m U hU T hT A hAM).
Local Notation RT := (@current_measurable_restriction R h2 n m V hV S hS B hBM).

(** Source for [current_borel_source_characteristic_contraction]:
    the actual source characteristic contraction
    is exactly restriction to the original
    inverse image, supporting Federer 4.1.7,
    p. 359. Characteristic uniqueness identifies
    the two actual scalar witnesses. *)
Lemma current_borel_source_characteristic_contraction:CS=RS.
Proof.
apply:(@current_characteristic_contraction_restriction R h2 v m U hU T hT A hAM
  (@current_form_pullback_on_domain R v n 0%N U V f psi) _).
move=>x.
rewrite (@current_borel_zero_form_pullback R n V B v U f hImage hf x).
have hComp:is_characteristic_function A
    (fun z:UT=>@CharacteristicFunction.value R VT B (fU z)).
  constructor.
  - move=>z hz;exact:(characteristic_on_set (@CharacteristicFunction.laws R VT B) hz).
  - move=>z hz;exact:(characteristic_off_set (@CharacteristicFunction.laws R VT B) hz).
by rewrite (@characteristic_function_unique R UT A _ _ hComp (@CharacteristicFunction.laws R UT A) x).
Qed.

(** Source for [current_borel_target_characteristic_contraction]:
    the actual target characteristic contraction
    is exactly restriction to B, supporting
    Federer 4.1.7, p. 359. Its
    original f#T variation measure is retained. *)
Lemma current_borel_target_characteristic_contraction:CT=RT.
Proof.
apply:(@current_characteristic_contraction_restriction R h2 n m V hV S hS B hBM
  (fun y:VT=>psi (set_val y)) _).
move=>y;exact:(@current_borel_zero_form_values R n V B y).
Qed.

(** Source for [current_borel_restriction_proper]:
    original support-properness of f also holds
    on T restricted to f inverse B,
    supporting Federer 4.1.7, p. 359.
    No properness assumption on the whole
    source domain is added. *)
Theorem current_borel_restriction_proper:
  @is_current_proper_on_support R h2 v n m U hU V RS f hImage.
Proof.
rewrite -current_borel_source_characteristic_contraction;exact:hCS.
Qed.

(** Source for [current_pushforward_borel_restriction]:
    the original identity f#(T restricted
    to f inverse B)=(f#T) restricted to B,
    Federer 4.1.7, p. 359, for
    every original relative Borel subset B.
    The preceding represented theorem includes
    the printed locally normal and normal cases. *)
Theorem current_pushforward_borel_restriction:
  @CurrentPushforward.value R h2 v n m U V hU hV RS f hImage hf current_borel_restriction_proper=RT.
Proof.
have hProjection:=@current_pushforward_baire_projection R h2 v n 0%N m U V hU hV
  T hT f hImage hf hp psi 1 hPsi ler01 hBound.
have hSame:=@current_pushforward_current_congruence R h2 v n m U V hU hV f hImage hf
  CS RS hCS current_borel_restriction_proper current_borel_source_characteristic_contraction.
exact:(eq_trans (esym hSame) (eq_trans hProjection current_borel_target_characteristic_contraction)).
Qed.
End CurrentPushforwardBorelRestriction.
