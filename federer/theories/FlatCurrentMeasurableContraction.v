(** Federer (1969), 4.1.17, p. 374: if T is flat with
    compact index K and finite mass, contraction by every
    ||T||-summable i-form is flat in degree m-i with the
    same K. Follow the printed proof: approximate the coefficient
    by actual compact smooth tests, use normal approximation for
    their contractions, and pass to the mass limit. The actual
    measurable contraction is the existing sealed operation of
    4.1.7, pp. 355–356. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentCoefficientCompleteness CurrentIntegrationCriterion NormalisedCurrentSealed
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothCompactSet
  CurrentContraction CurrentMeasurableMultiplierUP CurrentMeasurableProducts
  CurrentMeasurableSmoothAgreement CurrentMeasurableContractionLoneBound
  CurrentVariationFormLone CurrentMassSealed CurrentFiniteMassRepresentation
  FlatCurrentsUP FlatCurrentSmoothContraction FlatCurrentMassLimits
  MeasureIntegralUP SummableRealFunctionUP PartialFunctionUP PartialFunctionBasic
  MeasurableFunctionUP MeasureLpMembershipUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FlatCurrentMeasurableContraction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R n)).
Local Notation Y := (A_m X R^o k).
Local Notation NY := (@current_form_comass R h2 n k).
Local Notation hNY := (@current_form_comass_real_norm R h2 n k).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation UT := (current_domain R n U).
Local Notation C d := (@current_space R h2 n U hU d).
Local Notation flat d := (@is_flat_current_supported_in R h2 n d U hU K).
Local Notation E := (@current_smooth_space R h2 n U hU k).
Local Notation ev := (@current_smooth_value R h2 n U hU k).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU k).
Local Notation mu T hT := (@NormalisedCurrent.measure R h2 n (k+p) U hU T hT).
Local Notation represented := (@is_integration_representable_current R h2 n (k+p) U hU).
Local Notation field T hT := (is_locally_summable_current_field hNY (mu T hT)).
Local Notation contract T hT f hf := (@current_measurable_contraction R h2 n k p U hU T hT f hf).

(** Source for [flat_current_measurable_contraction_supported]:
    the L1 limiting step in Federer 4.1.17, p. 374.
    A represented same-index flat current remains flat after
    contraction by every globally variation-summable coefficient.
    The proof also works without finite total mass of T; the
    original finite-mass assertion is retained separately below.
    No boundedness or smoothness of the coefficient is imposed. *)
Theorem flat_current_measurable_contraction_supported
    (T:C (k+p)) (hT:represented T) (f:UT->Y) (hF:field T hT f):
  flat (k+p) T->
  is_measure_lp_function (mu T hT) 1 (partial_function_total
    (fun x=>(f x:real_norm_metric_space hNY)))->
  flat p (contract T hT f hF).
Proof.
move=>hFlat hLone.
have[D [hD hBound]]:=@current_measurable_contraction_lone_bound
  R h2 n k p U hU T hT.
apply:(@flat_current_mass_approximation_closed R h2 n p U hU K
  (contract T hT f hF))=>epsilon hEpsilon.
have hDenominator:0<D+1 by lra.
pose delta:=epsilon/(D+1).
have hDelta:0<delta by rewrite /delta divr_gt0.
have[psi [a [hIntegral hError]]]:=@current_variation_form_test_lone_dense
  R h2 n (k+p) k U hU T hT f hLone delta hDelta.
pose gamma:E:=smooth_test_inclusion hE psi.
pose g:=fun x:UT=>ev gamma (set_val x).
pose hG:=@current_smooth_form_variation_summable R h2 n k p U hU T hT gamma.
have hIntegralG:is_measure_integral (mu T hT)
    (real_total_integrand (fun x=>NY (f x-g x))) a%:E.
  exact:hIntegral.
have hMass:=hBound f g hF hG a hIntegralG.
have hAgreement:=@current_measurable_contraction_smooth_agreement
  R h2 n k p U hU T hT gamma.
change (contract T hT g hG=@current_contraction R h2 n k p U hU gamma T)
  in hAgreement.
rewrite hAgreement in hMass.
exists (@current_contraction R h2 n k p U hU gamma T);split.
- exact:(@flat_current_smooth_contraction_supported R h2 n k p U hU
    K gamma T hFlat).
- apply:(le_lt_trans hMass);rewrite lte_fin.
  have hFirst:=ler_wpM2l hD (ltW hError).
  have hStrict:D*delta<(D+1)*delta.
    rewrite (ltr_pM2r hDelta);lra.
  have hEndpoint:(D+1)*delta=epsilon.
    by rewrite /delta mulrC divfK ?gt_eqF.
  rewrite hEndpoint in hStrict;exact:le_lt_trans hFirst hStrict.
Qed.

(** Source for [federer_4_1_17_measurable_contraction]: the
    original second assertion of Federer 4.1.17, p. 374.
    Every measurable ||T||-summable k-form contracts a finite-mass
    flat (k+p)-current to a flat p-current with the same K.
    The arbitrary local-summability witness affects no added
    mathematical hypothesis: it follows from the printed summability.
    Both zero-degree endpoints and every compact index are retained. *)
Theorem federer_4_1_17_measurable_contraction
    (T:C (k+p)) (hT:represented T) (f:UT->Y) (hF:field T hT f):
  flat (k+p) T->(@CurrentMass.value R h2 n (k+p) U hU T< +oo)%E->
  is_measure_measurable_function (mu T hT) (partial_function_total
    (fun x=>(f x:real_norm_metric_space hNY)))->
  is_measure_summable (mu T hT) (real_total_integrand (fun x=>NY (f x)))->
  flat p (contract T hT f hF).
Proof.
move=>hFlat hMass hMeasurable hSummable.
exact (@flat_current_measurable_contraction_supported T hT f hF hFlat
  (@current_variation_summable_form_lone R h2 n (k+p) k U hU
    T hT f hMeasurable hSummable)).
Qed.

(** Source for [federer_4_1_17_summable_contraction]: the same
    original conclusion with all representation and local-summability
    evidence derived from the printed assumptions, Federer 4.1.17,
    p. 374. The result concerns the pre-existing actual measurable
    contraction; no new current or coefficient extension is defined. *)
Theorem federer_4_1_17_summable_contraction
    (T:C (k+p)) (hMass:(@CurrentMass.value R h2 n (k+p) U hU T< +oo)%E)
    (f:UT->Y):
  let hT:=@current_finite_mass_representation R h2 n (k+p) U hU T hMass in
  flat (k+p) T->
  is_measure_measurable_function (mu T hT) (partial_function_total
    (fun x=>(f x:real_norm_metric_space hNY)))->
  is_measure_summable (mu T hT) (real_total_integrand (fun x=>NY (f x)))->
  exists hF:field T hT f,flat p (contract T hT f hF).
Proof.
move=>hT hFlat hMeasurable hSummable.
have hLone:=@current_variation_summable_form_lone R h2 n (k+p) k U hU
  T hT f hMeasurable hSummable.
pose hLocal:=@current_variation_form_lone_locally_summable R h2 n (k+p) k
  U hU T hT f hLone.
exists hLocal.
exact (@flat_current_measurable_contraction_supported T hT f hLocal hFlat hLone).
Qed.
End FlatCurrentMeasurableContraction.
