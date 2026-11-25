(** Federer (1969), 4.1.7, p. 359:
    the actual pullback of a bounded
    Baire form is locally variation-summable.
    Original finite covector coordinates multiply
    genuine smooth pulled-back generators. The earlier
    measurable operations, compact bounds and Radon
    compact integrals prove every input condition
    for the actual measurable current contraction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Annihilator Hom RealNormUP NormMetric RealMetricBackground NormDifferentialUP NormClassOneUP NormRegularity
  NormBoundedLinearTopology ScalarNormExtendedEmbedding InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingDual LinearBasis FiniteDualDimension
  CurrentDomain CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentConstantFields
  CurrentProperSupportDomain CurrentUnitSmoothPairing CurrentFormPullbackOnDomain SmoothFormPullbackSealed
  FiniteScalarContinuousCombination CurrentMeasurableMultiplierUP MeasurableCompactNormIntegral
  PartialFunctionBasic MeasureUP RadonMeasureUP MeasurableFunctionUP MeasurableIdentityCriterion
  MeasurableTotalBasic BorelFunctionBasic BaireFunctions BaireBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentBaireFormPullback.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n k:nat.
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
Local Notation A := (A_m Y R^o k).
Local Notation AN := (@current_form_comass R h2 n k).
Local Notation hAN := (@current_form_comass_real_norm R h2 n k).
Local Notation B := (A_m X R^o k).
Local Notation BN := (@current_form_comass R h2 v k).
Local Notation hBN := (@current_form_comass_real_norm R h2 v k).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation fU := (@current_map_on_domain R v n U V f hImage).
Local Notation P := (@current_form_pullback_on_domain R v n k U V f).
Local Notation pull := (@SmoothFormPullback.operator R h2 v n k U V hU hV f hImage hf).

(** Source for [current_baire_form_pullback_locally_summable]:
    every original bounded Baire k-form
    pulls back to a measurable field
    with finite norm integral on each
    compact source set, supporting Federer
    4.1.7, p. 359. No whole-domain
    bound on Df or source compactness
    is added. *)
Theorem current_baire_form_pullback_locally_summable
    (mu:set UT->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (psi:Y->A) (C:R):
  @is_baire_function R VT (real_norm_metric_space hAN)
    (fun y:VT=>(psi (set_val y):real_norm_metric_space hAN))->
  0<=C->(forall y,V y->AN (psi y)<=C)->
  is_locally_summable_current_field hBN mu (P psi).
Proof.
move=>hPsi hC hBound.
have [d [a ha]]:=@current_form_finite_basis R h2 n k.
pose alpha (i:'I_d) (x:UT):=dual_basis ha i (psi (f (set_val x))).
pose b (i:'I_d) (x:UT):=P (fun _=>a i) x.
have hExpansion:(fun x:UT=>P psi x)=(fun x=>\sum_i alpha i x*:b i x).
  apply:funext=>x.
  rewrite (@current_form_pullback_on_domain_actual R v n k U V f psi hImage hf x).
  rewrite (@basis_vector_expansion R A d a ha (psi (f (set_val x)))) linear_sum.
  apply:eq_bigr=>i _;rewrite linearZ.
  congr (_ *: _);exact:esym (@current_form_pullback_on_domain_actual R v n k U V f
    (fun _=>a i) hImage hf x).
have hBContinuous i:continuous (fun x:UT=>(b i x:real_norm_metric_space hBN)).
  have hValues:(fun x:UT=>b i x)=(fun x=>@current_smooth_value R h2 v U hU k
      (pull (@current_constant_form R h2 n V hV k (a i))) (set_val x)).
    apply:funext=>x;exact:(@current_form_pullback_on_domain_constant R v n k U V f
      h2 hU hV hImage hf (a i) x).
  rewrite hValues.
  exact:(@current_unit_smooth_pairing_continuous_field R h2 v k U hU
    (pull (@current_constant_form R h2 n V hV k (a i)))).
have hF:=@current_map_on_domain_continuous R v n U V f hImage
  (norm_class_continuous (hf 0%N)).
have hIdentity:=(@measurable_identity_iff_open_sets R UT mu hm).2 (radon_open_measurable hr).
have hLinearBound i:=@current_form_linear_bounded R h2 n k R^o (fun t:R^o=>`|t|)
  (@scalar_absolute_value_norm R) (dual_basis ha i).
have hAlphaMeas i:is_measure_measurable_function mu
    (partial_function_total (fun x=>(alpha i x:real_line_metric R))).
  have hCoord:continuous (fun y:real_norm_metric_space hAN=>(dual_basis ha i y:real_line_metric R)).
    have hLinear:=@norm_bounded_linear_continuous R A R^o AN (fun t:R^o=>`|t|)
      hAN (@scalar_absolute_value_norm R) (dual_basis ha i) (hLinearBound i).
    move=>y;exact:(continuous_comp (hLinear y)
      (@scalar_norm_real_identity_continuous R (dual_basis ha i y))).
  have hBorel:=borel_function_composition (continuous_borel_function hF) (baire_function_borel hPsi).
  have hComposite:=borel_function_composition hBorel (continuous_borel_function hCoord).
  exact:(@measurable_total_borel_postcomposition R UT UT (real_line_metric R)
    mu hm id (fun x=>alpha i x) hIdentity hComposite).
have hMeas:is_measure_measurable_function mu
    (partial_function_total (fun x:UT=>(P psi x:real_norm_metric_space hBN))).
  rewrite hExpansion.
  exact:(@finite_scalar_continuous_combination_measurable R UT B BN hBN
    (@current_form_separable R h2 v k) d alpha b hBContinuous mu hm hr hAlphaMeas).
have [L hL]:=choice hLinearBound.
have hAlphaBound i x:`|alpha i x|<=L i*C.
  apply:(le_trans ((hL i).2 (psi (f (set_val x))))).
  exact:(ler_wpM2l (hL i).1 (hBound (f (set_val x)) (hImage (set_val x) (set_valP x)))).
split;first exact:hMeas.
move=>K hK.
have [M [hM hKBound]]:=@finite_scalar_continuous_combination_compact_bound R UT B BN hBN
  d alpha b hBContinuous (fun i=>L i*C) (fun i=>mulr_ge0 (hL i).1 hC) hAlphaBound K hK.
have hFinalBound x:K x->BN (P psi x)<=M.
  move=>hx.
  have hAt:P psi x=\sum_i alpha i x*:b i x:=congr1 (fun g=>g x) hExpansion.
  rewrite hAt;exact:(hKBound x hx).
exact:(@measurable_compact_norm_integral R UT B BN hBN mu hm hr (P psi) K M
  hMeas hK hM hFinalBound).
Qed.
End CurrentBaireFormPullback.
