(** Federer (1969), 4.1.7, p. 359:
    the original Baire form and target
    test product is measurable after composition
    with the actual smooth source map.
    This uses 2.2.15, p. 70,
    and 2.3.2, pp. 73–74, before
    changing the source measure. It makes
    no inference from weighted null sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ScalarCoefficients TensorUP RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingProduct
  CurrentDomain CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentProperSupportDomain
  CurrentFormWedgeBound MeasurableBoundedBilinearProduct SmoothFunctionSpaceUP SmoothTestEvaluation
  DistributionSubspaceTestValues CompactContinuousVectorFields BaireFunctions BaireBorel BorelFunctionBasic
  PartialFunctionBasic MeasureUP RadonMeasureUP MeasurableFunctionUP MeasurableIdentityCriterion MeasurableTotalBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentBaireTestSourceMeasurable.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n k p:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:set X) (V:set Y).
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Local Notation UT := (current_domain R v U).
Local Notation VT := (current_domain R n V).
Local Notation A := (fun d=>A_m Y R^o d).
Local Notation AN := (fun d=>@current_form_comass R h2 n d).
Local Notation hAN := (fun d=>@current_form_comass_real_norm R h2 n d).
Local Notation DT := (@current_test_space R h2 n V hV p).
Local Notation hE := (@current_smooth_space_laws R h2 n V hV p).
Local Notation ev := (@current_test_value R h2 n V hV p).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation fU := (@current_map_on_domain R v n U V f hImage).

(** Source for [current_baire_test_source_measurable]:
    the actual composed psi wedge phi
    is measurable for the original source
    Radon measure, supporting Federer 4.1.7,
    p. 359. No global bound on
    the derivative, finite source mass or
    pullback of completed null sets is required. *)
Theorem current_baire_test_source_measurable
    (mu:set UT->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (psi:Y->A k):
  @is_baire_function R VT (real_norm_metric_space (hAN k))
    (fun y:VT=>(psi (set_val y):real_norm_metric_space (hAN k)))->
  forall phi:DT,is_measure_measurable_function mu (partial_function_total
    (fun x:UT=>(form_wedge h2 (scalar_bilinear R)
      (psi (f (set_val x))) (ev phi (f (set_val x))):real_norm_metric_space (hAN (k+p))))).
Proof.
move=>hPsi phi.
have hF:=@current_map_on_domain_continuous R v n U V f hImage
  (norm_class_continuous (hf 0%N)).
have hIdentity:=(@measurable_identity_iff_open_sets R UT mu hm).2 (radon_open_measurable hr).
have hBorel:=borel_function_composition (continuous_borel_function hF) (baire_function_borel hPsi).
have hPsiMeas:=@measurable_total_borel_postcomposition R UT UT (real_norm_metric_space (hAN k))
  mu hm id (fun x=>psi (f (set_val x))) hIdentity hBorel.
have hPhi:=@smooth_test_original_continuous_field R Y (A p) NY (AN p) hNY (hAN p) V
  (@current_smooth_space R h2 n V hV p) (@current_smooth_value R h2 n V hV p) hE phi.
have hTestContinuous:continuous
    (fun x:UT=>(ev phi (f (set_val x)):real_norm_metric_space (hAN p))).
  move=>x;exact:(continuous_comp (hF x) (hPhi.1 (fU x))).
have hTestMeas:=@measurable_total_borel_postcomposition R UT UT (real_norm_metric_space (hAN p))
  mu hm id (fun x=>ev phi (f (set_val x))) hIdentity (continuous_borel_function hTestContinuous).
exact:(@measurable_bounded_bilinear_product R UT (A k) (A p) (A (k+p))
  (AN k) (AN p) (AN (k+p)) (hAN k) (hAN p) (hAN (k+p)) mu hm
  (@form_wedge R h2 Y R^o (fun a b=>a*b) (scalar_bilinear R) k p)
  (@current_form_wedge_bounded R h2 n k p)
  (fun x=>psi (f (set_val x))) (fun x=>ev phi (f (set_val x)))
  (@current_form_separable R h2 n k) (@current_form_separable R h2 n p) hPsiMeas hTestMeas).
Qed.
End CurrentBaireTestSourceMeasurable.
