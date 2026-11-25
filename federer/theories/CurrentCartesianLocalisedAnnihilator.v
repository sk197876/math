(** Federer (1969), 4.1.8, p. 360: factor the
    localised pure coordinate tests used by 4.1.3 into
    the original two open-factor tests, in every mixed degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  AlternatingForms AlternatingDual AlternatingProduct ScalarCoefficients ExteriorHomogeneousProducts
  CurrentSpaces CurrentDegreeTransport CurrentCoefficientNorms SmoothFunctionSpaceUP
  SmoothTestSpaces SmoothTestEvaluation SmoothCompactSet CompactSupportFunctionUP
  TestTensorMapUP CutoffCoordinateTest CoordinateTestBlockProduct
  CurrentCartesianDomain CurrentCartesianTestProductSealed CurrentCartesianLocalisedTensor
  CovectorBlockSpan TestTensorAnnihilator TensorFamilyUP ContinuousMultilinearSealed SmoothFunctionDerivativesUP CurrentCoefficientCompleteness
  FiniteCoordinates CurrentSpaces ContinuousRealDual SmoothTestTopology SmoothFunctionTopology
  OpenFamilyTopologyUP NormOpenTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianLocalisedAnnihilator.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Variable A:set X.
Variable B:set Y.
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DA := (fun k=>@current_test_space R h2 m A hA k).
Local Notation DB := (fun k=>@current_test_space R h2 n B hB k).
Local Notation EA := (fun k=>@current_smooth_space R h2 m A hA k).
Local Notation EB := (fun k=>@current_smooth_space R h2 n B hB k).
Local Notation EC := (fun k=>@current_smooth_space R h2 (m+n) AB hAB k).
Local Notation va := (fun k=>@current_smooth_value R h2 m A hA k).
Local Notation vb := (fun k=>@current_smooth_value R h2 n B hB k).
Local Notation vc := (fun k=>@current_smooth_value R h2 (m+n) AB hAB k).
Local Notation ta := (fun k=>@current_test_value R h2 m A hA k).
Local Notation tb := (fun k=>@current_test_value R h2 n B hB k).
Local Notation hEA := (fun k=>@current_smooth_space_laws R h2 m A hA k).
Local Notation hEB := (fun k=>@current_smooth_space_laws R h2 n B hB k).
Local Notation hEC := (fun k=>@current_smooth_space_laws R h2 (m+n) AB hAB k).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).

Variable Line:lmodType R.
Variable lineValue:Line->R^o->R^o.
Hypothesis hLine:is_smooth_function_space (@scalar_absolute_value_norm R)
  (@scalar_absolute_value_norm R) (fun _=>True) lineValue.
Variable d:nat.
Local Notation CF := (A_m Z R^o d).
Local Notation NF := (@current_form_comass R h2 (m+n) d).
Local Notation hNF := (@current_form_comass_real_norm R h2 (m+n) d).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variable Whole:lmodType R.
Variable wholeValue:Whole->Z->CF.
Hypothesis hWhole:is_smooth_function_space hNZ hNF (fun _=>True) wholeValue.
Variables Tensor TensorWithCoefficient:lmodType R.
Variable mu:{dffun forall t:'I_(m+n),smooth_test_space hLine}->Tensor.
Variable nu:Tensor->CF->TensorWithCoefficient.
Variable tensorMap:Hom TensorWithCoefficient (smooth_test_space hWhole).
Hypothesis hTensor:is_test_tensor_map hLine hWhole mu nu tensorMap.
Variables (u:X->R) (v:Y->R).
Hypothesis hu:norm_class_all_orders hNX (@scalar_absolute_value_norm R) (fun _=>True) u.
Hypothesis hv:norm_class_all_orders hNY (@scalar_absolute_value_norm R) (fun _=>True) v.
Variable KA:smooth_compact_set hNX A.
Variable KB:smooth_compact_set hNY B.
Hypothesis hKA:@real_function_support R (real_norm_metric_space hNX) u `<=` smooth_compact_carrier KA.
Hypothesis hKB:@real_function_support R (real_norm_metric_space hNY) v `<=` smooth_compact_carrier KB.
Variable localise:Hom Whole (@current_test_space R h2 (m+n) AB hAB d).
Hypothesis hLocalise:forall f z,AB z->
  @current_test_value R h2 (m+n) AB hAB d (localise f) z=
    (u (p z)*v (q z))*:wholeValue f z.
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Variable DWhole:forall k,Z->Hom Whole
  (@ContinuousMultilinear.space R k Z CF
    (inner_norm (@euclidean_inner_productP R (m+n))) NF hNZ hNF).
Hypothesis hDWhole:@SmoothFunctionDerivativesUP.is_smooth_function_derivatives R Z CF
  (inner_norm (@euclidean_inner_productP R (m+n))) NF hNZ hNF (fun _=>True)
  Whole wholeValue DWhole.
Hypothesis hLocaliseContinuous:open_family_continuous (smooth_function_opens hDWhole)
  (@current_test_opens R h2 (m+n) AB hAB d) localise.
Hypothesis hMu:is_tensor_product_family mu.
Hypothesis hNu:is_tensor_product nu.
(** Source for [current_cartesian_localised_annihilator_zero]:
    a current annihilating every original separated mixed
    test also annihilates every localised full-space test,
    supporting Federer 4.1.8, p. 360. The proof
    uses the earlier full-space 4.1.3 with the actual
    finite covector Banach target, without changing D's topology. *)
Theorem current_cartesian_localised_annihilator_zero
    (C:@current_space R h2 (m+n) AB hAB d):
  (forall k l (e:(k+l)%N=d) (a:DA k) (b:DB l),
    @current_value R h2 (m+n) AB hAB d C
      (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) d e (Pure k l a b))=0)->
  forall phi:smooth_test_space hWhole,
    @current_value R h2 (m+n) AB hAB d C
      (localise (smooth_test_inclusion hWhole phi))=0.
Proof.
move=>hZero.
pose action:=@current_value R h2 (m+n) AB hAB d C.
pose J:=hom_comp action (hom_comp localise (smooth_test_inclusion hWhole)).
have hPure:forall f y,J (tensorMap (nu (mu f) y))=0.
  move=>f y.
  pose coefficient:Hom CF TensorWithCoefficient:=
    @HomMap R CF TensorWithCoefficient (fun y=>nu (mu f) y)
      (introT (asboolP _) ((tensor_bilinear hNu).2 (mu f))).
  pose L:=hom_comp J (hom_comp tensorMap coefficient).
  have hMixed:forall k l (e:(k+l)%N=d) (alpha:A_m X R^o k) (beta:A_m Y R^o l),
      L (form_reindex e (form_wedge h2 (scalar_bilinear R)
        (A_m_dual (hom_as_linear p) alpha) (A_m_dual (hom_as_linear q) beta)))=0.
    move=>k l e alpha beta.
    have[a [b hSeparated]]:=@current_cartesian_localised_tensor_separated R h2 m n A B hA hB
      Line lineValue hLine d Whole wholeValue hWhole Tensor TensorWithCoefficient mu nu tensorMap hTensor
      u v hu hv KA KB hKA hKB localise hLocalise f k l e alpha beta.
    change (action (localise (smooth_test_inclusion hWhole
      (tensorMap (nu (mu f) (form_reindex e (form_wedge h2 (scalar_bilinear R)
        (A_m_dual (hom_as_linear p) alpha) (A_m_dual (hom_as_linear q) beta)))))))=0).
    rewrite hSeparated;exact:(hZero k l e a b).
  exact:(@covector_block_span R h2 Z X Y R^o (hom_as_linear p) (hom_as_linear q)
    (hom_as_linear (@euclidean_first_injection_map R m n))
    (hom_as_linear (@euclidean_last_injection_map R m n))
    (fun z=>esym (@euclidean_block_linear_decomposition R m n z))
    (m+n) (@coordinate_basis R (m+n)) (@coordinate_basisP R (m+n)) d L hMixed y).
have hCurrent:=@continuous_real_dual_member_continuous R
  (@current_test_space R h2 (m+n) AB hAB d)
  (@current_test_opens R h2 (m+n) AB hAB d)
  (smooth_test_final_topology_laws (hEC d)
    (@current_smooth_derivative_laws R h2 (m+n) AB hAB d)).1 C.
have hContinuous:open_family_continuous (smooth_test_opens hWhole hDWhole)
    (norm_open_family (@scalar_absolute_value_norm R)) J.
  exact:(open_family_continuous_compose
    (@smooth_test_inclusion_continuous R Z CF
      (inner_norm (@euclidean_inner_productP R (m+n))) NF hNZ hNF
      (fun _=>True) Whole wholeValue hWhole DWhole hDWhole)
    (open_family_continuous_compose hLocaliseContinuous hCurrent)).
exact:(@test_tensor_annihilator_zero R (m+n) Line lineValue hLine CF NF hNF
  (@current_form_complete R h2 (m+n) d) Whole wholeValue hWhole DWhole hDWhole
  Tensor TensorWithCoefficient mu nu tensorMap J hMu hNu hTensor hContinuous hPure).
Qed.
End CurrentCartesianLocalisedAnnihilator.
