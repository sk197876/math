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
  CurrentCartesianDomain CurrentCartesianTestProductSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianLocalisedTensor.
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
(** Source for [current_cartesian_localised_tensor_separated]:
    a coordinate pure test with a separated mixed covector
    coefficient localises to an actual separated test on
    the original factors, supporting Federer 4.1.8, p. 360,
    by 4.1.3, p. 348. All equal total-degree
    casts and both zero coordinate blocks are retained. *)
Theorem current_cartesian_localised_tensor_separated
    (f:{dffun forall t:'I_(m+n),smooth_test_space hLine}) k l (e:(k+l)%N=d)
    (alpha:A_m X R^o k) (beta:A_m Y R^o l):
  exists a:DA k,exists b:DB l,
    localise (smooth_test_inclusion hWhole
      (tensorMap (nu (mu f) (form_reindex e
        (form_wedge h2 (scalar_bilinear R) (A_m_dual (hom_as_linear p) alpha)
          (A_m_dual (hom_as_linear q) beta))))))=
    @current_test_degree_transport R h2 (m+n) AB hAB (k+l) d e (Pure k l a b).
Proof.
have[a ha]:=@cutoff_coordinate_test_exists R m Line lineValue hLine (A_m X R^o k)
  (@current_form_comass R h2 m k) (@current_form_comass_real_norm R h2 m k)
  A hA (EA k) (va k) (hEA k) u hu KA hKA (fun t=>f (lshift n t)) alpha.
have[b hb]:=@cutoff_coordinate_test_exists R n Line lineValue hLine (A_m Y R^o l)
  (@current_form_comass R h2 n l) (@current_form_comass_real_norm R h2 n l)
  B hB (EB l) (vb l) (hEB l) v hv KB hKB (fun t=>f (rshift m t)) beta.
exists a,b;apply:(smooth_test_values_extensional (hEC d))=>z hz.
change (@current_test_value R h2 (m+n) AB hAB d
  (localise (smooth_test_inclusion hWhole
    (tensorMap (nu (mu f) (form_reindex e (form_wedge h2 (scalar_bilinear R)
      (A_m_dual (hom_as_linear p) alpha) (A_m_dual (hom_as_linear q) beta))))))) z=
  @current_test_value R h2 (m+n) AB hAB d
    (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) d e (Pure k l a b)) z).
have hAValue:=@ha (p z) hz.1.
change (ta k a (p z)=(u (p z)*(\prod_t smooth_test_value hLine (f (lshift n t)) (p z t)))*:alpha) in hAValue.
have hBValue:=@hb (q z) hz.2.
change (tb l b (q z)=(v (q z)*(\prod_t smooth_test_value hLine (f (rshift m t)) (q z t)))*:beta) in hBValue.
rewrite (@hLocalise _ z hz) current_test_degree_transport_values
  ((@CartesianTestProduct.laws R h2 m n A B hA hB k l).2 a b z hz) hAValue hBValue.
have hPoint:=@hTensor f (form_reindex e (form_wedge h2 (scalar_bilinear R)
  (A_m_dual (hom_as_linear p) alpha) (A_m_dual (hom_as_linear q) beta))) z.
change (wholeValue (smooth_test_inclusion hWhole
  (tensorMap (nu (mu f) (form_reindex e (form_wedge h2 (scalar_bilinear R)
    (A_m_dual (hom_as_linear p) alpha) (A_m_dual (hom_as_linear q) beta)))))) z=
  (\prod_t smooth_test_value hLine (f t) (z t))*:
    form_reindex e (form_wedge h2 (scalar_bilinear R)
      (A_m_dual (hom_as_linear p) alpha) (A_m_dual (hom_as_linear q) beta))) in hPoint.
rewrite hPoint.
pose sa:=u (p z)*(\prod_t smooth_test_value hLine (f (lshift n t)) (p z t)).
pose sb:=v (q z)*(\prod_t smooth_test_value hLine (f (rshift m t)) (q z t)).
have hPullA:=linZ (@A_m_dual_linear R Z X R^o (hom_as_linear p) k) sa alpha.
have hPullB:=linZ (@A_m_dual_linear R Z Y R^o (hom_as_linear q) l) sb beta.
rewrite hPullA hPullB
  (bilZl (@form_wedge_bilinear R h2 Z R^o (fun x y:R^o=>x*y) (scalar_bilinear R) k l))
  (bilZr (@form_wedge_bilinear R h2 Z R^o (fun x y:R^o=>x*y) (scalar_bilinear R) k l)).
pose w:=form_wedge h2 (scalar_bilinear R) (A_m_dual (hom_as_linear p) alpha)
  (A_m_dual (hom_as_linear q) beta).
rewrite (linZ (@form_reindex_linear R Z R^o (k+l) d e) sa (sb*:w))
  (linZ (@form_reindex_linear R Z R^o (k+l) d e) sb w) !scalerA.
congr (_ *: _).
have hBlocks:=@coordinate_test_block_product R m n Line lineValue hLine f (p z) (q z).
have hJoin:@euclidean_block_join R m n (p z,q z)=z.
  exact:(@euclidean_block_splitK R m n z).
rewrite hJoin in hBlocks.
by rewrite hBlocks /sa /sb mulrACA.
Qed.
End CurrentCartesianLocalisedTensor.
