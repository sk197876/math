(** Federer (1969), 4.1.8, p. 360: exterior differentiation
    of the original separated tests. Reuse the graded product
    rule and pullback commutation already proved in 4.1.7,
    pp. 356, 359, with the actual original test derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear BilinearPrecompose RealNormUP
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  AlternatingForms AlternatingDual AlternatingProduct ScalarCoefficients
  CurrentSpaces SmoothTestSpaces SmoothTestEvaluation SmoothFormPullbackUP
  SmoothFormPullbackSealed SmoothCurrentFormProduct SmoothCurrentFormProductBilinear
  CurrentCartesianDomain CurrentCartesianProjections CurrentCartesianSmoothProductUP CurrentCartesianTestProductSealed SmoothFunctionSpaceLaws CurrentCartesianTestProductInclusion
  CurrentTestExteriorDerivative SmoothCurrentExteriorDerivative SmoothFormPullbackDifferential
  SmoothCurrentExteriorLeibniz Alternating AlternatingProduct ExteriorHomogeneousProducts ComassWedgeSymmetry
  CurrentTestValueLaws CurrentDegreeTransport CurrentCartesianTestExteriorValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianTestExteriorLeibniz.
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
Local Notation tc := (fun k=>@current_test_value R h2 (m+n) AB hAB k).
Local Notation vc := (fun k=>@current_smooth_value R h2 (m+n) AB hAB k).
Local Notation ta := (fun k=>@current_test_value R h2 m A hA k).
Local Notation tb := (fun k=>@current_test_value R h2 n B hB k).
Local Notation hEA := (fun k=>@current_smooth_space_laws R h2 m A hA k).
Local Notation hEB := (fun k=>@current_smooth_space_laws R h2 n B hB k).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).

Local Notation hEC := (fun k=>@current_smooth_space_laws R h2 (m+n) AB hAB k).
Local Notation IA := (fun k=>smooth_test_inclusion (hEA k)).
Local Notation IB := (fun k=>smooth_test_inclusion (hEB k)).
Local Notation IC := (fun k=>smooth_test_inclusion (hEC k)).
Local Notation ImageP := (fun z (hz:AB z)=>hz.1).
Local Notation ImageQ := (fun z (hz:AB z)=>hz.2).
Local Notation PSmooth := (@current_cartesian_first_projection_smooth R m n A B hA hB).
Local Notation QSmooth := (@current_cartesian_last_projection_smooth R m n A B hA hB).
Local Notation PA := (fun k=>@SmoothFormPullback.operator R h2 (m+n) m k AB A hAB hA p ImageP PSmooth).
Local Notation PB := (fun k=>@SmoothFormPullback.operator R h2 (m+n) n k AB B hAB hB q ImageQ QSmooth).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).

Local Notation dA := (fun k=>@current_test_exterior_derivative R h2 m k A hA).
Local Notation dB := (fun k=>@current_test_exterior_derivative R h2 n k B hB).
Local Notation dC := (fun k=>@current_test_exterior_derivative R h2 (m+n) k AB hAB).
Local Notation sdA := (fun k=>@smooth_current_exterior_derivative R h2 m k A hA).
Local Notation sdB := (fun k=>@smooth_current_exterior_derivative R h2 n k B hB).
Local Notation sdC := (fun k=>@smooth_current_exterior_derivative R h2 (m+n) k AB hAB).
Local Notation aw := (alternating_wedge h2 (@scalar_bilinear R)).

Local Notation Tr := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (m+n) AB hAB a b e).

(** Source for [current_cartesian_test_exterior_leibniz]:
    the original graded exterior derivative of separated
    tests as an equality in the actual compact test
    space, supporting the three boundary formulas in
    Federer 4.1.8, p. 360. *)
Theorem current_cartesian_test_exterior_leibniz k l (alpha:DA k) (beta:DB l):
  dC (k+l) (Pure k l alpha beta)=
    Tr _ _ (addSn k l) (Pure k.+1 l (dA k alpha) beta)+
    (-1:R)^+k*:Tr _ _ (addnS k l) (Pure k l.+1 alpha (dB l beta)).
Proof.
apply:(smooth_test_values_extensional (hEC (k+l).+1))=>z hz.
change (tc (k+l).+1 (dC (k+l) (Pure k l alpha beta)) z=
  smooth_test_values_hom (hEC (k+l).+1)
    (Tr _ _ (addSn k l) (Pure k.+1 l (dA k alpha) beta)+
      (-1:R)^+k*:Tr _ _ (addnS k l) (Pure k l.+1 alpha (dB l beta))) z).
rewrite linearD linearZ.
change (tc (k+l).+1 (dC (k+l) (Pure k l alpha beta)) z=
  tc (k+l).+1 (Tr _ _ (addSn k l) (Pure k.+1 l (dA k alpha) beta)) z+
    (-1:R)^+k*:tc (k+l).+1 (Tr _ _ (addnS k l) (Pure k l.+1 alpha (dB l beta))) z).
cbn beta.
rewrite (@current_test_degree_transport_values R h2 (m+n) AB hAB _ _ (addSn k l)
  (Pure k.+1 l (dA k alpha) beta) z)
  (@current_test_degree_transport_values R h2 (m+n) AB hAB _ _ (addnS k l)
  (Pure k l.+1 alpha (dB l beta)) z).
apply:(can_inj (@form_includeK R Z R^o (k+l).+1)).
rewrite linearD linearZ.
change (form_include (tc (k+l).+1 (dC (k+l) (Pure k l alpha beta)) z)=
  form_include (form_reindex (addSn k l)
    (tc (k.+1+l) (Pure k.+1 l (dA k alpha) beta) z))+
  (-1:R)^+k*:form_include (form_reindex (addnS k l)
    (tc (k+l.+1) (Pure k l.+1 alpha (dB l beta)) z))).
rewrite !form_reindex_include.
cbn beta.
rewrite (@current_cartesian_test_exterior_values R h2 m n A B hA hB k l alpha beta z hz).
rewrite ((@CartesianTestProduct.laws R h2 m n A B hA hB k.+1 l).2 (dA k alpha) beta z hz)
  ((@CartesianTestProduct.laws R h2 m n A B hA hB k l.+1).2 alpha (dB l beta) z hz).
by rewrite !form_wedge_include.
Qed.
End CurrentCartesianTestExteriorLeibniz.
