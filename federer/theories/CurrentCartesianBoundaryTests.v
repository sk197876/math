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
  SmoothCurrentExteriorLeibniz Alternating AlternatingProduct ExteriorHomogeneousProducts
  CurrentTestValueLaws CurrentDegreeTransport CurrentCartesianTestExteriorValues
  CurrentCartesianTestExteriorLeibniz CurrentDegreeTransportComposition
  CurrentDegreeTransportExterior CurrentBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianBoundaryTests.
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

Local Notation CC := (fun r=>@current_space R h2 (m+n) AB hAB r).
Local Notation ec := (fun r=>@current_value R h2 (m+n) AB hAB r).
Local Notation bd := (fun r=>@current_boundary R h2 (m+n) r AB hAB).

(** Source for [current_cartesian_boundary_tests]: evaluation
    of the original current boundary on every separated
    mixed test, supporting all three product boundary
    formulas of Federer 4.1.8, p. 360. *)
Theorem current_cartesian_boundary_tests r (P:CC r.+1) k l
    (e:(k+l)%N=r) (alpha:DA k) (beta:DB l):
  ec r (bd r P) (Tr _ _ e (Pure k l alpha beta))=
    ec r.+1 P (Tr _ _ (eq_trans (addSn k l) (congr1 S e))
      (Pure k.+1 l (dA k alpha) beta))+
    (-1:R)^+k*ec r.+1 P (Tr _ _ (eq_trans (addnS k l) (congr1 S e))
      (Pure k l.+1 alpha (dB l beta))).
Proof.
rewrite (@current_boundary_evaluation R h2 (m+n) r AB hAB P
  (Tr _ _ e (Pure k l alpha beta))).
rewrite (@current_test_degree_transport_exterior R h2 (m+n) AB hAB (k+l) r e
  (Pure k l alpha beta)).
rewrite (@current_cartesian_test_exterior_leibniz R h2 m n A B hA hB k l alpha beta).
rewrite (linD (hom_linear (Tr _ _ (congr1 S e))))
  (linZ (hom_linear (Tr _ _ (congr1 S e)))).
rewrite (linD (hom_linear (ec r.+1 P))) (linZ (hom_linear (ec r.+1 P))).
by rewrite !current_test_degree_transport_composition.
Qed.
End CurrentCartesianBoundaryTests.
