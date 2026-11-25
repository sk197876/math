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
  SmoothCurrentExteriorLeibniz Alternating AlternatingProduct ExteriorHomogeneousProducts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianTestExteriorValues.
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

(** Source for [current_cartesian_test_exterior_values]: the
    exterior derivative of p#alpha wedge q#beta is
    p#d alpha wedge q#beta plus (-1)^k p#alpha
    wedge q#d beta, supporting all three boundary
    formulas of Federer 4.1.8, p. 360. *)
Theorem current_cartesian_test_exterior_values k l (alpha:DA k) (beta:DB l) z:
  AB z->
  form_include (tc (k+l).+1 (dC (k+l) (Pure k l alpha beta)) z)=
    aw (form_include (A_m_dual (hom_as_linear p) (ta k.+1 (dA k alpha) (p z))))
      (form_include (A_m_dual (hom_as_linear q) (tb l beta (q z))))+
    (-1:R)^+k*:aw (form_include (A_m_dual (hom_as_linear p) (ta k alpha (p z))))
      (form_include (A_m_dual (hom_as_linear q) (tb l.+1 (dB l beta) (q z)))).
Proof.
move=>hz.
have hDP:sdC k (PA k (IA k alpha))=PA k.+1 (IA k.+1 (dA k alpha)).
  rewrite (@smooth_form_pullback_exterior_commutes R h2 (m+n) m k AB A hAB hA
    p ImageP PSmooth (IA k alpha)).
  by rewrite (@current_test_exterior_derivative_inclusion R h2 m k A hA alpha).
have hDQ:sdC l (PB l (IB l beta))=PB l.+1 (IB l.+1 (dB l beta)).
  rewrite (@smooth_form_pullback_exterior_commutes R h2 (m+n) n l AB B hAB hB
    q ImageQ QSmooth (IB l beta)).
  by rewrite (@current_test_exterior_derivative_inclusion R h2 n l B hB beta).
have hLeft:tc (k+l).+1 (dC (k+l) (Pure k l alpha beta)) z=
    vc (k+l).+1 (sdC (k+l) (@smooth_current_form_product R h2 (m+n) k l AB hAB
      (PA k (IA k alpha)) (PB l (IB l beta)))) z.
  change (vc (k+l).+1 (IC (k+l).+1 (dC (k+l) (Pure k l alpha beta))) z=
    vc (k+l).+1 (sdC (k+l) (@smooth_current_form_product R h2 (m+n) k l AB hAB
      (PA k (IA k alpha)) (PB l (IB l beta)))) z).
  by rewrite (@current_test_exterior_derivative_inclusion R h2 (m+n) (k+l) AB hAB
    (Pure k l alpha beta))
    (@current_cartesian_test_product_inclusion R h2 m n A B hA hB k l alpha beta).
rewrite hLeft.
have hLeibniz:=@smooth_current_exterior_leibniz_values R h2 (m+n) k l AB hAB
  (PA k (IA k alpha)) (PB l (IB l beta)) z hz.
rewrite hDP hDQ in hLeibniz.
have hP t (a:DA t):vc t (PA t (IA t a)) z=
    A_m_dual (hom_as_linear p) (ta t a (p z)).
  exact:(@smooth_form_pullback_values R (m+n) m t AB A
    (EA t) (EC t) (va t) (vc t) p (PA t)
    (@SmoothFormPullback.laws R h2 (m+n) m t AB A hAB hA p ImageP PSmooth)
    (IA t a) z p hz
    (@current_cartesian_first_projection_differential R m n A B hA hB z hz)).
have hQ t (b:DB t):vc t (PB t (IB t b)) z=
    A_m_dual (hom_as_linear q) (tb t b (q z)).
  exact:(@smooth_form_pullback_values R (m+n) n t AB B
    (EB t) (EC t) (vb t) (vc t) q (PB t)
    (@SmoothFormPullback.laws R h2 (m+n) n t AB B hAB hB q ImageQ QSmooth)
    (IB t b) z q hz
    (@current_cartesian_last_projection_differential R m n A B hA hB z hz)).
by rewrite !hP !hQ in hLeibniz.
Qed.
End CurrentCartesianTestExteriorValues.
