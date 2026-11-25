(** Federer (1969), 4.1.8, p. 360: identify the original
    separated test with the wedge of the two actual smooth
    pullbacks. This consequence of the independent point laws
    supports the printed boundary product rule. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear BilinearPrecompose RealNormUP
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  AlternatingForms AlternatingDual AlternatingProduct ScalarCoefficients
  CurrentSpaces SmoothTestSpaces SmoothTestEvaluation SmoothFormPullbackUP
  SmoothFormPullbackSealed SmoothCurrentFormProduct SmoothCurrentFormProductBilinear
  CurrentCartesianDomain CurrentCartesianProjections CurrentCartesianSmoothProductUP CurrentCartesianTestProductSealed SmoothFunctionSpaceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianTestProductInclusion.
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

(** Source for [current_cartesian_test_product_inclusion]:
    p#alpha wedge q#beta is the actual separated compact
    test in Federer 4.1.8, p. 360, with precisely the
    original smooth pullbacks and exterior product. *)
Theorem current_cartesian_test_product_inclusion k l (alpha:DA k) (beta:DB l):
  IC (k+l) (Pure k l alpha beta)=
    @smooth_current_form_product R h2 (m+n) k l AB hAB
      (PA k (IA k alpha)) (PB l (IB l beta)).
Proof.
apply:(smooth_function_extensional (hEC (k+l)))=>z hz.
change (tc (k+l) (Pure k l alpha beta) z=
  vc (k+l) (@smooth_current_form_product R h2 (m+n) k l AB hAB
    (PA k (IA k alpha)) (PB l (IB l beta))) z).
have hValue:=((@CartesianTestProduct.laws R h2 m n A B hA hB k l).2 alpha beta z hz).
have hProduct:=@smooth_current_form_product_values R h2 (m+n) k l AB hAB
  (PA k (IA k alpha)) (PB l (IB l beta)) z hz.
have hP:=@smooth_form_pullback_values R (m+n) m k AB A
  (EA k) (EC k) (va k) (vc k) p (PA k)
  (@SmoothFormPullback.laws R h2 (m+n) m k AB A hAB hA p ImageP PSmooth)
  (IA k alpha) z p hz
  (@current_cartesian_first_projection_differential R m n A B hA hB z hz).
have hQ:=@smooth_form_pullback_values R (m+n) n l AB B
  (EB l) (EC l) (vb l) (vc l) q (PB l)
  (@SmoothFormPullback.laws R h2 (m+n) n l AB B hAB hB q ImageQ QSmooth)
  (IB l beta) z q hz
  (@current_cartesian_last_projection_differential R m n A B hA hB z hz).
exact:(eq_trans hValue (esym (eq_trans hProduct
  (congr2 (@form_wedge R h2 Z R^o (fun a b:R^o=>a*b) (@scalar_bilinear R) k l) hP hQ)))).
Qed.
End CurrentCartesianTestProductInclusion.
