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
  CurrentCartesianDomain CurrentCartesianProjections CurrentCartesianSmoothProductUP CurrentCartesianTestProductSealed SmoothFunctionSpaceLaws CurrentCartesianTestProductInclusion
  CurrentCoefficientNorms CurrentCoefficientCompleteness SmoothFunctionTopology
  SmoothFormPullbackContinuity SmoothBilinearMultiplierUP SmoothBilinearMultiplierSealed
  SmoothBilinearMultiplierContinuity OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianSmoothFactorOperators.
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

Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation NC := (fun k=>@current_form_comass R h2 (m+n) k).
Local Notation hNC := (fun k=>@current_form_comass_real_norm R h2 (m+n) k).
Local Notation FC := (fun k=>@current_form_finite_basis R h2 (m+n) k).
Local Notation DerA := (fun k=>@current_smooth_derivatives R h2 m A hA k).
Local Notation DerB := (fun k=>@current_smooth_derivatives R h2 n B hB k).
Local Notation DerC := (fun k=>@current_smooth_derivatives R h2 (m+n) AB hAB k).
Local Notation hDerA := (fun k=>@current_smooth_derivative_laws R h2 m A hA k).
Local Notation hDerB := (fun k=>@current_smooth_derivative_laws R h2 n B hB k).
Local Notation hDerC := (fun k=>@current_smooth_derivative_laws R h2 (m+n) AB hAB k).

(** Source for [current_cartesian_second_smooth_extension]:
    with the first separated test fixed, the original
    product admits a continuous linear extension on the
    second smooth space, supporting the density arguments
    of Federer 4.1.8, pp. 360–361. The witness
    uses only the public pullback and wedge laws. *)
Theorem current_cartesian_second_smooth_extension k l (alpha:DA k):
  exists P:Hom (EB l) (EC (k+l)),
    open_family_continuous (smooth_function_opens (hDerB l))
      (smooth_function_opens (hDerC (k+l))) P /\
    forall beta:DB l,IC (k+l) (Pure k l alpha beta) = P (IB l beta).
Proof.
pose W:=@smooth_current_form_product R h2 (m+n) k l AB hAB (PA k (IA k alpha)).
pose P:=hom_comp W (PB l).
exists P;split.
- exact:(@open_family_continuous_compose (EB l) (EC l) (EC (k+l))
    (smooth_function_opens (hDerB l)) (smooth_function_opens (hDerC l))
    (smooth_function_opens (hDerC (k+l))) (PB l) W
    (@smooth_form_pullback_continuous R h2 (m+n) n l AB B hAB hB q ImageQ QSmooth (PB l)
      (@SmoothFormPullback.laws R h2 (m+n) n l AB B hAB hB q ImageQ QSmooth))
    (@smooth_current_form_product_continuous R h2 (m+n) k l AB hAB (PA k (IA k alpha)))).
- move=>beta;exact:(@current_cartesian_test_product_inclusion R h2 m n A B hA hB k l alpha beta).
Qed.

(** Source for [current_cartesian_first_smooth_extension]:
    with the second separated test fixed, the original
    product admits a continuous linear extension on the
    first smooth space, supporting the density arguments
    of Federer 4.1.8, pp. 360–361. Reuse the
    original bilinear multiplier with its arguments reversed;
    no new product construction or joint test continuity
    is assumed. *)
Theorem current_cartesian_first_smooth_extension k l (beta:DB l):
  exists P:Hom (EA k) (EC (k+l)),
    open_family_continuous (smooth_function_opens (hDerA k))
      (smooth_function_opens (hDerC (k+l))) P /\
    forall alpha:DA k,IC (k+l) (Pure k l alpha beta) = P (IA k alpha).
Proof.
pose Bflip (b:A_m Z R^o l) (a:A_m Z R^o k):=
  @form_wedge R h2 Z R^o (fun s t:R^o=>s*t) (@scalar_bilinear R) k l a b.
have hFlip:bilinear Bflip.
  have hWedge:=@form_wedge_bilinear R h2 Z R^o (fun s t:R^o=>s*t) (@scalar_bilinear R) k l.
  split;[exact:hWedge.2|exact:hWedge.1].
pose v:=PB l (IB l beta).
pose W:=@SmoothBilinearMultiplier.operator R Z (A_m Z R^o l) (A_m Z R^o k)
  (A_m Z R^o (k+l)) NZ (NC l) (NC k) (NC (k+l)) hNZ (hNC l) (hNC k) (hNC (k+l))
  AB (EC l) (EC k) (EC (k+l)) (vc l) (vc k) (vc (k+l))
  (hEC l) (hEC k) (hEC (k+l)) (FC l) (FC k) Bflip hFlip v.
have hW:=@SmoothBilinearMultiplier.laws R Z (A_m Z R^o l) (A_m Z R^o k)
  (A_m Z R^o (k+l)) NZ (NC l) (NC k) (NC (k+l)) hNZ (hNC l) (hNC k) (hNC (k+l))
  AB (EC l) (EC k) (EC (k+l)) (vc l) (vc k) (vc (k+l))
  (hEC l) (hEC k) (hEC (k+l)) (FC l) (FC k) Bflip hFlip v.
pose P:=hom_comp W (PA k).
exists P;split.
- have hWC:=@smooth_bilinear_multiplier_continuous R Z (A_m Z R^o l) (A_m Z R^o k)
    (A_m Z R^o (k+l)) NZ (NC l) (NC k) (NC (k+l)) hNZ (hNC l) (hNC k) (hNC (k+l))
    AB (EC l) (EC k) (EC (k+l)) (vc l) (vc k) (vc (k+l))
    (hEC l) (hEC k) (hEC (k+l)) (FC l) (FC k) Bflip hFlip v
    hAB (DerC k) (DerC (k+l)) (hDerC k) (hDerC (k+l)) W hW.
  exact:(@open_family_continuous_compose (EA k) (EC k) (EC (k+l))
    (smooth_function_opens (hDerA k)) (smooth_function_opens (hDerC k))
    (smooth_function_opens (hDerC (k+l))) (PA k) W
    (@smooth_form_pullback_continuous R h2 (m+n) m k AB A hAB hA p ImageP PSmooth (PA k)
      (@SmoothFormPullback.laws R h2 (m+n) m k AB A hAB hA p ImageP PSmooth)) hWC).
- move=>alpha.
  rewrite (@current_cartesian_test_product_inclusion R h2 m n A B hA hB k l alpha beta).
  apply:(smooth_function_extensional (hEC (k+l)))=>z hz.
  have hProduct:=@smooth_current_form_product_values R h2 (m+n) k l AB hAB
    (PA k (IA k alpha)) v z hz.
  exact:(eq_trans hProduct (esym (hW (PA k (IA k alpha)) z hz))).
Qed.
End CurrentCartesianSmoothFactorOperators.
