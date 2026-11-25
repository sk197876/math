(** Federer (1969), 4.1.8, p. 361: the original
    Cartesian interchange pulls a separated compact test
    back to its reversed product with the exact graded
    sign. This proves equality in the actual smooth
    space and retains every equal total degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap EuclideanCartesianSwapLinear
  AlternatingForms AlternatingDual AlternatingProduct ScalarCoefficients ExteriorHomogeneousProducts
  CurrentSpaces SmoothFunctionSpaceLaws SmoothTestSpaces SmoothTestEvaluation
  CurrentTestValueLaws CurrentDegreeTransport SmoothFormPullbackUP SmoothFormPullbackSealed
  CurrentCartesianDomain CurrentCartesianSwapDomain CurrentCartesianTestProductSealed
  CovectorCartesianSwap FormReindexPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianSwapPurePullback.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation BA := (@euclidean_cartesian_set R n m B A).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation hBA := (@current_cartesian_domain_open R n m B A hB hA).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Local Notation swap := (@euclidean_cartesian_swap_map R m n).
Local Notation Image := (fun z hz=>@current_cartesian_swap_image R m n A B z hz).
Local Notation hSmooth := (@euclidean_cartesian_swap_smooth R m n AB hAB).
Local Notation EA := (fun k=>@current_smooth_space R h2 (m+n) AB hAB k).
Local Notation EB := (fun k=>@current_smooth_space R h2 (n+m) BA hBA k).
Local Notation va := (fun k=>@current_smooth_value R h2 (m+n) AB hAB k).
Local Notation vb := (fun k=>@current_smooth_value R h2 (n+m) BA hBA k).
Local Notation hEA := (fun k=>@current_smooth_space_laws R h2 (m+n) AB hAB k).
Local Notation hEB := (fun k=>@current_smooth_space_laws R h2 (n+m) BA hBA k).
Local Notation IA := (fun k=>smooth_test_inclusion (hEA k)).
Local Notation IB := (fun k=>smooth_test_inclusion (hEB k)).
Local Notation PureA := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation PureB := (fun k l=>@CartesianTestProduct.value R h2 n m B A hB hA k l).
Local Notation TrA := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (m+n) AB hAB a b e).
Local Notation TrB := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (n+m) BA hBA a b e).
Local Notation pull := (fun d=>@SmoothFormPullback.operator R h2 (m+n) (n+m) d
  AB BA hAB hBA swap Image hSmooth).

(** Source for [current_cartesian_swap_pure_pullback]: the
    exact pulled-back separated test for w, with sign
    (-1)^(kl), supporting the signed current interchange
    of Federer 4.1.8, p. 361. Both sides
    are actual smooth representatives of compact tests. *)
Theorem current_cartesian_swap_pure_pullback d k l (e:(k+l)%N=d)
    (alpha:@current_test_space R h2 n B hB k)
    (beta:@current_test_space R h2 m A hA l):
  pull d (IB d (TrB _ _ e (PureB k l alpha beta)))=
    IA d ((-1:R)^+(k * l)*:TrA _ _ (eq_trans (addnC l k) e) (PureA l k beta alpha)).
Proof.
apply:(smooth_function_extensional (hEA d))=>z hz.
have hTargetPure:=(@CartesianTestProduct.laws R h2 n m B A hB hA k l).2
  alpha beta (swap z) (@current_cartesian_swap_image R m n A B z hz).
cbn beta in hTargetPure.
rewrite euclidean_cartesian_swap_first euclidean_cartesian_swap_last in hTargetPure.
have hTargetTr:=@current_test_degree_transport_values R h2 (n+m) BA hBA (k+l) d e
  (PureB k l alpha beta) (swap z).
rewrite hTargetPure in hTargetTr.
have hPull:=@smooth_form_pullback_values R (m+n) (n+m) d AB BA
  (EB d) (EA d) (vb d) (va d) swap (pull d)
  (@SmoothFormPullback.laws R h2 (m+n) (n+m) d AB BA hAB hBA swap Image hSmooth)
  (IB d (TrB _ _ e (PureB k l alpha beta))) z swap hz
  (@euclidean_cartesian_swap_differential R m n AB hAB z hz).
have hLeft:=eq_trans hPull (congr1 (fun a:A_m (R_n R (n+m)) R^o d=>A_m_dual (hom_as_linear swap) a) hTargetTr).
have hSourcePure:=(@CartesianTestProduct.laws R h2 m n A B hA hB l k).2 beta alpha z hz.
have hSourceTr:=@current_test_degree_transport_values R h2 (m+n) AB hAB (l+k) d
  (eq_trans (addnC l k) e) (PureA l k beta alpha) z.
rewrite hSourcePure in hSourceTr.
have hScaling:
    va d (IA d ((-1:R)^+(k * l)*:TrA _ _ (eq_trans (addnC l k) e) (PureA l k beta alpha))) z=
    (-1:R)^+(k * l)*:@current_test_value R h2 (m+n) AB hAB d
      (TrA _ _ (eq_trans (addnC l k) e) (PureA l k beta alpha)) z.
  change (smooth_test_values_hom (hEA d)
    ((-1:R)^+(k * l)*:TrA _ _ (eq_trans (addnC l k) e) (PureA l k beta alpha)) z=
    (-1:R)^+(k * l)*:smooth_test_values_hom (hEA d)
      (TrA _ _ (eq_trans (addnC l k) e) (PureA l k beta alpha)) z).
  by rewrite linearZ.
have hRight:=eq_trans hScaling (congr1 (fun v=>(-1:R)^+(k * l)*:v) hSourceTr).
rewrite original_linear_pullback_reindex covector_cartesian_swap_product
  (linZ (@form_reindex_linear R (R_n R (m+n)) R^o (k+l) d e)) in hLeft.
cbn beta in hLeft, hRight.
rewrite form_reindex_composition in hLeft.
exact:(eq_trans hLeft (esym hRight)).
Qed.
End CurrentCartesianSwapPurePullback.
