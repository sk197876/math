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
  SmoothBilinearMultiplierContinuity OpenFamilyTopologyUP
  CurrentCartesianSmoothFactorOperators SmoothTestOperatorBetweenDomains CurrentCartesianTestProductSupport
  CurrentSupportGeometry SmoothCompactSet SmoothFunctionSupport SmoothTestTopology
  LinearSubspaceRepresentationUP SmoothTestSubspaces CurrentCartesianCompact CurrentCartesianCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianTestFactorContinuity.
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

Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NA := (fun k=>@current_form_comass R h2 m k).
Local Notation NB := (fun k=>@current_form_comass R h2 n k).
Local Notation hNA := (fun k=>@current_form_comass_real_norm R h2 m k).
Local Notation hNB := (fun k=>@current_form_comass_real_norm R h2 n k).
Local Open Scope classical_set_scope.

(** Source for [current_cartesian_test_product_first_continuous]:
    with its second factor fixed, the original separated
    test map is continuous for the literal final topologies,
    supporting the density arguments of Federer 4.1.8,
    pp. 360–361. Product compact supports and the
    existing smooth pullback continuity supply the proof. *)
Theorem current_cartesian_test_product_first_continuous k l (beta:DB l):
  open_family_continuous (@current_test_opens R h2 m A hA k)
    (@current_test_opens R h2 (m+n) AB hAB (k+l))
    (fun alpha:DA k=>Pure k l alpha beta).
Proof.
have[P [hPC hInc]]:=@current_cartesian_first_smooth_extension R h2 m n A B hA hB k l beta.
have hLinear:linear (fun alpha:DA k=>Pure k l alpha beta):=
  ((@CartesianTestProduct.laws R h2 m n A B hA hB k l).1).1 beta.
pose L:=@HomMap R (DA k) (@current_test_space R h2 (m+n) AB hAB (k+l))
  (fun alpha=>Pure k l alpha beta) (introT (asboolP _) hLinear).
change (open_family_continuous (@current_test_opens R h2 m A hA k)
  (@current_test_opens R h2 (m+n) AB hAB (k+l)) L).
apply:(@smooth_test_operator_between_domains_continuous R X Z (A_m X R^o k) (A_m Z R^o (k+l))
  NX NZ (NA k) (NC (k+l)) hNX hNZ (hNA k) (hNC (k+l)) A AB
  (EA k) (EC (k+l)) (va k) (vc (k+l)) (hEA k) (hEC (k+l))
  (DerA k) (DerC (k+l)) (hDerA k) (hDerC (k+l)) L P hInc hPC).
move=>K.
have[KB hKB]:=smooth_test_support_bound (hEB l) beta.
have[KC hKC]:=@current_cartesian_compact_rectangle R m n A B K KB.
exists KC;move=>f.
change (@current_test_support R h2 (m+n) (k+l) AB hAB
  (Pure k l (smooth_test_step (hEA k) K f) beta) `<=` smooth_compact_carrier KC).
have hSource:@current_test_support R h2 m k A hA (smooth_test_step (hEA k) K f) `<=`
    smooth_compact_carrier K.
  change (@smooth_function_support R X (A_m X R^o k) NX hNX A (EA k) (va k)
    (IA k (smooth_test_step (hEA k) K f)) `<=` smooth_compact_carrier K).
  rewrite smooth_test_step_evaluation.
  exact:(subspace_representation_member (smooth_fixed_test_space_laws (hEA k) K) f).
move=>z hz;rewrite hKC.
have hProduct:=@current_cartesian_test_product_support R h2 m n A B hA hB k l
  (smooth_test_step (hEA k) K f) beta z hz.
split;[exact:(hSource (p z) hProduct.1)|exact:(hKB (q z) hProduct.2)].
Qed.

(** Source for [current_cartesian_test_product_second_continuous]:
    with its first factor fixed, the original separated
    test map is continuous for the literal final topologies,
    supporting Federer 4.1.8, pp. 360–361. The
    argument uses common product support on each original
    compact step; it asserts no joint vector continuity. *)
Theorem current_cartesian_test_product_second_continuous k l (alpha:DA k):
  open_family_continuous (@current_test_opens R h2 n B hB l)
    (@current_test_opens R h2 (m+n) AB hAB (k+l))
    (fun beta:DB l=>Pure k l alpha beta).
Proof.
have[P [hPC hInc]]:=@current_cartesian_second_smooth_extension R h2 m n A B hA hB k l alpha.
have hLinear:linear (fun beta:DB l=>Pure k l alpha beta):=
  ((@CartesianTestProduct.laws R h2 m n A B hA hB k l).1).2 alpha.
pose L:=@HomMap R (DB l) (@current_test_space R h2 (m+n) AB hAB (k+l))
  (fun beta=>Pure k l alpha beta) (introT (asboolP _) hLinear).
change (open_family_continuous (@current_test_opens R h2 n B hB l)
  (@current_test_opens R h2 (m+n) AB hAB (k+l)) L).
apply:(@smooth_test_operator_between_domains_continuous R Y Z (A_m Y R^o l) (A_m Z R^o (k+l))
  NY NZ (NB l) (NC (k+l)) hNY hNZ (hNB l) (hNC (k+l)) B AB
  (EB l) (EC (k+l)) (vb l) (vc (k+l)) (hEB l) (hEC (k+l))
  (DerB l) (DerC (k+l)) (hDerB l) (hDerC (k+l)) L P hInc hPC).
move=>K.
have[KA hKA]:=smooth_test_support_bound (hEA k) alpha.
have[KC hKC]:=@current_cartesian_compact_rectangle R m n A B KA K.
exists KC;move=>f.
change (@current_test_support R h2 (m+n) (k+l) AB hAB
  (Pure k l alpha (smooth_test_step (hEB l) K f)) `<=` smooth_compact_carrier KC).
have hSource:@current_test_support R h2 n l B hB (smooth_test_step (hEB l) K f) `<=`
    smooth_compact_carrier K.
  change (@smooth_function_support R Y (A_m Y R^o l) NY hNY B (EB l) (vb l)
    (IB l (smooth_test_step (hEB l) K f)) `<=` smooth_compact_carrier K).
  rewrite smooth_test_step_evaluation.
  exact:(subspace_representation_member (smooth_fixed_test_space_laws (hEB l) K) f).
move=>z hz;rewrite hKC.
have hProduct:=@current_cartesian_test_product_support R h2 m n A B hA hB k l
  alpha (smooth_test_step (hEB l) K f) z hz.
split;[exact:(hKA (p z) hProduct.1)|exact:(hSource (q z) hProduct.2)].
Qed.
End CurrentCartesianTestFactorContinuity.
