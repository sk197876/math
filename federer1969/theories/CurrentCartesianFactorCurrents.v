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
  LinearSubspaceRepresentationUP SmoothTestSubspaces CurrentCartesianCompact CurrentCartesianCutoff CurrentCartesianTestFactorContinuity ContinuousRealDual NormOpenTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianFactorCurrents.
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

Local Notation CA := (fun k=>@current_space R h2 m A hA k).
Local Notation CB := (fun k=>@current_space R h2 n B hB k).
Local Notation CC := (fun k=>@current_space R h2 (m+n) AB hAB k).

(** Source for [current_cartesian_second_factor_current_exists]:
    fixing the first separated test in an arbitrary
    product-domain current gives a genuine current in
    the second factor, supporting the density argument
    for Federer 4.1.8, p. 361. Existence uses
    the proved fixed-factor final-topology continuity. *)
Theorem current_cartesian_second_factor_current_exists k l (C:CC (k+l)) (alpha:DA k):
  exists T:CB l,forall beta:DB l,
    @current_value R h2 n B hB l T beta=
    @current_value R h2 (m+n) AB hAB (k+l) C (Pure k l alpha beta).
Proof.
have hLinear:linear (fun beta:DB l=>Pure k l alpha beta):=
  ((@CartesianTestProduct.laws R h2 m n A B hA hB k l).1).2 alpha.
pose L:=@HomMap R (DB l) (@current_test_space R h2 (m+n) AB hAB (k+l))
  (fun beta=>Pure k l alpha beta) (introT (asboolP _) hLinear).
pose F:=hom_comp (@current_value R h2 (m+n) AB hAB (k+l) C) L.
pose O:=@current_test_opens R h2 n B hB l.
pose hO:=(smooth_test_final_topology_laws (hEB l) (hDerB l)).1.
have hContinuous:open_family_continuous O (norm_open_family (@scalar_absolute_value_norm R)) F.
  exact:(open_family_continuous_compose
    (@current_cartesian_test_product_second_continuous R h2 m n A B hA hB k l alpha)
    (@continuous_real_dual_member_continuous R (@current_test_space R h2 (m+n) AB hAB (k+l))
      (@current_test_opens R h2 (m+n) AB hAB (k+l))
      (smooth_test_final_topology_laws (hEC (k+l)) (hDerC (k+l))).1 C)).
have[T hT]:=@continuous_real_dual_represents R (DB l) O hO F hContinuous.
exists T=>beta;exact:(congr1 (fun f:Hom (DB l) R^o=>f beta) hT).
Qed.

(** Source for [current_cartesian_first_factor_current_exists]:
    fixing the second separated test in an arbitrary
    product-domain current gives a genuine current in
    the first factor, supporting the density argument
    for Federer 4.1.8, p. 361. No representation
    by measure is required. *)
Theorem current_cartesian_first_factor_current_exists k l (C:CC (k+l)) (beta:DB l):
  exists S:CA k,forall alpha:DA k,
    @current_value R h2 m A hA k S alpha=
    @current_value R h2 (m+n) AB hAB (k+l) C (Pure k l alpha beta).
Proof.
have hLinear:linear (fun alpha:DA k=>Pure k l alpha beta):=
  ((@CartesianTestProduct.laws R h2 m n A B hA hB k l).1).1 beta.
pose L:=@HomMap R (DA k) (@current_test_space R h2 (m+n) AB hAB (k+l))
  (fun alpha=>Pure k l alpha beta) (introT (asboolP _) hLinear).
pose F:=hom_comp (@current_value R h2 (m+n) AB hAB (k+l) C) L.
pose O:=@current_test_opens R h2 m A hA k.
pose hO:=(smooth_test_final_topology_laws (hEA k) (hDerA k)).1.
have hContinuous:open_family_continuous O (norm_open_family (@scalar_absolute_value_norm R)) F.
  exact:(open_family_continuous_compose
    (@current_cartesian_test_product_first_continuous R h2 m n A B hA hB k l beta)
    (@continuous_real_dual_member_continuous R (@current_test_space R h2 (m+n) AB hAB (k+l))
      (@current_test_opens R h2 (m+n) AB hAB (k+l))
      (smooth_test_final_topology_laws (hEC (k+l)) (hDerC (k+l))).1 C)).
have[S hS]:=@continuous_real_dual_represents R (DA k) O hO F hContinuous.
exists S=>alpha;exact:(congr1 (fun f:Hom (DA k) R^o=>f alpha) hS).
Qed.
End CurrentCartesianFactorCurrents.
