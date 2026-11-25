(** Federer (1969), 4.1.19, p. 377: divergence
    of the actual translated kernel multivector test
    is the finite sum of translated derivative-kernel
    tests with the original coordinate contractions.
    This combines only the two preceding exact formulas. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals topology.
From Federer Require Import Bilinear Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanCoordinateForms
  ExteriorGrading AlternatingForms OneCovectorInterior CurrentCoefficientNorms
  CurrentVectorSpaces CurrentOneCovectorMap CurrentDivergenceMap DivergenceCoordinates
  SmoothCurrentDivergence SmoothFunctionSpaceUP SmoothFunctionSpaceLaws
  SmoothTestSpaces SmoothTestEvaluation ContinuousMultilinearSealed ContinuousMultilinearOne
  TranslatedKernelTestUP TranslatedKernelFirstDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section KernelDivergence.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NS := (fun t : R^o => `|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Local Notation V d := (exterior_power X d).
Local Notation VN d := (@current_vector_mass R h2 n d).
Local Notation hVN d := (@current_vector_mass_real_norm R h2 n d).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation E d := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation ev d := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation hE d := (@current_vector_smooth_space_laws R h2 n Full hFull d).
Local Notation D d := (@current_vector_smooth_derivatives R h2 n Full hFull d).
Local Notation hD d := (@current_vector_smooth_derivative_laws R h2 n Full hFull d).
Local Notation DT d := (smooth_test_space (hE d)).
Local Notation div := (@smooth_current_divergence R h2 n m Full hFull).
Local Notation cut j := (@current_one_covector_map R h2 n m (euclidean_coordinate_form j)).
Local Notation Jet := (@current_vector_smooth_derivatives R h2 n Full hFull m.+1).
Local Notation Z1 := (@ContinuousMultilinear.space R 1%N X (V m.+1)
  NX (VN m.+1) hNX (hVN m.+1)).
Local Notation evZ1 := (@ContinuousMultilinear.evaluation R 1%N X (V m.+1)
  NX (VN m.+1) hNX (hVN m.+1)).
Local Notation NZ1 := (@ContinuousMultilinear.norm R 1%N X (V m.+1)
  NX (VN m.+1) hNX (hVN m.+1)).
Local Notation hZ1 := (@ContinuousMultilinear.laws R 1%N X (V m.+1)
  NX (VN m.+1) hNX (hVN m.+1)).
Local Notation J := (@continuous_multilinear_one_evaluation R X (V m.+1) Z1
  NX (VN m.+1) evZ1 NZ1 hZ1).
Variable kernel : X -> R.
Hypothesis hKernel : norm_class_all_orders hNX hNS Full kernel.
Variable theta : 'I_n -> X -> R.
Variable G : 'I_n -> X -> Hom X R^o.
Hypothesis hG : forall j x, has_norm_differential NX NS Full kernel x (G j x).
Hypothesis hTheta : forall j x, G j x (@coordinate_basis R n j)=theta j x.
Variable B : X -> Hom (V m.+1) (DT m.+1).
Variable C : 'I_n -> X -> Hom (V m) (DT m).
Hypothesis hB : @is_translated_kernel_tests R X (V m.+1) NX (VN m.+1)
  hNX (hVN m.+1) (E m.+1) (ev m.+1) (hE m.+1) kernel B.
Hypothesis hC : forall j, @is_translated_kernel_tests R X (V m) NX (VN m)
  hNX (hVN m) (E m) (ev m) (hE m) (theta j) (C j).

(** Source for [current_kernel_test_divergence_values]:
    div_x[kernel(x-z) theta] equals the sum
    of D_j kernel(x-z) times theta contracted DX_j,
    supporting the smoothing criterion of Federer
    4.1.19, p. 377. All tests are
    actual old compact smooth tests, not raw surrogates. *)
Theorem current_kernel_test_divergence_values z (a : V m.+1) x :
  ev m (div (smooth_test_inclusion (hE m.+1) (B z a))) x=
    smooth_test_value (hE m) (\sum_(j : 'I_n) C j z (cut j a)) x.
Proof.
rewrite (@smooth_current_divergence_values R h2 n m Full hFull
  (smooth_test_inclusion (hE m.+1) (B z a)) x Logic.I)
  /current_divergence_map hom_compE divergence_coordinate_formula.
change ((\sum_j cut j (J (@Jet 1%N x
    (smooth_test_inclusion (hE m.+1) (B z a))) (@coordinate_basis R n j)))=
  smooth_test_values_hom (hE m) (\sum_j C j z (cut j a)) x).
rewrite linear_sum fct_sumE; apply: eq_bigr=> j _.
have hDerivative := @translated_kernel_first_derivative_value R n (V m.+1)
  (VN m.+1) (hVN m.+1) (E m.+1) (ev m.+1) (hE m.+1)
  (D m.+1) (hD m.+1) kernel hKernel (G j) (@hG j) B hB
  z a x (@coordinate_basis R n j).
rewrite (@hTheta j (x-z)) in hDerivative.
change (cut j (@ContinuousMultilinear.evaluation R 1%N X (V m.+1) NX (VN m.+1)
    hNX (hVN m.+1) [ffun _ : 'I_1 => @coordinate_basis R n j]
    (@Jet 1%N x (smooth_test_inclusion (hE m.+1) (B z a))))=
  smooth_test_value (hE m) (C j z (cut j a)) x).
rewrite (@hC j z (cut j a) x) hDerivative.
exact: (linZ (hom_linear (cut j)) _ _).
Qed.
End KernelDivergence.
