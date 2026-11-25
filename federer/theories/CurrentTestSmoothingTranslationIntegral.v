(** Federer (1969), 4.1.18, p. 374: the
    actual compact test regularisation has the original
    reflected translation integral. All spaces and
    translations are the previously specified actual
    opaque operators.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentSpaces CurrentCoefficientNorms SmoothTestSpaces
  SmoothTestEvaluation PartialFunctionBasic MeasureVectorIntegralUP
  EuclideanLebesgueDimensions EuclideanAdditiveGroup SmoothingKernelUP SmoothingDilationUP
  CurrentTranslations CurrentSmoothingOperators SmoothingReflectedTranslationIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentTestSmoothingTranslationIntegral.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation Y:=(A_m X R^o m).
Local Notation NY:=(@current_form_comass R h2 n m).
Local Notation hNY:=(@current_form_comass_real_norm R h2 n m).
Local Notation E:=(@current_smooth_space R h2 n Full hFull m).
Local Notation ev:=(@current_smooth_value R h2 n Full hFull m).
Local Notation hE:=(@current_smooth_space_laws R h2 n Full hFull m).
Local Notation DT:=(@current_test_space R h2 n Full hFull m).
Local Notation value:=(@current_test_value R h2 n Full hFull m).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [current_test_smoothing_translation_integral]:
    literal actual-form values in the first integral
    display of Federer 4.1.18, p. 374.
    The weight is Phi_epsilon(-z), including
    nonsymmetric kernels and ambient dimension zero. *)
Theorem current_test_smoothing_translation_integral epsilon:
  0<epsilon ->forall omega:DT,forall x:X,
  is_measure_vector_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun z=>
      (family epsilon (-z)*:
        value (@current_translation_test R h2 n m z omega) x:
        real_norm_metric_space hNY)))
    (value (@current_test_smoothing R h2 n m phi family hPhi hFamily epsilon omega) x).
Proof.
move=>hEpsilon omega x.
have hOriginal:=@smoothing_reflected_translation_integral R n Y NY hNY
  (family epsilon) (value omega)
  (ev (@current_smooth_smoothing R h2 n m phi family hPhi hFamily epsilon
    (smooth_test_inclusion hE omega)))
  (@current_smooth_smoothing_convolution R h2 n m phi family hPhi hFamily
    epsilon hEpsilon (smooth_test_inclusion hE omega)) x.
have hFunction:(fun z=>
    (family epsilon (-z)*:value (@current_translation_test R h2 n m z omega) x:
      real_norm_metric_space hNY))=
    (fun z=>(family epsilon (-z)*:value omega (x+z):real_norm_metric_space hNY)).
  apply:funext=>z;rewrite current_translation_test_values /euclidean_translation addrC.
  reflexivity.
rewrite hFunction.
change (@is_measure_vector_integral R X Y NY hNY
  (@euclidean_lebesgue_measure R n)
  (partial_function_total (fun z=>(family epsilon (-z)*:value omega (x+z):
    real_norm_metric_space hNY)))
  (ev (smooth_test_inclusion hE
    (@current_test_smoothing R h2 n m phi family hPhi hFamily epsilon omega)) x)).
rewrite (@current_test_smoothing_inclusion R h2 n m phi family hPhi hFamily
  epsilon hEpsilon omega).
exact:hOriginal.
Qed.
End CurrentTestSmoothingTranslationIntegral.
