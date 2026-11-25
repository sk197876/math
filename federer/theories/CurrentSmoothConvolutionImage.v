(** Federer (1969), 4.1.18, pp. 375, 377:
    every actual smooth representative of an
    ordinary Omega convolution has the same
    reflected-kernel current smoothing image. The
    earlier convolution uniqueness gives exact
    smooth equality, not almost equality. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentSpaces CurrentCoefficientNorms CurrentVectorSpaces
  SmoothFunctionSpaceUP CurrentSmoothLebesgue CurrentSmoothingOperators
  CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorAmbient CompactSummableFullConvolution
  SmoothingKernelUP SmoothingDilationUP SmoothingKernelReflection
  SmoothingConvolutionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section SmoothConvolutionImage.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n d : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation F := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation fv := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation hF := (@current_vector_smooth_space_laws R h2 n Full hFull d).
Local Notation W := (@compact_summable_multivector_space R h2 n d Full hFull).
Local Notation raw := (@compact_summable_multivector_ambient_value R h2 n d Full hFull).
Local Notation A := (@compact_summable_multivector_current R h2 n d Full hFull).
Local Notation hVN := (@current_vector_mass_real_norm R h2 n d).
Variables (phi : X -> R) (family : R -> X -> R).
Hypothesis hPhi : is_smoothing_kernel phi.
Hypothesis hFamily : is_smoothing_dilation phi family.
Variable epsilon : R.
Hypothesis hEpsilon : 0 < epsilon.

(** Source for [current_smooth_convolution_image]:
    the smooth ordinary convolution used in
    the original graph argument of Federer
    4.1.18, p. 377, has exactly
    the reflected original current-smoothing image.
    Every independently given actual smooth
    convolution representative is admitted. *)
Theorem current_smooth_convolution_image (xi : W) (f : F) :
  is_smoothing_convolution hVN (family epsilon) (raw xi) (fv f) ->
  @current_smooth_lebesgue_map R h2 n d f=
    @current_smoothing R h2 n d
      (fun x : X => phi (-x)) (fun e x => family e (-x))
      (@smoothing_reflected_kernel_laws R n phi hPhi)
      (@smoothing_reflected_dilation_laws R n phi family hFamily) (A xi) epsilon.
Proof.
move=> hConv.
have [g [hGConv hGImage]] := @compact_summable_full_convolution_exists R h2 n d
  phi family hPhi hFamily epsilon hEpsilon xi.
have hFields := @smoothing_convolution_unique R n (exterior_power X d)
  (@current_vector_mass R h2 n d) hVN (family epsilon) (raw xi)
  (fv f) (fv g) hConv hGConv.
have hEqual : f=g := smooth_function_evaluation_injective hF hFields.
by rewrite hEqual.
Qed.
End SmoothConvolutionImage.
