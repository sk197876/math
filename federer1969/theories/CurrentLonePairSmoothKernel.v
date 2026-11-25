(** Federer (1969), 4.1.18, p. 377:
    smoothing a q-zero pair gives exactly
    the original smooth divergence graph.
    Reuse reflected current smoothing, boundary
    commutation, the old smooth boundary identity
    and exact smooth-density injectivity by continuous smoothing. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentCoefficientNorms CurrentVectorSpaces
  CurrentBoundary CurrentSmoothLebesgue CurrentSmoothLebesgueBoundary
  SmoothCurrentDivergence CurrentSmoothLebesgueInjective
  CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorAmbient CurrentLonePairImageUP CurrentLonePairImageSealed
  CurrentSmoothingOperators CurrentSmoothingExteriorDerivative
  CurrentSmoothConvolutionImage SmoothingKernelUP SmoothingDilationUP
  SmoothingKernelReflection SmoothingConvolutionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SmoothKernelGraph.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation F d := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation fv d := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation P := (@current_lone_pair_space R h2 n m Full hFull).
Local Notation raw d := (@compact_summable_multivector_ambient_value R h2 n d Full hFull).
Local Notation A d := (@compact_summable_multivector_current R h2 n d Full hFull).
Local Notation L d := (@current_smooth_lebesgue_map R h2 n d).
Local Notation hVN d := (@current_vector_mass_real_norm R h2 n d).
Local Notation div := (@smooth_current_divergence R h2 n m Full hFull).
Variables (phi : X -> R) (family : R -> X -> R).
Hypothesis hPhi : is_smoothing_kernel phi.
Hypothesis hFamily : is_smoothing_dilation phi family.
Variable epsilon : R.
Hypothesis hEpsilon : 0 < epsilon.
Local Notation refPhi := (fun x : X => phi (-x)).
Local Notation refFamily := (fun e x => family e (-x)).
Local Notation hRefPhi := (@smoothing_reflected_kernel_laws R n phi hPhi).
Local Notation hRefFamily := (@smoothing_reflected_dilation_laws R n phi family hFamily).
Local Notation smooth d :=
  (@current_smoothing R h2 n d refPhi refFamily hRefPhi hRefFamily).

(** Source for [current_lone_pair_full_smooth_kernel]:
    the ordinary smoothed first field equals
    the actual divergence of the ordinary
    smoothed second field, the exact graph
    verification in Federer 4.1.18, p. 377.
    The original arbitrary nonsymmetric kernel
    is retained through its explicit reflection. *)
Theorem current_lone_pair_full_smooth_kernel (v : P)
    (f : F m) (g : F m.+1) :
  @CurrentLonePair.map R h2 n m Full hFull v=0 ->
  is_smoothing_convolution (hVN m) (family epsilon) (raw m v.1) (fv m f) ->
  is_smoothing_convolution (hVN m.+1) (family epsilon) (raw m.+1 v.2) (fv m.+1 g) ->
  f=div g.
Proof.
move=> hZero hF hG.
have hFirst := @current_smooth_convolution_image R h2 n m phi family
  hPhi hFamily epsilon hEpsilon v.1 f hF.
have hSecond := @current_smooth_convolution_image R h2 n m.+1 phi family
  hPhi hFamily epsilon hEpsilon v.2 g hG.
have hLinear := @current_smoothing_linear R h2 n m refPhi refFamily
  hRefPhi hRefFamily epsilon hEpsilon.
have hPair : L m f+@current_boundary R h2 n m Full hFull (L m.+1 g)=0.
  rewrite hFirst hSecond
    (@current_smoothing_boundary_commutation R h2 n m refPhi refFamily
      hRefPhi hRefFamily epsilon hEpsilon (A m.+1 v.2))
    -(linD hLinear) -(@CurrentLonePair.laws R h2 n m Full hFull v) hZero.
  exact: (lin0 hLinear).
rewrite (@current_smooth_lebesgue_boundary R h2 n m g) in hPair.
apply: (@current_smooth_lebesgue_map_injective R h2 n m).
by apply/eqP; rewrite -subr_eq0; apply/eqP.
Qed.
End SmoothKernelGraph.
