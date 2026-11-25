(** Federer (1969), 4.1.18, p. 375: the
    ordinary convolutions of compact summable fields
    contract the literal L1 mass. The independently
    proved current mass estimate, with the explicitly
    reflected kernel, gives the exact coefficient one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom CurrentVectorSpaces EuclideanLebesgueDimensions RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentCoefficientNorms CurrentMassSealed CurrentDensityUniqueness CurrentSmoothLebesgue
  CurrentSmoothingOperators CurrentSmoothingMass SmoothingKernelUP SmoothingDilationUP
  SmoothingKernelReflection SmoothingConvolutionUP CompactSummableMultivectors
  CompactSummableMultivectorDensity CompactSummableMultivectorAmbient
  CompactSummableFullCurrentAction CompactSummableFullConvolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CompactSummableFullConvolutionMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation W:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation raw:=(@compact_summable_multivector_ambient_value R h2 n m Full hFull).
Local Notation size:=(@compact_summable_multivector_size R h2 n m Full hFull).
Local Notation A:=(@compact_summable_multivector_current R h2 n m Full hFull).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.

(** Source for [compact_summable_full_convolution_current]:
    ordinary field convolution represents actual current
    smoothing with the reflected kernel, supporting
    the normal approximants of 4.1.18, p. 375.
    This identity requires no symmetry of phi. *)
Theorem compact_summable_full_convolution_current (xi zeta:W):
  is_smoothing_convolution hVN (family epsilon) (raw xi) (raw zeta) ->
  A zeta=@current_smoothing R h2 n m
    (fun x:X=>phi (-x)) (fun e x=>family e (-x))
    (@smoothing_reflected_kernel_laws R n phi hPhi)
    (@smoothing_reflected_dilation_laws R n phi family hFamily) (A xi) epsilon.
Proof.
move=>hConv.
have[zetaSmooth [hSmoothConv hSmoothCurrent]]:=
  @compact_summable_full_convolution_exists R h2 n m
    phi family hPhi hFamily epsilon hEpsilon xi.
have hFields:=@smoothing_convolution_unique R n (exterior_power X m)
  (@current_vector_mass R h2 n m) hVN (family epsilon) (raw xi)
  (raw zeta) (@current_vector_smooth_value R h2 n Full hFull m zetaSmooth)
  hConv hSmoothConv.
have hAction:=@compact_summable_full_current_action R h2 n m zeta.
rewrite hFields in hAction.
have hCurrent:=@current_density_action_unique R h2 n m
  (@euclidean_lebesgue_measure R n)
  (@current_vector_smooth_value R h2 n Full hFull m zetaSmooth)
  (A zeta) (@current_smooth_lebesgue_map R h2 n m zetaSmooth)
  hAction (current_smooth_lebesgue_action zetaSmooth).
exact:(eq_trans hCurrent hSmoothCurrent).
Qed.

(** Source for [compact_summable_full_convolution_mass_bound]:
    the ordinary field convolution has L1 mass
    at most that of the original field, supporting
    the first proposition in 4.1.18, p. 375.
    Actual representatives, all degrees and empty supports
    are retained; there is no flatness assumption. *)
Theorem compact_summable_full_convolution_mass_bound (xi zeta:W):
  is_smoothing_convolution hVN (family epsilon) (raw xi) (raw zeta) ->
  size zeta<=size xi.
Proof.
move=>hConv.
have hCurrent:=compact_summable_full_convolution_current hConv.
have hMass:=@current_smoothing_mass_bound R h2 n m
  (fun x:X=>phi (-x)) (fun e x=>family e (-x))
  (@smoothing_reflected_kernel_laws R n phi hPhi)
  (@smoothing_reflected_dilation_laws R n phi family hFamily)
  epsilon hEpsilon (A xi).
rewrite -hCurrent
  !compact_summable_multivector_current_mass in hMass.
by move:hMass;rewrite lee_fin.
Qed.
End CompactSummableFullConvolutionMass.
