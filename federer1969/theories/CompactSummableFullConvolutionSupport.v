(** Federer (1969), 4.1.18, pp. 375–376: ordinary
    field smoothing has support in the original closed
    epsilon tube and is an actual compact summable
    smooth field. This retains the exact original
    support, rather than a chosen larger carrier. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentDomain CurrentVectorSpaces CurrentCoefficientNorms SmoothCompactSet SmoothingKernelUP SmoothingDilationUP
  SmoothingDilationNonzeroRadius SmoothingConvolutionUP CompactConvolutionSupport VectorSetSum
  EuclideanLebesgueDimensions EuclideanClosedSupportTube EuclideanClosedSupportTubeNorm
  CompactSummableMultivectors CompactSummableMultivectorAmbient CompactSummableFullConvolution
  CompactSummableMultivectorSmoothField.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactSummableFullConvolutionSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation W:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation value:=(@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation raw:=(@compact_summable_multivector_ambient_value R h2 n m Full hFull).
Local Notation support:=(@compact_summable_multivector_ambient_support R h2 n m Full hFull).
Local Notation V:=(exterior_power X m).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.

(** Source for [compact_summable_full_convolution_support]:
    ordinary Phi_epsilon*xi vanishes outside the actual
    closed epsilon neighbourhood of spt xi, supporting
    both propositions in Federer 4.1.18, pp. 375–376. *)
Theorem compact_summable_full_convolution_support (xi:W) (g:X->V):
  is_smoothing_convolution hVN (family epsilon) (raw xi) g ->
  forall x,~@euclidean_closed_support_tube R n (support xi) epsilon x->g x=0.
Proof.
move=>hConv.
have hOff:=(@compact_summable_multivector_ambient_support_laws R h2 n m Full hFull xi).2.2.
apply:(@compact_convolution_support_bound R X V NX VN hVN
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (support xi) (@euclidean_closed_support_tube R n (support xi) epsilon)
  epsilon (family epsilon) (raw xi) g
  (@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily epsilon hEpsilon)
  _ hOff hConv).
move=>x z hz hDistance.
have h:=@vector_set_sum_contains X (support xi) [set y|NX y<=epsilon] z (x-z) hz hDistance.
by rewrite addrC subrK in h.
Qed.

(** Source for [compact_summable_full_convolution_field_exists]:
    ordinary field smoothings belong to the same actual
    Omega space and retain their literal pointwise
    convolution graph, Federer 4.1.18, pp. 375–376. *)
Theorem compact_summable_full_convolution_field_exists (xi:W):
  exists zeta:W,
    is_smoothing_convolution hVN (family epsilon) (raw xi) (raw zeta) /\
    forall x,~@euclidean_closed_support_tube R n (support xi) epsilon x->raw zeta x=0.
Proof.
have[zetaSmooth [hConv _]]:=@compact_summable_full_convolution_exists R h2 n m
  phi family hPhi hFamily epsilon hEpsilon xi.
pose C:=@euclidean_closed_support_tube R n (support xi) epsilon.
have hC:@compact (real_norm_metric_space hNX) C.
  exact:(@euclidean_closed_support_tube_norm_compact R n (support xi) epsilon
    (@compact_summable_multivector_ambient_support_laws R h2 n m Full hFull xi).1).
pose K:=@Build_smooth_compact_set R X NX hNX Full C (fun _ _=>Logic.I) hC.
have hOff:=compact_summable_full_convolution_support hConv.
have[zeta hValue]:=@compact_summable_multivector_smooth_field R h2 n m Full hFull zetaSmooth K
  (fun x _ hx=>hOff x hx).
have hRaw:raw zeta=@current_vector_smooth_value R h2 n Full hFull m zetaSmooth.
  apply:funext=>x.
  pose x':current_domain R n Full:=exist _ x (mem_set Logic.I).
  change (raw zeta (set_val x')=
    @current_vector_smooth_value R h2 n Full hFull m zetaSmooth (set_val x')).
  rewrite compact_summable_multivector_ambient_inside hValue.
  reflexivity.
exists zeta;rewrite hRaw;by split.
Qed.
End CompactSummableFullConvolutionSupport.
