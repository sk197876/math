(** Federer (1969), 4.1.18, p. 375: the
    ordinary convolutions of an Omega field exist
    simultaneously at every positive smoothing scale.
    Only existence is asserted for the family;
    subsequent limits apply to every family satisfying
    the independently stated convolution graph. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentCoefficientNorms CompactSummableMultivectors CompactSummableMultivectorAmbient
  SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP
  CompactSummableFullConvolutionSupport EuclideanClosedSupportTube.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CompactSummableFullConvolutionFamily.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation W:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation raw:=(@compact_summable_multivector_ambient_value R h2 n m Full hFull).
Local Notation support:=(@compact_summable_multivector_ambient_support R h2 n m Full hFull).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [compact_summable_full_convolution_family_exists]:
    the actual ordinary smoothing family in the
    first proposition of Federer 4.1.18, p. 375,
    with the literal scale-dependent support tube. *)
Theorem compact_summable_full_convolution_family_exists (xi:W):
  exists P:R->W,forall epsilon,0<epsilon->
    is_smoothing_convolution hVN (family epsilon) (raw xi) (raw (P epsilon)) /\
    forall x,~@euclidean_closed_support_tube R n (support xi) epsilon x->raw (P epsilon) x=0.
Proof.
have hEach epsilon:exists zeta:W,0<epsilon->
    is_smoothing_convolution hVN (family epsilon) (raw xi) (raw zeta) /\
    forall x,~@euclidean_closed_support_tube R n (support xi) epsilon x->raw zeta x=0.
  case:(pselect (0<epsilon))=>[hPositive|hNotPositive].
  - have[zeta hZeta]:=@compact_summable_full_convolution_field_exists R h2 n m
      phi family hPhi hFamily epsilon hPositive xi.
    by exists zeta.
  - exists 0;move=>hPositive;exact:False_ind _ (hNotPositive hPositive).
have[P hP]:=choice hEach.
by exists P.
Qed.
End CompactSummableFullConvolutionFamily.
