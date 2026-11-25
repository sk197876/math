(** Federer (1969), 4.1.18, p. 375: both
    ordinary field convolutions in the first proposition
    converge in the original L1 seminorm. The proof
    follows density by compact continuous fields, their
    compact uniform smoothing, and exact L1 contraction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentDomain CurrentVectorCompleteness CurrentCoefficientNorms
  CompactSummableFieldLaws CompactSummableFieldIntegral CompactSummableFieldContinuous
  CompactSummableMultivectors CompactSummableMultivectorAmbient CompactSummableMultivectorDifference
  CompactSummableFullConvolutionFamily CompactSummableFullConvolutionMass
  CompactContinuousFullConvolutionLone SmoothingConvolutionUP SmoothingConvolutionArithmetic
  SmoothingKernelUP SmoothingDilationUP EuclideanOpenDomainMeasure
  CompactContinuousLoneDensity CompactContinuousVectorFields RadonCompactScalarIntegral
  MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactSummableFullConvolutionLone.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation FT:=(current_domain R n Full).
Local Notation V:=(exterior_power X m).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Local Notation hSep:=(@current_multivector_mass_separable R h2 n m).
Local Notation W:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation value:=(@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation raw:=(@compact_summable_multivector_ambient_value R h2 n m Full hFull).
Local Notation size:=(@compact_summable_multivector_size R h2 n m Full hFull).
Local Notation hSize:=(@compact_summable_multivector_size_laws R h2 n m Full hFull).
Local Notation mu:=(@euclidean_open_domain_measure R n Full).
Local Notation hm:=(@euclidean_open_domain_measure_laws R n Full hFull).1.
Local Notation hr:=(@euclidean_open_domain_measure_laws R n Full hFull).2.
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [compact_summable_full_convolution_lone]:
    integral mass(Phi_epsilon*xi-xi) tends to zero
    for every original compact summable field xi,
    Federer 4.1.18, p. 375. The ordinary kernel
    remains arbitrary and need not be even. *)
Theorem compact_summable_full_convolution_lone (xi:W) (P:R->W):
  (forall epsilon,0<epsilon->
    is_smoothing_convolution hVN (family epsilon) (raw xi) (raw (P epsilon))) ->
  forall eta:R,0<eta->exists d:R,0<d /\
    forall epsilon,0<epsilon->epsilon<d->size (P epsilon-xi)<eta.
Proof.
move=>hConv eta hEta.
have hEta3:0<eta/3 by rewrite divr_gt0 // ltr0n.
have hDense:=@compact_continuous_vector_lone_dense R FT V VN hVN hSep mu hm hr
  (@radon_positive_compact_integral R FT mu hm hr)
  (@radon_positive_compact_integral_laws R FT mu hm hr) (value xi)
  (@compact_summable_field_lone R FT V VN hVN mu hm xi).
have[w [a [hW [hError hA]]]]:=hDense (eta/3) hEta3.
have[zeta hValue]:=@compact_summable_continuous_field_representative R FT V VN hVN
  hSep mu hm hr w hW.
have hZetaValue:value zeta=w:=hValue.
have hZetaContinuous:compact_continuous_vector_fields hVN (value zeta).
  by rewrite hZetaValue.
have hSizeError:size (xi-zeta)=a.
  have hActual:=@compact_summable_multivector_difference_integral R h2 n m Full hFull xi zeta.
  rewrite hZetaValue in hActual.
  exact:(EFin_inj (measure_integral_unique hActual hError)).
have[Q hQ]:=@compact_summable_full_convolution_family_exists R h2 n m
  phi family hPhi hFamily zeta.
have hQConv:forall epsilon,0<epsilon->
    is_smoothing_convolution hVN (family epsilon) (raw zeta) (raw (Q epsilon)).
  by move=>epsilon hEpsilon;exact:(@hQ epsilon hEpsilon).1.
have[d [hD hMiddle]]:=@compact_continuous_full_convolution_lone R h2 n m
  phi family hPhi hFamily zeta Q hZetaContinuous hQConv (eta/3) hEta3.
exists d;split=>// epsilon hEpsilon hSmall.
have hDifference:is_smoothing_convolution hVN (family epsilon) (raw (xi-zeta))
    (raw (P epsilon-Q epsilon)).
  rewrite !compact_summable_multivector_ambient_difference.
  exact:(@smoothing_convolution_subtract R n V VN hVN (family epsilon)
    (raw xi) (raw zeta) (raw (P epsilon)) (raw (Q epsilon))
    (@hConv epsilon hEpsilon) (@hQConv epsilon hEpsilon)).
have hContract:=@compact_summable_full_convolution_mass_bound R h2 n m
  phi family hPhi hFamily epsilon hEpsilon (xi-zeta) (P epsilon-Q epsilon) hDifference.
rewrite hSizeError in hContract.
have hNear:=@hMiddle epsilon hEpsilon hSmall.
have hReverse:size (zeta-xi)=a.
  by rewrite compact_summable_multivector_difference_symmetric hSizeError.
have hIdentity:P epsilon-xi=(P epsilon-Q epsilon)+(Q epsilon-zeta)+(zeta-xi).
  by rewrite !addrA !subrK.
rewrite hIdentity.
have hFirst:=real_seminorm_triangle hSize
  (P epsilon-Q epsilon+(Q epsilon-zeta)) (zeta-xi).
have hSecond:=real_seminorm_triangle hSize (P epsilon-Q epsilon) (Q epsilon-zeta).
have hUpper:=le_trans hFirst (lerD hSecond (lexx (size (zeta-xi)))).
rewrite hReverse in hUpper.
apply:le_lt_trans hUpper _.
have hAux:=lerD hContract (ltW hNear).
lra.
Qed.
End CompactSummableFullConvolutionLone.
