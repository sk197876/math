(** Federer (1969), 4.1.18, p. 375: ordinary
    Phi_epsilon*xi is defined from the literal
    zero extension of xi on its original open U.
    Its support lies in the exact epsilon tube;
    its L1 error over U tends to zero. All
    sufficiently small positive scales are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import NormBoundedLinearTopology RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentDomain CurrentCoefficientNorms CompactSummableMultivectors
  CompactSummableMultivectorAmbient CompactSummableMultivectorAmbientAgreement
  CompactSummableMultivectorDifference CompactSummableFullConvolutionFamily
  CompactSummableFullConvolutionLone EuclideanClosedSupportTube EuclideanOpenDomainMeasure
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP OpenSubspaceSupportedIntegral
  MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OpenConvolution.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation FT:=(current_domain R n Full).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation WU:=(@compact_summable_multivector_space R h2 n m U hU).
Local Notation WF:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation valueU:=(@compact_summable_multivector_value R h2 n m U hU).
Local Notation valueF:=(@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation rawU:=(@compact_summable_multivector_ambient_value R h2 n m U hU).
Local Notation rawF:=(@compact_summable_multivector_ambient_value R h2 n m Full hFull).
Local Notation sizeU:=(@compact_summable_multivector_size R h2 n m U hU).
Local Notation sizeF:=(@compact_summable_multivector_size R h2 n m Full hFull).
Local Notation supportU:=(@compact_summable_multivector_ambient_support R h2 n m U hU).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [compact_summable_open_convolution_exists]:
    ordinary convolution, its literal support and L1
    convergence over the original U, Federer 4.1.18,
    p. 375. The radius allowance is used
    only to keep the original convolution support
    in U, as in the printed first proposition. *)
Theorem compact_summable_open_convolution_exists (xi:WU):
  exists xiFull:WF,exists P:R->WF,
    valueF xiFull=(fun x:FT=>rawU xi (set_val x)) /\
    sizeF xiFull=sizeU xi /\
    (forall epsilon,0<epsilon->
      is_smoothing_convolution hVN (family epsilon) (rawU xi) (rawF (P epsilon)) /\
      forall x,~@euclidean_closed_support_tube R n (supportU xi) epsilon x->rawF (P epsilon) x=0) /\
    forall delta,0<delta->
      (@euclidean_closed_support_tube R n (supportU xi) delta `<=` U)->
      forall eta,0<eta->exists d:R,0<d /\
        forall epsilon,0<epsilon->epsilon<d->exists a:R,
          is_measure_integral (@euclidean_open_domain_measure R n U)
            (real_total_integrand (fun x:UT=>VN (rawF (P epsilon) (set_val x)-valueU xi x)))
            a%:E /\a<eta.
Proof.
have[xiFull [hValue hSize]]:=@compact_summable_multivector_ambient_representative
  R h2 n m U hU xi.
have hRaw:=@compact_summable_multivector_full_ambient_agreement R h2 n m U hU
  xi xiFull hValue.
have hSupport:=@compact_summable_multivector_full_support_agreement R h2 n m U hU
  xi xiFull hValue.
have[P hP]:=@compact_summable_full_convolution_family_exists R h2 n m
  phi family hPhi hFamily xiFull.
exists xiFull,P;split;first exact:hValue.
split;first exact:hSize.
split.
- move=>epsilon hEpsilon;have h:=@hP epsilon hEpsilon.
  by rewrite hRaw hSupport in h.
- move=>delta hDelta hTube eta hEta.
  have hConv:forall epsilon,0<epsilon->
      is_smoothing_convolution hVN (family epsilon) (rawF xiFull) (rawF (P epsilon)).
    by move=>epsilon hEpsilon;exact:(@hP epsilon hEpsilon).1.
  have[d0 [hD0 hLimit]]:=@compact_summable_full_convolution_lone R h2 n m
    phi family hPhi hFamily xiFull P hConv eta hEta.
  pose d:=Num.min delta d0.
  have hD:0<d by rewrite /d lt_min hDelta hD0.
  exists d;split=>// epsilon hEpsilon hSmall.
  have /andP [hEDelta hED0]:(epsilon<delta)&&(epsilon<d0) by rewrite -lt_min -/d.
  pose a:=sizeF (P epsilon-xiFull).
  have hA:a<eta:=@hLimit epsilon hEpsilon hED0.
  have hIntegral:=@compact_summable_multivector_ambient_integral R h2 n m Full hFull
    (P epsilon-xiFull).
  rewrite compact_summable_multivector_ambient_difference hRaw in hIntegral.
  pose error:=fun x:X=>VN (rawF (P epsilon) x-rawU xi x).
  have hErrorOff:forall x,~U x->error x=0.
    move=>x hx.
    have hNoTube:~@euclidean_closed_support_tube R n
        (@compact_summable_multivector_ambient_support R h2 n m Full hFull xiFull) epsilon x.
      move=>h;apply:hx;apply:hTube.
      rewrite -hSupport.
      exact:(@euclidean_closed_support_tube_mono R n _ _ epsilon delta
        (fun _ hy=>hy) (ltW hEDelta) x h).
    rewrite /error ((@hP epsilon hEpsilon).2 x hNoTube)
      (@compact_summable_multivector_ambient_outside R h2 n m U hU xi x hx)
      subrr (real_seminorm_zero hVN.1).
    reflexivity.
  have hOpen:@open XT U.
    rewrite openE=>x hx.
    exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).1 (@hU x hx).
  have hMeas:=@euclidean_distribution_measure_open R n U hOpen.
  have hOnU:=@open_subspace_supported_total_integral R XT U
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
    hMeas error a%:E hErrorOff hIntegral.
  have hFunction:(fun x:UT=>error (set_val x))=
      (fun x:UT=>VN (rawF (P epsilon) (set_val x)-valueU xi x)).
    apply:funext=>x;by rewrite /error compact_summable_multivector_ambient_inside.
  exists a;split;last exact:hA.
  by rewrite hFunction in hOnU.
Qed.
End OpenConvolution.
