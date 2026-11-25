(** Federer (1969), 4.1.18, p. 375: ordinary
    convolution converges in L1 for the compact
    continuous core of Omega. Reuse the already
    proved compact uniform convolution approximation
    and Radon compact finiteness of 4.1.5. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentDomain CurrentVectorSpaces CurrentVectorCompleteness CurrentCoefficientNorms
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionSubspaceTestValues
  CompactSupportFunctionUP CompactContinuousVectorFields CompactContinuousDomainFields CompactContinuousVectorZeroExtension
  CompactContinuousVectorAlgebra CompactContinuousConvolutionApproximation CompactUniformApproximationUP
  IsotropyGroupTopology EuclideanOpenDomainMeasure CompactSummableMultivectors
  CompactSummableMultivectorAmbient CompactSummableMultivectorDifference
  SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP
  MeasureUP MeasureBasic RadonMeasureUP RadonBorelRegularity RadonCompactScalarIntegral
  MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP CompactFieldUniformIntegralBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactContinuousFullConvolutionLone.
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
Local Notation V:=(exterior_power X m).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Local Notation W:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation value:=(@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation raw:=(@compact_summable_multivector_ambient_value R h2 n m Full hFull).
Local Notation size:=(@compact_summable_multivector_size R h2 n m Full hFull).
Local Notation E:=(@current_vector_smooth_space R h2 n Full hFull m).
Local Notation ev:=(@current_vector_smooth_value R h2 n Full hFull m).
Local Notation hE:=(@current_vector_smooth_space_laws R h2 n Full hFull m).
Local Notation mu:=(@euclidean_open_domain_measure R n Full).
Local Notation hm:=(@euclidean_open_domain_measure_laws R n Full hFull).1.
Local Notation hr:=(@euclidean_open_domain_measure_laws R n Full hFull).2.
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [compact_continuous_full_convolution_lone]:
    ordinary Phi_epsilon*xi tends to xi in
    the original L1 seminorm for compact continuous
    xi, the dense-core step of Federer 4.1.18,
    p. 375. Every sufficiently small positive
    epsilon is covered, not merely a subsequence. *)
Theorem compact_continuous_full_convolution_lone (xi:W) (P:R->W):
  compact_continuous_vector_fields hVN (value xi) ->
  (forall epsilon,0<epsilon->
    is_smoothing_convolution hVN (family epsilon) (raw xi) (raw (P epsilon))) ->
  forall eta:R,0<eta->exists d:R,0<d /\
    forall epsilon,0<epsilon->epsilon<d->size (P epsilon-xi)<eta.
Proof.
move=>hXi hConv eta hEta.
have hRaw:@compact_continuous_vector_fields R XT V VN hVN (raw xi).
  exact:(@compact_vector_open_extension_compact R XT (@metric_hausdorff R XT)
    Full openT V VN hVN (value xi) hXi).
have hDomain:@compact_continuous_domain_fields R XT Full V VN hVN (raw xi).
  by split;last move=>x _.
have[Q [hApprox [rConv [hRConv hQConv]]]]:=
  @compact_continuous_convolution_test_approximation R n V VN hVN
    (@current_multivector_mass_complete R h2 n m) Full hFull E ev hE
    phi hPhi family hFamily (raw xi) hDomain.
have[C [hC [_ [r [hR [hOff hUniform]]]]]]:=hApprox.
pose K:set FT:=(set_val @^-1` C) `|`
  @real_function_support R FT (fun x=>VN (value xi x)).
have hK:compact K:=compactU (@set_type_compact_preimage XT Full C hC
  (fun _ _=>Logic.I)) hXi.2.
have hFinite:mu K \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm K)).
  exact:(@radon_compact_finite R FT mu hr K hK).
pose c:=fine (mu K).
have hCNonnegative:0<=c.
  have h:=measure_nonnegative hm K.
  by rewrite -(fineK hFinite) lee_fin in h.
have hDen:0<c+1 by lra.
pose delta:=eta/(c+1).
have hDelta:0<delta by rewrite /delta divr_gt0.
have[d0 [hD0 hSmall]]:=@hUniform delta hDelta.
pose d:=Num.min r (Num.min rConv d0).
have hD:0<d by rewrite /d !lt_min hR hRConv hD0.
exists d;split=>// epsilon hEpsilon hEpsilonD.
have /andP [hER /andP [hERConv hED0]]:
    (epsilon<r)&&((epsilon<rConv)&&(epsilon<d0)).
  by rewrite -!lt_min -/d.
have hFields:=@smoothing_convolution_unique R n V VN hVN (family epsilon) (raw xi)
  (raw (P epsilon)) (smooth_test_value hE (Q epsilon))
  (@hConv epsilon hEpsilon) (@hQConv epsilon hEpsilon hERConv).
pose q:=fun x:FT=>smooth_test_value hE (Q epsilon) (set_val x).
have hValues:value (P epsilon)=q.
  apply:funext=>x.
  rewrite -(compact_summable_multivector_ambient_inside (P epsilon) x).
  exact:(congr1 (fun g:X->V=>g (set_val x)) hFields).
have hQ:@compact_continuous_vector_fields R FT V VN hVN q.
  exact:(@smooth_test_original_continuous_field R X V NX VN hNX hVN
    Full E ev hE (Q epsilon)).
pose u:=fun x:FT=>value (P epsilon) x-value xi x.
have hU:@compact_continuous_vector_fields R FT V VN hVN u.
  rewrite /u hValues;exact:compact_continuous_vector_subtract hQ hXi.
have hBound:forall x:FT,VN (u x)<=delta.
  move=>x;have h:=@hSmall epsilon hEpsilon hED0 (set_val x).
  change (is_true (VN (smooth_test_value hE (Q epsilon) (set_val x)-
    raw xi (set_val x))<delta)) in h.
  rewrite -hFields (compact_summable_multivector_ambient_inside (P epsilon) x)
    (compact_summable_multivector_ambient_inside xi x) in h.
  exact:ltW h.
have hUOff:forall x:FT,~K x->u x=0.
  move=>x hx.
  have hNoC:~C (set_val x) by move=>h;apply:hx;by left.
  have hNoXi:~@real_function_support R FT (fun y=>VN (value xi y)) x.
    move=>h;apply:hx;by right.
  have hZero:=@hOff epsilon hEpsilon hER (set_val x) hNoC.
  change (smooth_test_value hE (Q epsilon) (set_val x)=0) in hZero.
  rewrite /u hValues /q hZero
    (@compact_continuous_vector_zero_off_norm_support R FT V VN hVN
      (value xi) x hNoXi) subrr.
  reflexivity.
have[a [hIntegral hA]]:=@compact_field_uniform_integral_bound R FT V VN hVN mu hm hr
  (@radon_positive_compact_integral R FT mu hm hr)
  (@radon_positive_compact_integral_laws R FT mu hm hr) u K delta hU hK hDelta hBound hUOff.
have hActual:=@compact_summable_multivector_difference_integral R h2 n m Full hFull
  (P epsilon) xi.
have hSize:size (P epsilon-xi)=a.
  exact:(EFin_inj (measure_integral_unique hActual hIntegral)).
rewrite hSize.
have hStrict:delta*c<delta*(c+1) by rewrite ltr_pM2l //;lra.
have hDenNonzero:c+1!=0 by rewrite (gt_eqF hDen).
have hBudget:delta*(c+1)=eta by rewrite /delta divfK //.
rewrite hBudget in hStrict;exact:le_lt_trans hA hStrict.
Qed.
End CompactContinuousFullConvolutionLone.
