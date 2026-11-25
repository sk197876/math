(** Federer (1969), 4.1.18, p. 375, final
    display: the integral over U of the sum
    of the two ordinary convolution errors tends
    to zero as epsilon tends to zero from
    above. Each convolution retains its literal
    scale-dependent support tube. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  CurrentDomain CurrentCoefficientNorms CompactSummableMultivectors CompactSummableMultivectorAmbient
  CurrentLonePairImageUP CompactSummableOpenConvolution EuclideanOpenDomainMeasure
  EuclideanClosedSupportTube SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP
  MeasureIntegralUP SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PairConvolutionLone.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation WF d:=(@compact_summable_multivector_space R h2 n d Full hFull).
Local Notation value d:=(@compact_summable_multivector_value R h2 n d U hU).
Local Notation raw d:=(@compact_summable_multivector_ambient_value R h2 n d U hU).
Local Notation rawF d:=(@compact_summable_multivector_ambient_value R h2 n d Full hFull).
Local Notation support d:=(@compact_summable_multivector_ambient_support R h2 n d U hU).
Local Notation VN d:=(@current_vector_mass R h2 n d).
Local Notation hVN d:=(@current_vector_mass_real_norm R h2 n d).
Local Notation Pairs:=(@current_lone_pair_space R h2 n m U hU).
Local Notation mu:=(@euclidean_open_domain_measure R n U).
Local Notation hm:=(@euclidean_open_domain_measure_laws R n U hU).1.
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [compact_summable_pair_convolution_lone]:
    the literal two-error integral limit in the
    proof of the first proposition of 4.1.18,
    p. 375. Neither kernel evenness nor finite
    mass of the represented q is assumed. *)
Theorem compact_summable_pair_convolution_lone (v:Pairs) delta (hDelta:0<delta)
    (hInside:@euclidean_closed_support_tube R n
      (support m v.1 `|` support m.+1 v.2) delta `<=` U):
  exists P:R->WF m,exists Q:R->WF m.+1,
    (forall epsilon,0<epsilon->
      is_smoothing_convolution (hVN m) (family epsilon) (raw m v.1) (rawF m (P epsilon)) /\
      is_smoothing_convolution (hVN m.+1) (family epsilon) (raw m.+1 v.2) (rawF m.+1 (Q epsilon)) /\
      (forall x,~@euclidean_closed_support_tube R n (support m v.1) epsilon x->rawF m (P epsilon) x=0) /\
      (forall x,~@euclidean_closed_support_tube R n (support m.+1 v.2) epsilon x->rawF m.+1 (Q epsilon) x=0)) /\
    forall tolerance,0<tolerance->exists d:R,0<d /\
      forall epsilon,0<epsilon->epsilon<d->exists a:R,
        is_measure_integral mu (real_total_integrand (fun x:UT=>
          VN m (rawF m (P epsilon) (set_val x)-value m v.1 x)+
          VN m.+1 (rawF m.+1 (Q epsilon) (set_val x)-value m.+1 v.2 x))) a%:E /\
        a<tolerance.
Proof.
have[xiFull [P [_ [_ [hP hPLimit]]]]]:=@compact_summable_open_convolution_exists
  R h2 n m U hU phi family hPhi hFamily v.1.
have[etaFull [Q [_ [_ [hQ hQLimit]]]]]:=@compact_summable_open_convolution_exists
  R h2 n m.+1 U hU phi family hPhi hFamily v.2.
have hPTube:@euclidean_closed_support_tube R n (support m v.1) delta `<=` U.
  move=>x hx;apply:hInside.
  exact:(@euclidean_closed_support_tube_mono R n _ _ delta delta
    (fun _ h=>or_introl h) (lexx delta) x hx).
have hQTube:@euclidean_closed_support_tube R n (support m.+1 v.2) delta `<=` U.
  move=>x hx;apply:hInside.
  exact:(@euclidean_closed_support_tube_mono R n _ _ delta delta
    (fun _ h=>or_intror h) (lexx delta) x hx).
exists P,Q;split.
- move=>epsilon hEpsilon.
  have[hPConv hPOff]:=@hP epsilon hEpsilon.
  have[hQConv hQOff]:=@hQ epsilon hEpsilon.
  exact:(conj hPConv (conj hQConv (conj hPOff hQOff))).
- move=>tolerance hTolerance.
  have hHalf:0<tolerance/2 by rewrite divr_gt0 // ltr0n.
  have[dP [hDP hSmallP]]:=@hPLimit delta hDelta hPTube (tolerance/2) hHalf.
  have[dQ [hDQ hSmallQ]]:=@hQLimit delta hDelta hQTube (tolerance/2) hHalf.
  exists (Num.min dP dQ);split;first by rewrite lt_min hDP hDQ.
  move=>epsilon hEpsilon hSmall.
  have /andP [hEP hEQ]:(epsilon<dP)&&(epsilon<dQ) by rewrite -lt_min.
  have[a [hA hASmall]]:=@hSmallP epsilon hEpsilon hEP.
  have[b [hB hBSmall]]:=@hSmallQ epsilon hEpsilon hEQ.
  exists (a+b);split.
  - exact:(@real_total_integral_add R UT mu hm _ _ a b hA hB).
  - have h:=ltrD hASmall hBSmall;by rewrite -splitr in h.
Qed.
End PairConvolutionLone.
