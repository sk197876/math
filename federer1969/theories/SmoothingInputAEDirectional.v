(** Federer (1969), 4.1.2, p. 347: the original input
    derivative commutes with convolution when a bounded almost-everywhere
    derivative field is available. The reflexive existence theorem supplies
    that field; actual quotient integrals and scalar dominated convergence
    identify the already existing derivative of the smooth convolution. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormClassOneUP NormRegularity
  NormDifferentialDirectional NormedCurveDerivativeUP VectorDaniellHypotheses
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanLebesgueDimensions
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurePushforward
  MeasureIntegralUP SummableRealFunctionUP SummableRealArithmetic MeasureVectorIntegralUP
  SmoothingConvolutionUP SmoothingConvolutionSubstitution EuclideanReflectionTranslation
  SmoothingInputQuotientIntegral PuncturedNormReciprocalSequence TotalVectorDominatedLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothingInputAEDirectional.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hSep:is_separable_normed_space hNY.
Local Notation TY := (real_norm_metric_space hNY).
Variable psi:X->R.
Hypothesis hNonnegative:forall z,0<=psi z.
Hypothesis hMass:is_measure_integral mu (real_total_integrand psi) (1:R)%:E.
Variables f xi g q:X->Y.
Variable v a:X.
Variable M:R.
Hypothesis hQuotientBound:forall m:nat,forall z:X,psi z!=0 ->
  NY ((((m.+1)%:R:R)^-1)^-1*:(f ((a-z)+(((m.+1)%:R:R)^-1)*:v)-f (a-z)))<=M.
Hypothesis hXiBound:forall z:X,psi z!=0 ->NY (xi (a-z))<=M.
Hypothesis hXiAE:measure_almost_everywhere mu [set z|punctured_norm_limit NY
  (fun t=>t^-1*:(f (z+t*:v)-f z)) (xi z)].
Hypothesis hConv:is_smoothing_convolution hNY psi f g.
Hypothesis hConvXi:is_smoothing_convolution hNY psi xi q.
Hypothesis hGClass:norm_class hN hNY (fun _=>True) g 1%N.

(** Source for [smoothing_input_ae_directional_derivative]: the original
    D_j(Phi*f)=Phi*D_j f under the proved compact quotient bound of
    Federer 4.1.2, p. 347. The derivative representative is
    arbitrary subject to its actual original conull derivative law.
    One compact bound suffices for the kernel-weighted quotients;
    the complete reflexive/local wrapper supplies these premises. *)
Theorem smoothing_input_ae_directional_derivative:
  punctured_norm_limit NY (fun t=>t^-1*:(g (a+t*:v)-g a)) (q a).
Proof.
pose eps:=fun m:nat=>((m.+1)%:R:R)^-1.
pose F m z:=psi z*:((eps m)^-1*:(f ((a-z)+eps m*:v)-f (a-z))).
pose G z:=psi z*:xi (a-z).
pose u m:=((eps m)^-1*:(g (a+eps m*:v)-g a):TY).
have hFI m:is_measure_vector_integral mu
    (partial_function_total (fun z=>(F m z:TY))) (u m).
  exact:(@smoothing_input_quotient_integral R n Y NY hNY hSep f g psi hConv a v (eps m)).
have hGI:=@smoothing_convolution_alternate_integral R n Y NY hNY psi xi q hSep hConvXi a.
pose H z:=(2*M)*psi z.
have hHI:is_measure_integral mu (real_total_integrand H) (2*M)%:E.
  have h:=@real_total_integral_scale R X mu hm psi 1 (2*M) hMass.
  by rewrite mulr1 in h.
have hDom m z:NY (F m z-G z)<=H z.
  case:(eqVneq (psi z) 0)=>[hZero|hNonzero].
  - by rewrite /F /G /H hZero !scale0r mulr0 subrr (real_seminorm_zero hNY.1).
  rewrite /F /G -scalerBr (real_seminorm_scale hNY.1)
    (ger0_norm (hNonnegative z)).
  have hOne:=@hQuotientBound m z hNonzero.
  have hTwo:=@hXiBound z hNonzero.
  have hTriangle:=real_seminorm_triangle hNY.1
    ((eps m)^-1*:(f ((a-z)+eps m*:v)-f (a-z))) (-xi (a-z)).
  rewrite (real_seminorm_negate hNY.1) in hTriangle.
  have hUpper:NY ((eps m)^-1*:(f ((a-z)+eps m*:v)-f (a-z))-xi (a-z))<=2*M.
    have hSum:=le_trans hTriangle (lerD hOne hTwo).
    by rewrite mulr_natl mulr2n; exact hSum.
  have hEqual:H z=psi z*(2*M) by rewrite /H mulrC.
  rewrite hEqual.
  have hWeighted:=ler_wpM2l (hNonnegative z) hUpper.
  exact hWeighted.
have hPull:measure_almost_everywhere mu [set z|punctured_norm_limit NY
    (fun t=>t^-1*:(f ((a-z)+t*:v)-f (a-z))) (xi (a-z))].
  have h:measure_almost_everywhere
      (measure_pushforward (fun z:X=>a-z) mu)
      [set z|punctured_norm_limit NY (fun t=>t^-1*:(f (z+t*:v)-f z)) (xi z)].
    by rewrite euclidean_reflection_translation_measure.
  exact h.
have hPoint:measure_almost_everywhere mu [set z|forall eta:R,0<eta ->
    exists M:nat,forall m,(M<=m)%N ->NY (F m z-G z)<eta].
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hPull).
  move=>z hz eta hEta.
  case:(eqVneq (psi z) 0)=>[hZero|hNonzero].
  - exists 0%N=>m _; by rewrite /F /G hZero !scale0r subrr (real_seminorm_zero hNY.1).
  - have hPositive:0<psi z by rewrite lt_neqAle eq_sym hNonzero (hNonnegative z).
    have hTol:0<eta/psi z by rewrite divr_gt0.
    have hSeq:=@punctured_norm_reciprocal_sequence R Y NY hNY
      (fun t=>t^-1*:(f ((a-z)+t*:v)-f (a-z))) (xi (a-z)) hz.
    have hNear : \forall m \near \oo,ball (xi (a-z):TY) (eta/psi z)
        ((eps m)^-1*:(f ((a-z)+eps m*:v)-f (a-z)):TY).
      exact:((cvg_ballP _ _).1 hSeq (eta/psi z) hTol).
    have[N0 _ hN0]:=hNear.
    exists N0=>m hmN.
    have hSmall:=hN0 m hmN.
    rewrite ballEmdist in hSmall.
    change (is_true (NY (xi (a-z)-(eps m)^-1*:(f ((a-z)+eps m*:v)-f (a-z)))<eta/psi z)) in hSmall.
    rewrite (real_seminorm_subtract hNY.1) in hSmall.
    rewrite /F /G -scalerBr (real_seminorm_scale hNY.1) (ger0_norm (ltW hPositive)).
    have hCancel:psi z*(eta/psi z)=eta by rewrite mulrC divfK // gt_eqF.
    have hProduct:psi z*NY ((eps m)^-1*:(f ((a-z)+eps m*:v)-f (a-z))-xi (a-z))<psi z*(eta/psi z).
      by rewrite (ltr_pM2l hPositive).
    by rewrite hCancel in hProduct.
have hIntegralLimit:=@total_vector_integral_dominated_limit R X Y NY hNY mu hm
  F G u (q a) H hFI hGI (ex_intro _ (2*M) hHI) hDom hPoint.
have hSeqQ:u @ \oo --> (q a:TY).
  move=>V hV.
  have[eta hEta hBall]:=(metricType_numDomainType.nbhs_mdistP (q a:TY) V).1 hV.
  have[K0 hK0]:=hIntegralLimit eta hEta.
  exists K0; first exact Logic.I.
  move=>m hmK; apply:hBall.
  change (is_true (NY (q a-u m)<eta)).
  rewrite (real_seminorm_subtract hNY.1); exact:hK0 m hmK.
have[D hD]:=(norm_class_firstP hN hNY (fun _=>True) g).1 hGClass.
have hDiff:=@norm_differential_directional_limit R X Y N NY hN hNY
  (fun _=>True) g a (D a) (norm_class_one_differential hD Logic.I) v.
have hSeqD:=@punctured_norm_reciprocal_sequence R Y NY hNY
  (fun t=>t^-1*:(g (a+t*:v)-g a)) (D a v) hDiff.
have PF0:ProperFilter (\oo:set_system nat) by typeclasses eauto.
have PF:ProperFilter (u @ \oo):=fmap_proper_filter u PF0.
have hEqual:=@cvg_unique TY (@metric_hausdorff R TY) _ PF (D a v) (q a) hSeqD hSeqQ.
by rewrite -hEqual.
Qed.
End SmoothingInputAEDirectional.
