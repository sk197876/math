(** Federer (1969), 4.1.2, p. 347: the
    directional derivative of convolution is the convolution
    with the corresponding kernel derivative. The compact
    quotient estimate of 4.1.1 supplies the limit;
    the integral error is bounded on one compact ball. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormedCurveDerivativeUP
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness FiniteNormEquivalence
  SmoothCompactSet NormCompactDirectionalQuotient MeasureUP MeasureVectorIntegralUP EuclideanLebesgueDimensions
  LocallyIntegrableVectorFieldUP SmoothingConvolutionUP CompactKernelSourceBall
  TotalVectorIntegralArithmetic WeightedVectorIntegralError.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ConvolutionDirectionalDerivative.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variables f g q:X->Y.
Variables psi theta:X->R.
Variable r:R.
Hypothesis hField:@is_locally_integrable_vector_field R X Y N NY hN hNY
  (@euclidean_lebesgue_measure R n) f.
Hypothesis hPsi:norm_class_all_orders hN hR (fun _=>True) psi.
Hypothesis hPsiOff:forall z,r<N z ->psi z=0.
Hypothesis hThetaOff:forall z,r<N z ->theta z=0.
Hypothesis hConv:is_smoothing_convolution hNY psi f g.
Hypothesis hConvDerivative:is_smoothing_convolution hNY theta f q.
Variable v:X.
Variable D:X->Hom X R^o.
Hypothesis hD:forall z,has_norm_differential N (fun t:R^o=>`|t|) (fun _=>True) psi z (D z).
Hypothesis hTheta:forall z,D z v=theta z.

(** Source for [compact_smooth_convolution_directional_derivative]: the
    original kernel derivative formula of Federer 4.1.2,
    p. 347. Standard coordinate directions give
    D_j(Phi*f)=(D_j Phi)*f. The zero
    direction and the zero-dimensional source are included. *)
Theorem compact_smooth_convolution_directional_derivative a:
  punctured_norm_limit NY (fun t=>t^-1*:(g (a+t*:v)-g a)) (q a).
Proof.
move=>e he.
pose K:=@Build_smooth_compact_set R X N hN (fun _=>True)
  [set z|N (z-a)<=r+1] (fun _ _=>Logic.I)
  (@finite_norm_closed_ball_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN a (r+1)).
have [b hLocal]:=@locally_integrable_vector_compact_norm R X Y N NY hN hNY
  (@euclidean_lebesgue_measure R n) f hField K.
pose c:=e/(`|b|+1).
have hDen:0<`|b|+1 by have:=normr_ge0 b; lra.
have hc:0<c by rewrite /c divr_gt0.
have hcValue:c*(`|b|+1)=e by rewrite /c divfK // gt_eqF.
pose L:=[set w:X|N (w-0)<=r+1].
have hL:@compact (real_norm_metric_space hN) L.
  exact:(@finite_norm_closed_ball_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN 0 (r+1)).
have [d [hd hQuotient]]:=@norm_compact_directional_quotient R X R^o N (fun t:R^o=>`|t|)
  hN hR (fun _=>True) L psi (hPsi 1%N) hL (fun _ _=>Logic.I) v c hc.
have hNv:=real_seminorm_nonnegative hN.1 v.
have hNv1:0<N v+1 by lra.
pose delta:=Num.min d (1/(N v+1)).
have hDelta:0<delta by rewrite /delta lt_min hd divr_gt0 //.
exists delta; split=>// t /andP [ht hSmall].
have hTd:`|t|<d.
  apply:(lt_le_trans hSmall); by rewrite /delta ge_min lexx.
have hTOne:`|t|<1/(N v+1).
  apply:(lt_le_trans hSmall); by rewrite /delta ge_min lexx orbT.
have hProduct:`|t|*(N v+1)<1 by move:hTOne; rewrite ltr_pdivlMr.
have hIncrement:N (t*:v)<1.
  rewrite (real_seminorm_scale hN.1).
  apply:le_lt_trans _ hProduct; by rewrite ler_wpM2l // lerDl.
have hDifference:=@total_vector_integral_subtract R X Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (fun z=>psi (a+t*:v-z)*:f z) (fun z=>psi (a-z)*:f z)
  (g (a+t*:v)) (g a) (hConv (a+t*:v)) (hConv a).
have hScaled:=@total_vector_integral_scale R X Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (fun z=>psi (a+t*:v-z)*:f z-psi (a-z)*:f z) (g (a+t*:v)-g a) t^-1 hDifference.
have hIntegrand:(fun z:X=>(t^-1*:(psi (a+t*:v-z)*:f z-psi (a-z)*:f z):real_norm_metric_space hNY))=
    (fun z=>(t^-1*(psi (a+t*:v-z)-psi (a-z))*:f z:real_norm_metric_space hNY)).
  apply:funext=>z; by rewrite -scalerBl scalerA.
rewrite hIntegrand in hScaled.
have hError:=@weighted_vector_integral_difference_bound R X Y NY hNY
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (smooth_compact_carrier K) f
  (fun z=>t^-1*(psi (a+t*:v-z)-psi (a-z))) (fun z=>theta (a-z))
  (t^-1*:(g (a+t*:v)-g a)) (q a) b c hLocal hScaled (hConvDerivative a).
have hBound z:smooth_compact_carrier K z ->
    `|t^-1*(psi (a+t*:v-z)-psi (a-z))-theta (a-z)|<=c.
  move=>hz.
  have hBase:L (a-z).
    change (is_true (N (a-z-0)<=r+1)).
    rewrite subr0 (real_seminorm_subtract hN.1 a z); exact hz.
  have hTd':0<`|t|<d by apply/andP; split.
  have hPoint:=hQuotient (a-z) hBase t hTd' (D (a-z)) (hD (a-z)).
  have hShift:a+t*:v-z=(a-z)+t*:v by rewrite addrAC.
  change (is_true (`|t^-1*(psi ((a-z)+t*:v)-psi (a-z))-D (a-z) v|<c)) in hPoint.
  rewrite hShift -hTheta; exact:ltW hPoint.
have hZero z:~smooth_compact_carrier K z ->
    t^-1*(psi (a+t*:v-z)-psi (a-z))=0 /\ theta (a-z)=0.
  move=>hz.
  have hOutside:r+1<N (z-a).
    rewrite ltNge; apply/negP=>hNear; exact:hz hNear.
  have [hFirst hNext]:=@norm_kernel_source_ball_shift R X N hN a (t*:v) z r hIncrement hOutside.
  split.
  - by rewrite (@hPsiOff _ hNext) (@hPsiOff _ hFirst) subrr mulr0.
  - exact:(@hThetaOff _ hFirst).
have hFinal:=hError hBound hZero.
apply:le_lt_trans hFinal _.
have hb:b<=`|b| := ler_norm b.
nra.
Qed.
End ConvolutionDirectionalDerivative.
