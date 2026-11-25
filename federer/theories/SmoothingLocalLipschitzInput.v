(** Federer (1969), 4.1.2, p. 347: input derivatives
    commute with smoothing for the actual locally Lipschitz field.
    The derivative representative preserves the original partial graph.
    One compact quotient bound discharges the dominated integral
    theorem; no global Lipschitz bound on the input is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  NormedCurveDerivativeUP NormRegularity NormClassZeroWhole LipschitzUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothCompactSet MetricClosedBalls EuclideanNormClosedBalls EuclideanLebesgueDimensions
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationIntegral SmoothingDilationNonzeroRadius
  SmoothingConvolutionUP CompactSmoothConvolutionSmoothness ContinuousFieldLocalIntegrability
  MetricLocalLipschitzContinuity NormCompactLipschitzDirectionalBound EuclideanReflectionTranslation
  MeasureAlmostUP SmoothingInputAEDirectional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothingLocalLipschitzInput.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable e:R.
Hypothesis he:0<e.
Variables f xi g q:X->Y.
Hypothesis hLocal:is_locally_metric_lipschitz setT
  (f:real_norm_metric_space hN->real_norm_metric_space hNY).
Variable v:X.
Hypothesis hRep:forall x w,punctured_norm_limit NY
  (fun t=>t^-1*:(f (x+t*:v)-f x)) w ->xi x=w.
Hypothesis hZero:forall x,~(exists w,punctured_norm_limit NY
  (fun t=>t^-1*:(f (x+t*:v)-f x)) w) ->xi x=0.
Hypothesis hXiAE:measure_almost_everywhere (@euclidean_lebesgue_measure R n)
  [set z|punctured_norm_limit NY (fun t=>t^-1*:(f (z+t*:v)-f z)) (xi z)].
Hypothesis hConv:is_smoothing_convolution hNY (family e) f g.
Hypothesis hConvXi:is_smoothing_convolution hNY (family e) xi q.

(** Source for [smoothing_local_lipschitz_input_derivative]: the
    original commutation D_j(Phi_epsilon*f)=Phi_epsilon*D_j f
    under the full local Lipschitz hypothesis, Federer 4.1.2,
    p. 347. Reflexivity is used only to supply the actual
    derivative field in the complete existence theorem. *)
Theorem smoothing_local_lipschitz_input_derivative a:
  punctured_norm_limit NY (fun t=>t^-1*:(g (a+t*:v)-g a)) (q a).
Proof.
pose mu:=@euclidean_lebesgue_measure R n.
have hContinuous:=metric_local_lipschitz_continuous_whole hLocal.
have hField:=@continuous_field_locally_norm_integrable R n Y NY hNY f
  (norm_continuous_whole_class_zero hContinuous).
have hPsi:=@smoothing_dilation_smooth R n phi hPhi family hFamily e he.
have hOff:=@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he.
have hG:=@compact_smooth_convolution_class R n Y NY hNY hY hSep f hField 1%N
  (family e) e g hPsi hOff hConv.
pose K:=@Build_smooth_compact_set R X N hN (fun _=>True)
  (@metric_closed_ball R (real_norm_metric_space hN) a e)
  (fun _ _=>Logic.I) (@euclidean_norm_closed_ball_compact R n a e).
have[M [hM [hQB hDB]]]:=@norm_compact_lipschitz_directional_bound R n Y NY hNY f v hLocal K.
have hBase z:family e z!=0 ->smooth_compact_carrier K (a-z).
  move=>hz.
  have hRadius:=@smoothing_dilation_nonzero_radius R n phi family hPhi hFamily e he z hz.
  change (is_true (N (a-(a-z))<=e)).
  rewrite (@euclidean_reflection_translation_involutive R n a z); exact:ltW hRadius.
have hQuotient m z:family e z!=0 ->
    NY ((((m.+1)%:R:R)^-1)^-1*:(f ((a-z)+(((m.+1)%:R:R)^-1)*:v)-f (a-z)))<=M.
  move=>hz.
  have hPos:0<((m.+1)%:R:R) by rewrite ltr0n.
  have hInvPos:0<((m.+1)%:R:R)^-1 by rewrite invr_gt0.
  have hUnit:((m.+1)%:R:R)^-1<=1.
    by rewrite (invf_le1 hPos) ler1n.
  apply:(@hQB (a-z) (@hBase z hz) (((m.+1)%:R:R)^-1) (lt0r_neq0 hInvPos)).
  by rewrite (ger0_norm (ltW hInvPos)).
have hXiBound z:family e z!=0 ->NY (xi (a-z))<=M.
  move=>hz.
  case:(pselect (exists w,punctured_norm_limit NY
    (fun t=>t^-1*:(f ((a-z)+t*:v)-f (a-z))) w))=>[[w hw]|hn].
  - rewrite (@hRep (a-z) w hw); exact:(@hDB (a-z) (@hBase z hz) w hw).
  - by rewrite (@hZero (a-z) hn) (real_seminorm_zero hNY.1).
exact:(@smoothing_input_ae_directional_derivative R n Y NY hNY hSep (family e)
  (@smoothing_dilation_nonnegative R n phi hPhi family hFamily e he)
  (@smoothing_dilation_integral_one R n phi family hPhi hFamily e he)
  f xi g q v a M hQuotient hXiBound hXiAE hConv hConvXi hG).
Qed.
End SmoothingLocalLipschitzInput.
