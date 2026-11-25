(** Federer (1969), 4.1.2, p. 347: convolution
    by the original smoothing family converges at
    every Lebesgue point of the field. The exact
    mean limit and the original epsilon^-n ball
    estimate prove the result in every source dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring.
From Federer Require Import RealNormUP NormMetric VectorDaniellHypotheses GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness MetricClosedBalls CenteredBallRelations NoncenteredBallRelations EuclideanClosedBallGrowth
  EuclideanLebesgueDimensions PartialFunctionBasic MeasureLebesgueSet LocallyIntegrableVectorFieldUP
  SmoothingKernelUP SmoothingDilationUP SmoothingKernelScalarBound SmoothingConvolutionUP
  EuclideanLocalDistanceMeans SmoothingLebesgueErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothingAtLebesguePoints.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T := (real_norm_metric_space hN).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation C := (@euclidean_closed_unit_volume R n).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hSep:is_separable_normed_space hNY.
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable f:X->Y.
Hypothesis hField:@is_locally_integrable_vector_field R X Y N NY hN hNY mu f.
Variable g:R->X->Y.
Hypothesis hConvolution:forall e:R,0<e ->is_smoothing_convolution hNY (family e) f (g e).

(** Source for [smoothing_at_lebesgue_point]: the original
    pointwise convergence assertion in Federer 4.1.2,
    p. 347. Every supplied original Lebesgue
    point is retained, with the exact norm
    error and positive-scale limit. *)
Theorem smoothing_at_lebesgue_point (V:T->set T->Prop) (a:T):
  (forall r:R,0<r ->V a (metric_closed_ball a r)) ->
  @measure_lebesgue_set R [the metricType R of T] [the metricType R of real_norm_metric_space hNY] mu V (partial_function_total (fun z=>(f z:real_norm_metric_space hNY))) a ->
  forall eta:R,0<eta ->exists d:R,0<d /\ forall e:R,0<e ->e<d ->
    NY (g e a-f a)<eta.
Proof.
move=>hBalls hLebesgue eta hEta.
have [M [hM hBound]]:=@smoothing_kernel_absolute_bound R n phi hPhi.
have hC:0<C:=(@euclidean_closed_unit_volume_laws R n).2.
have hMC:0<M*C:=mulr_gt0 hM hC.
have hScaledEta:0<eta/(M*C) by rewrite divr_gt0.
have [d [hd hMeans]]:=@euclidean_lebesgue_point_ball_mean_small R n Y NY hNY f hField
  V a hBalls hLebesgue (eta/(M*C)) hScaledEta.
exists d; split=>// e he hSmall.
have [J [hJ hMean]]:=hMeans e he hSmall.
have hError:=@smoothing_lebesgue_error_bound R n Y NY hNY hSep phi hPhi family hFamily
  f (g e) e a M J he hBound (@hConvolution e he) hJ.
have hIdentity:M/(e^+n)*J=(M*C)*(J/(C*e^+n)).
  transitivity ((M*J)*(C*C^-1)*(e^+n)^-1).
  - rewrite (mulfV (lt0r_neq0 hC)) mulr1; ring.
  - rewrite invfM; ring.
apply:le_lt_trans hError _.
rewrite hIdentity.
have hLess:(M*C)*(J/(C*e^+n))<(M*C)*(eta/(M*C)).
  by rewrite (ltr_pM2l hMC).
have hEnd:(M*C)*(eta/(M*C))=eta by rewrite mulrC divfK // gt_eqF.
by rewrite hEnd in hLess.
Qed.

(** Source for [smoothing_at_centered_lebesgue_point]: the original
    smoothing conclusion for the centered-ball Lebesgue set,
    Federer 4.1.2, p. 347, using the
    ball relation of 2.8.18, p. 152. *)
Corollary smoothing_at_centered_lebesgue_point (a:T):
  @measure_lebesgue_set R [the metricType R of T] [the metricType R of real_norm_metric_space hNY] mu (@centered_closed_ball_relation R [the metricType R of T])
    (partial_function_total (fun z=>(f z:real_norm_metric_space hNY))) a ->
  forall eta:R,0<eta ->exists d:R,0<d /\ forall e:R,0<e ->e<d ->
    NY (g e a-f a)<eta.
Proof.
apply:smoothing_at_lebesgue_point=>r hr; exists r; by split.
Qed.

(** Source for [smoothing_at_containing_ball_lebesgue_point]: the original
    smoothing conclusion also retains the containing-ball Lebesgue set
    of 2.9.9, pp. 156–157, as invoked
    in Federer 4.1.2, p. 347. *)
Corollary smoothing_at_containing_ball_lebesgue_point (a:T):
  @measure_lebesgue_set R [the metricType R of T] [the metricType R of real_norm_metric_space hNY] mu (@noncentered_closed_ball_relation R [the metricType R of T])
    (partial_function_total (fun z=>(f z:real_norm_metric_space hNY))) a ->
  forall eta:R,0<eta ->exists d:R,0<d /\ forall e:R,0<e ->e<d ->
    NY (g e a-f a)<eta.
Proof.
apply:smoothing_at_lebesgue_point=>r hr.
apply:centered_closed_balls_subrelation; exists r; by split.
Qed.
End SmoothingAtLebesguePoints.
