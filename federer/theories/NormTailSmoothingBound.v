(** Federer (1969), 4.1.5, p. 350: the
    smoothed positive-tail field satisfies the original
    sharp pointwise bound ||Phi_e*(h w)||<=||w||.
    The small positive level of the original norm has
    a uniform compact collar. Uniform approximation
    then gives the bound on that collar, and the
    actual convolution vanishes outside it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric RealMetricBackground CountableOrderIntervals
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  FunctionLatticeUP CompactSupportFunctionUP CompactSupportLevels MetricOpenThickening MetricCompactNeighbourhood
  SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP CompactSmoothingSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NormTailSmoothingBound.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hN).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [norm_tail_smoothing_pointwise_bound]:
    the first original convolution inequality of Federer
    4.1.5, p. 350. The positive level set, common
    collar and uniform approximation are proved from
    continuity and compact support of the original majorant. *)
Theorem norm_tail_smoothing_pointwise_bound (f:X->R) eta (u:X->Y) (g:R->X->Y) r:
  @positive_function_lattice R X (@compactly_supported_continuous_functions R XT) f ->
  0<eta ->0<r ->
  (forall x,NY (u x)=Num.max (f x-eta) 0) ->
  (forall e:R,0<e ->e<r ->is_smoothing_convolution hNY (family e) u (g e)) ->
  (forall a:R,0<a ->exists d:R,0<d /\
    forall e:R,0<e ->e<d ->forall x,NY (g e x-u x)<a) ->
  exists d:R,0<d /\ d<=r /\ forall e:R,0<e ->e<d ->forall x,NY (g e x)<=f x.
Proof.
move=>hF hEta hr hTail hConvolution hApprox.
pose K:set XT:=[set x|eta<=f x].
pose V:set XT:=[set x|eta/2<f x].
have hK:compact K:=@compact_support_positive_closed_level_compact R XT f eta hF.1 hEta.
have hV:open V.
  exact:((@continuousP XT (real_line_metric R) f).1 hF.1.1 _
    (@order_strict_upper_ray_open _ [the orderTopologicalType _ of R^o] (eta/2))).
have hKV:K `<=` V.
  move=>x hx; change (is_true (eta<=f x)) in hx.
  change (is_true (eta/2<f x)); lra.
have[a [ha hCollar]]:=@compact_metric_open_thickening R XT K V hK hV hKV.
have hHalfA:0<a/2 by rewrite divr_gt0 // ltr0n.
have hHalfEta:0<eta/2 by rewrite divr_gt0 // ltr0n.
have hThick:forall x z,K z ->N (x-z)<=a/2 ->V x.
  move=>x z hz hDist; apply:hCollar; exists z; first exact hz.
  change (is_true (N (z-x)<a)); rewrite (real_seminorm_subtract hN.1).
  lra.
have hOff:forall x,~K x ->u x=0.
  move=>x hx; apply:hNY.2.
  have hSmall:f x<eta by rewrite ltNge; apply/negP.
  have hNeg:f x-eta<=0 by lra.
  by rewrite hTail (max_r hNeg).
have[b [hb hUniform]]:=hApprox (eta/2) hHalfEta.
exists (Num.min r (Num.min (a/2) b)); split; first by rewrite !lt_min hr hHalfA hb.
split; first by rewrite ge_min lexx.
move=>e he hSmall x.
have /andP [her hRest]:(e<r)&&(e<Num.min (a/2) b) by rewrite -lt_min.
have /andP [hea heb]:(e<a/2)&&(e<b) by rewrite -lt_min.
case:(pselect (V x))=>hx.
- have hX:eta/2<f x:=hx.
  have hError:=hUniform e he heb x.
  have hT:=real_seminorm_triangle hNY.1 (g e x-u x) (u x).
  rewrite subrK hTail in hT.
  case:(leP eta (f x))=>hCase.
  + have hPos:0<=f x-eta by lra.
    rewrite (max_l hPos) in hT; lra.
  + have hNeg:f x-eta<=0 by lra.
    rewrite (max_r hNeg) in hT; lra.
- have hZero:=@compact_smoothing_support_bound R n Y NY hNY phi hPhi family hFamily
    K V (a/2) e u (g e) hThick he (ltW hea) hOff (hConvolution e he her) x hx.
  by rewrite hZero (real_seminorm_zero hNY.1); exact:hF.2 x.
Qed.
End NormTailSmoothingBound.
