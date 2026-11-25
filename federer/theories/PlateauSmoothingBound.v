(** Federer (1969), 4.1.5, p. 350: the
    smoothed removed tail has norm at most eta g.
    The original compact support has a uniform collar
    in the plateau where g is one, so the actual
    convolution vanishes elsewhere. The positive
    normalized kernel preserves the uniform eta bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  MetricOpenThickening MetricCompactNeighbourhood SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP
  CompactSmoothingSupport SmoothingUniformNormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PlateauSmoothingBound.
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

(** Source for [plateau_smoothing_pointwise_bound]:
    the second original convolution inequality of
    Federer 4.1.5, p. 350, for the actual
    removed tail and the chosen compact plateau g. *)
Theorem plateau_smoothing_pointwise_bound (K W:set XT) (g:X->R)
    (u:X->Y) (P:R->X->Y) eta r:
  compact K ->open W ->K `<=` W ->
  (forall x,0<=g x) ->(forall x,W x ->g x= 1) ->
  0<=eta ->0<r ->
  (forall x,~K x ->u x=0) ->(forall x,NY (u x)<=eta) ->
  (forall e:R,0<e ->e<r ->is_smoothing_convolution hNY (family e) u (P e)) ->
  exists d:R,0<d /\ d<=r /\
    forall e:R,0<e ->e<d ->forall x,NY (P e x)<=eta*g x.
Proof.
move=>hK hW hKW hG hOne hEta hr hOff hBound hConvolution.
have[a [ha hCollar]]:=@compact_metric_open_thickening R XT K W hK hW hKW.
have hHalf:0<a/2 by rewrite divr_gt0 // ltr0n.
have hThick:forall x z,K z ->N (x-z)<=a/2 ->W x.
  move=>x z hz hDist; apply:hCollar; exists z; first exact hz.
  change (is_true (N (z-x)<a)); rewrite (real_seminorm_subtract hN.1); lra.
exists (Num.min r (a/2)); split; first by rewrite lt_min hr hHalf.
split; first by rewrite ge_min lexx.
move=>e he hSmall x.
have /andP [her hea]:(e<r)&&(e<a/2) by rewrite -lt_min.
case:(pselect (W x))=>hx.
- rewrite (hOne x hx) mulr1.
  exact:(@smoothing_uniform_norm_bound R n Y NY hNY phi hPhi family hFamily e u (P e) eta
    he (hConvolution e he her) hBound x).
- have hZero:=@compact_smoothing_support_bound R n Y NY hNY phi hPhi family hFamily
    K W (a/2) e u (P e) hThick he (ltW hea) hOff (hConvolution e he her) x hx.
  rewrite hZero (real_seminorm_zero hNY.1); exact:mulr_ge0 hEta (hG x).
Qed.
End PlateauSmoothingBound.
