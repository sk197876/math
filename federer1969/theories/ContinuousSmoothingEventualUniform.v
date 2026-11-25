(** Federer (1969), 4.1.2, p. 347,
    used in 4.1.7, p. 358:
    the original compact-uniform convolution
    limit depends only on sufficiently small
    positive radii. This adapter permits the
    actual compact test family on an
    arbitrary open domain, with its original
    upper radius retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP NormClassOneUP SmoothCompactSet
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius
  SmoothingConvolutionUP ContinuousCompactConvolution ContinuousSmoothingLocallyUniform.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ContinuousSmoothingEventualUniform.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable kernel:X->R.
Hypothesis hKernel:is_smoothing_kernel kernel.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation kernel family.
Variables (f:X->Y) (g:R->X->Y).

(** Source for [continuous_smoothing_eventual_uniform]:
    convolution at all sufficiently small
    positive radii converges uniformly on
    each original compact index, supporting
    the class-one approximation in Federer
    4.1.7, p. 358, by 4.1.2,
    p. 347. Values at larger
    radii contribute no hypothesis or conclusion. *)
Theorem continuous_smoothing_eventual_uniform r:
  0<r->norm_class_zero NX NY (fun _=>True) f->
  (forall e,0<e->e<r->is_smoothing_convolution hNY (family e) f (g e))->
  forall K:smooth_compact_set hNX (fun _=>True),forall eta:R,0<eta->
    exists d:R,0<d /\d<=r /\forall e,0<e->e<d->
      forall x,smooth_compact_carrier K x->NY (g e x-f x)<eta.
Proof.
move=>hr hf hConvolution K eta hEta.
have hChoice e:exists q:X->Y,0<e->is_smoothing_convolution hNY (family e) f q.
  case:(pselect (0<e))=>he.
  - have [q hq]:=@continuous_compact_convolution_exists R n Y NY hNY hY f hf
      (family e) (@smoothing_dilation_smooth R n kernel hKernel family hFamily e he) e
      (@smoothing_dilation_zero_beyond_radius R n kernel family hKernel hFamily e he).
    by exists q.
  - exists (fun _=>0)=>h;exact:False_ind _ (he h).
have [q hq]:=choice hChoice.
have [d [hd hUniform]]:=@continuous_smoothing_locally_uniform R n Y NY hNY hY
  kernel hKernel family hFamily f q hq hf K eta hEta.
exists (Num.min d r);split;first by rewrite lt_min hd hr.
split;first by rewrite ge_min lexx orbT.
move=>e he hSmall x hx.
have /andP [hed her]:(e<d)&&(e<r) by rewrite -lt_min.
have hEqual:g e=q e:=smoothing_convolution_unique (hConvolution e he her) (hq e he).
by rewrite hEqual;exact:hUniform e he hed x hx.
Qed.
End ContinuousSmoothingEventualUniform.
