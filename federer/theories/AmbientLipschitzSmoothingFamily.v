(** Federer (1969), 4.1.15, p. 372: smooth the
    original f and radius-dependent G_r with the same
    normalized kernel. The preceding 4.1.2 convolution,
    regularity and Lipschitz estimates give actual smooth
    families with one common differential control. This
    existence adapter allows the unsmoothed input to vary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormRegularity NormClassOneUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric LipschitzUP LipschitzBasic EuclideanLipschitzClassZero
  EuclideanOwnNormCompleteness SmoothingKernelSealed SmoothingDilationSealed
  SmoothingDilationSmooth SmoothingDilationNonzeroRadius SmoothingConvolutionUP
  ContinuousCompactConvolution ContinuousSmoothingSmoothness
  SmoothingLipschitzBound SmoothingLipschitzError.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AmbientLipschitzSmoothingFamily.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation phi:=(@SmoothingKernel.value R n).
Local Notation hPhi:=(@SmoothingKernel.laws R n).
Local Notation family:=(@SmoothingDilation.value R n phi).
Local Notation hFamily:=(@SmoothingDilation.laws R n phi).
Variable F:nat->X->Y.
Variable L:R.
Hypothesis hL:0<=L.
Hypothesis hBound:forall i x y,NY (F i x-F i y)<=L*NX (x-y).
Variable epsilon:nat->R.
Hypothesis hEpsilon:forall i,0<epsilon i.

(** Source for [ambient_lipschitz_smoothing_family_exists]:
    the two actual smoothing families in Federer 4.1.15,
    p. 372, exist with the original common kernel.
    Each term is smooth, retains the input Lipschitz
    bound and differs from that input by at most
    L epsilon_i. Empty sources are never filled by
    a point from the original target open set. *)
Theorem ambient_lipschitz_smoothing_family_exists:
  exists a:nat->X->Y,
    (forall i,is_smoothing_convolution hNY (family (epsilon i)) (F i) (a i)) /\
    (forall i,norm_class_all_orders hNX hNY setT (a i)) /\
    (forall i x y,NY (a i x-a i y)<=L*NX (x-y)) /\
    forall i x,NY (a i x-F i x)<=L*epsilon i.
Proof.
have hContinuous i:norm_class_zero NX NY setT (F i).
  apply:(@euclidean_lipschitz_norm_class_zero R n nu (F i)).
  apply:metric_lipschitz_of_bound.
  split;first exact:hL.
  move=>x y _ _.
  change (is_true (NY (F i x-F i y)<=L*NX (x-y))).
  exact:(@hBound i x y).
have hExists i:exists ai:X->Y,
    is_smoothing_convolution hNY (family (epsilon i)) (F i) ai.
  exact:(@continuous_compact_convolution_exists R n Y NY hNY
    (@euclidean_own_norm_complete R nu) (F i) (hContinuous i) (family (epsilon i))
    (@smoothing_dilation_smooth R n phi hPhi family hFamily (epsilon i) (@hEpsilon i))
    (epsilon i) (@smoothing_dilation_zero_beyond_radius R n phi family
      hPhi hFamily (epsilon i) (@hEpsilon i))).
have[a hConvolution]:=choice hExists.
exists a;split;first exact:hConvolution.
split.
- move=>i.
  exact:(@continuous_smooth_convolution_smooth R n Y NY hNY
    (@euclidean_own_norm_complete R nu) (F i) (hContinuous i)
    (family (epsilon i)) (epsilon i) (a i)
    (@smoothing_dilation_smooth R n phi hPhi family hFamily (epsilon i) (@hEpsilon i))
    (@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily
      (epsilon i) (@hEpsilon i)) (@hConvolution i)).
- split.
  + move=>i;exact:(@smoothing_lipschitz_bound R n Y NY hNY phi hPhi family hFamily
      (epsilon i) (F i) (a i) L (@hEpsilon i) (@hConvolution i) (@hBound i)).
  + move=>i;exact:(@smoothing_lipschitz_error_bound R n Y NY hNY
      (@euclidean_own_norm_complete R nu) phi hPhi family hFamily
      (epsilon i) (F i) (a i) L (@hEpsilon i) hL (@hConvolution i) (@hBound i)).
Qed.
End AmbientLipschitzSmoothingFamily.
