(** Federer (1969), 4.1.24, p. 381: a
    Lipschitz image of an original zero-simplex is
    the point current at its image. Reuse the
    preceding support agreement from 4.1.15 and the
    smooth Dirac image from 4.1.7. Source and
    target dimensions are arbitrary, including zero. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormRegularityOperations InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP LipschitzBasic
  CurrentSpaces CurrentDirac DiracCurrentBounds CurrentPushforwardDirac
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzSupportAgreement
  CurrentFlatSmoothPushforward FlatCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_flat_lipschitz_dirac_pushforward]:
    f#delta_x=delta_f(x), the zero-simplex image
    used in R_0=P-script_0, 4.1.24, p. 381.
    Every supplied flat-membership witness gives the
    same actual value. No global affine or
    smooth hypothesis is imposed on the original f. *)
Theorem current_flat_lipschitz_dirac_pushforward (R:realType)
    (h2:(1+1:R)!=0) d n
    (Z:set (R_n R d)) (U:set (R_n R n))
    (hZ:forall x,Z x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R d)) Z x)
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (f:R_n R d->R_n R n) (hImage:forall x,Z x->U (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) Z f)
    (c:R_n R d) (hc:Z c)
    (hFlat:@is_flat_current R h2 d 0%N Z hZ (@dirac_current R h2 d Z hZ c)):
  @CurrentFlatLipschitzPushforward.value R h2 d n 0%N Z U hZ hU
    f hImage hLocal (@dirac_current R h2 d Z hZ c) hFlat=
    @dirac_current R h2 n U hU (f c).
Proof.
pose X:=R_n R d;pose Y:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R d).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R d).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose g:=fun _:X=>f c.
pose hGImage:=fun (x:X) (_:Z x)=>@hImage c hc.
have hGLip:@is_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) Z g.
  exact:(@metric_lipschitz_of_bound R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) Z g 0
    (least_metric_lipschitz_bound (@metric_lipschitz_constant_map R
      (real_norm_metric_space hNX) (real_norm_metric_space hNY) Z (f c)))).
pose hGLocal:=@metric_lipschitz_is_local R (real_norm_metric_space hNX)
  (real_norm_metric_space hNY) Z g hGLip.
pose hSmooth:=fun k=>@norm_class_constant R X Y NX NY hNX hNY Z (f c) k hZ.
have hAgreement:forall x,@current_support R h2 d Z hZ 0%N
    (@dirac_current R h2 d Z hZ c) x->f x=g x.
  move=>x hx;have hxc: x=c:=@dirac_current_support_subset R h2 d Z hZ c hc x hx.
  by rewrite hxc.
rewrite (@current_flat_lipschitz_support_agreement
  R h2 d n 0%N Z U hZ hU f g hImage hGImage hLocal hGLocal
  (@dirac_current R h2 d Z hZ c) hFlat hAgreement).
pose hProper:=@current_point_support_proper R h2 d n Z U hZ c hc g hGImage.
rewrite (@current_flat_lipschitz_pushforward_smooth
  R h2 d n 0%N Z U hZ hU g hGImage hGLocal
  (@dirac_current R h2 d Z hZ c) hFlat hSmooth hProper).
exact:(@current_pushforward_dirac R h2 d n Z U hZ hU c hc g hGImage hSmooth).
Qed.
