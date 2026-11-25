(** Federer (1969), 4.1.15, p. 372: two
    locally Lipschitz maps equal on sptT give equal
    actual flat images. The preceding radial smoothing supplies
    genuine comparison families; the universal approximation law
    then identifies the two image currents. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentSpaces CurrentSupportGeometry FlatCurrentsUP FlatCurrentFinite
  CurrentFlatLipschitzPushforwardSealed CurrentSupportSmoothComparisonUP
  CurrentSupportSmoothComparisonExistence CurrentSupportSmoothComparisonImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_flat_lipschitz_support_agreement]:
    f restricted to sptT equals g restricted to sptT
    implies f#T=g#T for every original flat T,
    Federer 4.1.15, p. 372. No equality on K,
    fixed source neighbourhood, normality or finite mass
    is an additional hypothesis. *)
Theorem current_flat_lipschitz_support_agreement (R:realType)
    (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f g:R_n R n->R_n R nu)
    (hFImage:forall x,U x->V (f x))
    (hGImage:forall x,U x->V (g x))
    (hFLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (hGLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U g)
    (T:@current_space R h2 n U hU m)
    (hFlat:@is_flat_current R h2 n m U hU T)
    (hAgree:forall x,@current_support R h2 n U hU m T x->f x=g x):
  @CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
    f hFImage hFLocal T hFlat=
  @CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
    g hGImage hGLocal T hFlat.
Proof.
have[K hK]:=hFlat.
have hSupport:=@flat_current_supported_support R h2 n m U hU K T hK.
have[Z [a [b hComparison]]]:=@current_support_smooth_comparison_exists R n nu
  U V hU hV K f g hFImage hGImage hFLocal hGLocal
  (@current_support R h2 n U hU m T) hSupport hAgree.
exact:(@current_support_smooth_comparison_images R h2 n nu m U V hU hV
  f g hFImage hGImage hFLocal hGLocal K T hK hFlat Z a b hComparison).
Qed.

Arguments current_flat_lipschitz_support_agreement : clear implicits.
