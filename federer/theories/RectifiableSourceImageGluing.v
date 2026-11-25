(** Federer (1969), 4.1.24, p. 380: the
    two original polyhedral source maps admit one
    globally Lipschitz map on disjoint open neighbourhoods
    of their exact tagged compact images. No target
    convexity or extension to the whole target is
    required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP LipschitzBasic MetricLipschitzCompactImage SmoothCompactSet
  EuclideanLinearSourcePullback RectifiableSourceEmbeddings
  CompactLipschitzGluingUP CompactLipschitzGluingExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section RectifiableSourceImageGluing.
Variable R:realType.
Variables d0 d1 n:nat.
Local Notation X0:=(R_n R d0).
Local Notation X1:=(R_n R d1).
Local Notation X:=(R_n R (1+(d0+d1))%N).
Local Notation Y:=(R_n R n).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R (1+(d0+d1))%N)).
Local Notation E0:=(@rectifiable_source_left R d0 d1).
Local Notation E1:=(@rectifiable_source_right R d0 d1).
Local Notation P0:=(@rectifiable_source_left_projection R d0 d1).
Local Notation P1:=(@rectifiable_source_right_projection R d0 d1).
Variables (Z0:set X0) (Z1:set X1) (U:set Y).
Hypothesis hZ0:forall x,Z0 x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R d0)) Z0 x.
Hypothesis hZ1:forall x,Z1 x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R d1)) Z1 x.
Variable C0:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R d0)) Z0.
Variable C1:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R d1)) Z1.
Variables (f0:X0->Y) (f1:X1->Y).
Hypothesis hImage0:forall x,Z0 x->U (f0 x).
Hypothesis hImage1:forall x,Z1 x->U (f1 x).
Hypothesis hLip0:@is_metric_lipschitz R
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d0)))
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) Z0 f0.
Hypothesis hLip1:@is_metric_lipschitz R
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d1)))
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) Z1 f1.
Local Notation O0:=(fun x:X=>Z0 (P0 x)).
Local Notation O1:=(fun x:X=>Z1 (P1 x)).
Local Notation F0:=(fun x:X=>f0 (P0 x)).
Local Notation F1:=(fun x:X=>f1 (P1 x)).

(** Source for [rectifiable_left_source_compact]: the exact
    first tagged compact, with unchanged original source
    membership, supporting 4.1.24, p. 380. This
    merely packages the literal image under the existing
    affine block inclusion. *)
Definition rectifiable_left_source_compact:smooth_compact_set hNX O0.
Proof.
refine (@Build_smooth_compact_set R X
  (inner_norm (@euclidean_inner_productP R (1+(d0+d1))%N)) hNX O0
  (E0 @` smooth_compact_carrier C0) _ _).
- move=>x [y hy <-];rewrite rectifiable_source_left_inverse.
  exact:smooth_compact_in_domain C0 y hy.
- apply:metric_lipschitz_compact_image (smooth_compact_is_compact C0) _.
  have[L [hL hBound]]:=@rectifiable_source_left_lipschitz R d0 d1.
  exists L;split;first exact:hL.
  exact:(@metric_lipschitz_bound_restrict R (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d0)))
    (real_norm_metric_space hNX) setT (smooth_compact_carrier C0) E0 L
    (fun _ _=>Logic.I) hBound).
Defined.

(** Source for [rectifiable_right_source_compact]: the exact
    second tagged compact, 4.1.24, p. 380.
    Its carrier is not enlarged to a hull or
    neighbourhood. *)
Definition rectifiable_right_source_compact:smooth_compact_set hNX O1.
Proof.
refine (@Build_smooth_compact_set R X
  (inner_norm (@euclidean_inner_productP R (1+(d0+d1))%N)) hNX O1
  (E1 @` smooth_compact_carrier C1) _ _).
- move=>x [y hy <-];rewrite rectifiable_source_right_inverse.
  exact:smooth_compact_in_domain C1 y hy.
- apply:metric_lipschitz_compact_image (smooth_compact_is_compact C1) _.
  have[L [hL hBound]]:=@rectifiable_source_right_lipschitz R d0 d1.
  exists L;split;first exact:hL.
  exact:(@metric_lipschitz_bound_restrict R (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d1)))
    (real_norm_metric_space hNX) setT (smooth_compact_carrier C1) E1 L
    (fun _ _=>Logic.I) hBound).
Defined.

(** Source for [rectifiable_sources_image_gluing_exists]: two
    original image maps have a common genuine globally
    Lipschitz source map near both tagged source compacts,
    the geometric step in the original additive assertion
    of 4.1.24, p. 380. The source dimensions
    remain independent and may both be zero. *)
Theorem rectifiable_sources_image_gluing_exists:
  exists W0:set X,exists W1:set X,exists F:X->Y,
    @is_compact_lipschitz_gluing R (1+(d0+d1))%N n O0 O1 U
      rectifiable_left_source_compact rectifiable_right_source_compact F0 F1 W0 W1 F.
Proof.
have[hO0 hF0]:=@euclidean_linear_source_pullback R (1+(d0+d1))%N d0 n
  Z0 hZ0 P0 f0 hLip0.
have[hO1 hF1]:=@euclidean_linear_source_pullback R (1+(d0+d1))%N d1 n
  Z1 hZ1 P1 f1 hLip1.
have hDisjoint:forall x,smooth_compact_carrier rectifiable_left_source_compact x->
    smooth_compact_carrier rectifiable_right_source_compact x->False.
  exact:(@rectifiable_source_images_disjoint R d0 d1
    (smooth_compact_carrier C0) (smooth_compact_carrier C1)).
have hI0:forall x,O0 x->U (F0 x) by move=>x hx;exact:@hImage0 (P0 x) hx.
have hI1:forall x,O1 x->U (F1 x) by move=>x hx;exact:@hImage1 (P1 x) hx.
exact:(@compact_lipschitz_gluing_exists R (1+(d0+d1))%N n O0 O1 U
  hO0 hO1 rectifiable_left_source_compact rectifiable_right_source_compact
  F0 F1 hDisjoint hF0 hF1 hI0 hI1).
Qed.
End RectifiableSourceImageGluing.
