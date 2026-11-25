(** Federer (1969), 4.1.20, p. 378: the rotated and
    projected scalar contractions are flat currents. This
    supporting form of 4.1.14, pp. 370–371, identifies the
    original smooth pushforward with the already specified
    opaque Lipschitz image. Flatness supplies compact support;
    neither finite mass nor normality is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormRegularityOperations NormClassOneUP NormClassOneLocalLipschitz
  NormLocalLipschitzScalarProduct
  LipschitzUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces SmoothCompactSet FlatCurrentsUP FlatCurrentFinite
  CurrentLipschitzCompactImage CurrentCompactPushforwardAlgebra
  CurrentCompactLipschitzPushforwardSealed CurrentCompactLipschitzPushforwardSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_smooth_flat_image]: an actual smooth
    map sends every original compactly supported flat current
    to a flat current, the use of 4.1.14 in Federer 4.1.20,
    p. 378. The actual support-proper smooth pushforward is
    retained, on arbitrary original open source and target sets. *)
Theorem current_smooth_flat_image (R:realType) (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hf:norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T:@current_space R h2 n U hU m)
    (hFlat:@is_flat_current_supported_in R h2 n m U hU K T):
  @is_flat_current R h2 nu m V hV
    (@current_compact_map_pushforward R h2 n nu U V hU hV f hImage hf m T
      (@flat_supported_current_compact R h2 n m U hU K T hFlat)).
Proof.
pose X:=R_n R n;pose Y:=R_n R nu.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R nu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R nu).
have hLocal:@is_locally_metric_lipschitz R
    (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
  apply:(@norm_class_one_locally_metric_lipschitz R X Y NX NY hNX hNY U f).
  apply:((@norm_class_firstP R X Y NX NY hNX hNY U f).1).
  exact:hf 1.
pose E:=@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K.
have hLaws:=@CurrentCompactLipschitzPushforward.laws R h2 n nu m U V hU hV
  f hImage hLocal K T hFlat.
have hSmooth:=@current_compact_lipschitz_pushforward_smooth R h2 n nu m
  U V hU hV f hImage hLocal K T hFlat hf.
rewrite hSmooth in hLaws.
exists E;exact:hLaws.1.
Qed.
