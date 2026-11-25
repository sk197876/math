(** Federer (1969), 4.1.11, pp. 365–366: compare compact
    images under the original coordinate maps. These supporting
    laws reuse the preceding support, map agreement and proper
    composition theorems without constructing new currents. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentProperSupport CurrentCompactMapProper CurrentPushforwardSealed
  CurrentPushforwardNormality CurrentPushforwardMapAgreement
  CurrentCompactPushforwardAlgebra SmoothFormPullbackComposition
  CurrentPushforwardCompositionParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Images.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variables (U:set (R_n R m)) (V:set (R_n R n)).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) U x.
Hypothesis hV:forall y,V y->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) V y.
Variable f:R_n R m->R_n R n.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hf:norm_class_all_orders
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U f.
Variable k:nat.
Variable T:@current_space R h2 m U hU k.
Hypothesis hT:@compact (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m U hU k T).
Local Notation Push := (@current_compact_map_pushforward R h2 m n U V hU hV
  f hImage hf k T hT).
Local Notation Proper := (@current_compact_map_proper R h2 m n k U V hU T f hImage
  (norm_class_continuous (hf 0%N)) hT).

(** Source for [current_compact_map_image_compact]: the
    original smooth image of a compact current has compact
    support, supporting the reversing and affine images in
    Federer 4.1.11, p. 365. Reuse the general support theorem. *)
Theorem current_compact_map_image_compact:
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n V hV k Push).
Proof.
exact:(@current_pushforward_compact_support R h2 m n U V hU hV f hImage hf
  k T Proper hT).
Qed.

(** Source for [current_compact_map_images_agree]: maps
    agreeing on the original source give the same image of T,
    with any compactness witnesses. This supporting comparison
    identifies the coordinate maps in Federer 4.1.11, pp. 365–366. *)
Theorem current_compact_map_images_agree (g:R_n R m->R_n R n)
    (hGImage:forall x,U x->V (g x))
    (hg:norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U g)
    (hT':@compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m)))
      (@current_support R h2 m U hU k T)):
  (forall x,U x->f x=g x)->Push=
    @current_compact_map_pushforward R h2 m n U V hU hV g hGImage hg k T hT'.
Proof.
move=>hEqual.
exact:(@current_pushforward_map_agreement R h2 m n k U V hU hV
  f g hImage hGImage hf hg T Proper
  (@current_compact_map_proper R h2 m n k U V hU T g hGImage
    (norm_class_continuous (hg 0%N)) hT') hEqual).
Qed.
End Images.

Section Composition.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n v:nat.
Variables (U:set (R_n R m)) (V:set (R_n R n)) (W:set (R_n R v)).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) U x.
Hypothesis hV:forall y,V y->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) V y.
Hypothesis hW:forall z,W z->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R v)) W z.
Variables (f:R_n R m->R_n R n) (g:R_n R n->R_n R v).
Hypothesis hFImage:forall x,U x->V (f x).
Hypothesis hGImage:forall y,V y->W (g y).
Hypothesis hf:norm_class_all_orders
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U f.
Hypothesis hg:norm_class_all_orders
  (inner_norm_real_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R v)) V g.
Variable k:nat.
Variable T:@current_space R h2 m U hU k.
Hypothesis hT:@compact (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R m)))
  (@current_support R h2 m U hU k T).
Local Notation S := (@current_compact_map_pushforward R h2 m n U V hU hV
  f hFImage hf k T hT).
Hypothesis hS:@compact (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n V hV k S).
Local Notation GFImage := (@current_smooth_composite_image R m n v U V W
  f g hFImage hGImage).
Local Notation GFClass := (@current_smooth_composite_class R m n v U V
  f g hFImage hf hg).

(** Source for [current_compact_map_images_compose]: the
    original compact image under g composed with f equals the
    successive images, supporting the reversing, affine and
    associativity identities of Federer 4.1.11, pp. 365–366.
    This is the preceding proper composition theorem. *)
Theorem current_compact_map_images_compose:
  @current_compact_map_pushforward R h2 m v U W hU hW
    (fun x=>g (f x)) GFImage GFClass k T hT=
  @current_compact_map_pushforward R h2 n v V W hV hW g hGImage hg k S hS.
Proof.
exact:(@current_pushforward_composition_parameters R h2 m n v k U V W hU hV hW
  f g hFImage hGImage hf hg T
  (@current_compact_map_proper R h2 m v k U W hU T
    (fun x=>g (f x)) GFImage (norm_class_continuous (GFClass 0%N)) hT)
  (@current_compact_map_proper R h2 m n k U V hU T f hFImage
    (norm_class_continuous (hf 0%N)) hT)
  (@current_compact_map_proper R h2 n v k V W hV S g hGImage
    (norm_class_continuous (hg 0%N)) hS)).
Qed.
End Composition.
