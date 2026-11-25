(** Federer (1969), 4.1.14, p. 371: seal the
    actual compactly supported flat-current image.
    A compact source index is chosen only inside the
    existence proof. The public laws retain agreement
    with every original fixed-index image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentSpaces FlatCurrentsUP
  CurrentCompactLipschitzImageUniqueness CurrentCompactLipschitzPushforwardSealed
  CurrentFlatLipschitzPushforwardUP CurrentFlatLipschitzPushforwardExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type CurrentFlatLipschitzPushforwardSignature.
(** Source for [value]: the original actual flat-current image on the compact-index union, Federer
    4.1.14, p. 371. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f) (T:(@current_space R h2 n U hU m)) (hFlat:(@is_flat_current R h2 n m U hU T)),(@current_space R h2 nu V hV m).
(** Source for [laws]: the original flat image agrees with every compact index, Federer
    4.1.14, p. 371. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f) (T:(@current_space R h2 n U hU m)) (hFlat:(@is_flat_current R h2 n m U hU T)),
  @is_current_flat_lipschitz_image R h2 n nu m U V hU hV f hImage hLocal T (@value R h2 n nu m U V hU hV f hImage hLocal T hFlat).
(** Source for [compact_value]: agreement with every original fixed-support definition, Federer
    4.1.14, p. 371. *)
Parameter compact_value:forall (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f) (T:(@current_space R h2 n U hU m)) (hFlat:(@is_flat_current R h2 n m U hU T))
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U) (hK:@is_flat_current_supported_in R h2 n m U hU K T),
  @value R h2 n nu m U V hU hV f hImage hLocal T hFlat=
    @CurrentCompactLipschitzPushforward.value R h2 n nu m U V hU hV f hImage hLocal K T hK.
End CurrentFlatLipschitzPushforwardSignature.

Module CurrentFlatLipschitzPushforward:CurrentFlatLipschitzPushforwardSignature.
(** Source for [value]: select one independently proved original union image, Federer
    4.1.14, p. 371. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f) (T:(@current_space R h2 n U hU m)) (hFlat:(@is_flat_current R h2 n m U hU T)):(@current_space R h2 nu V hV m):=
  projT1 (cid (@current_flat_lipschitz_pushforward_exists R h2 n nu m U V hU hV f hImage hLocal T hFlat)).
(** Source for [laws]: the selected value satisfies the independent union law, Federer
    4.1.14, p. 371. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f) (T:(@current_space R h2 n U hU m)) (hFlat:(@is_flat_current R h2 n m U hU T)):
  @is_current_flat_lipschitz_image R h2 n nu m U V hU hV f hImage hLocal T (@value R h2 n nu m U V hU hV f hImage hLocal T hFlat).
Proof. exact:projT2 (cid (@current_flat_lipschitz_pushforward_exists R h2 n nu m U V hU hV f hImage hLocal T hFlat)). Qed.
(** Source for [compact_value]: pointwise uniqueness removes any hidden compact-index choice, Federer
    4.1.14, p. 371. *)
Lemma compact_value (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f) (T:(@current_space R h2 n U hU m)) (hFlat:(@is_flat_current R h2 n m U hU T))
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U) (hK:@is_flat_current_supported_in R h2 n m U hU K T):
  @value R h2 n nu m U V hU hV f hImage hLocal T hFlat=
    @CurrentCompactLipschitzPushforward.value R h2 n nu m U V hU hV f hImage hLocal K T hK.
Proof.
apply:(@current_compact_lipschitz_image_unique R h2 n nu m U V hU hV f hImage hLocal K T hK).
- exact:(@laws R h2 n nu m U V hU hV f hImage hLocal T hFlat).2 K hK.
- exact:(@CurrentCompactLipschitzPushforward.laws R h2 n nu m U V hU hV f hImage hLocal K T hK).
Qed.
End CurrentFlatLipschitzPushforward.

Arguments CurrentFlatLipschitzPushforward.value : clear implicits.

Arguments CurrentFlatLipschitzPushforward.laws : clear implicits.

Arguments CurrentFlatLipschitzPushforward.compact_value : clear implicits.
