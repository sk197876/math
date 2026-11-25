(** Federer (1969), 4.1.14, p. 371: seal the
    actual locally flat image under properness only
    on spt T. The public law retains every original
    compact target test and every admissible scalar
    cutoff. Selected cutoffs and local gluing witnesses
    are absent from this interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentSpaces FlatCurrentsUP CurrentProperSupport
  CurrentLipschitzPushforwardUP CurrentLipschitzImageExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type CurrentLipschitzPushforwardSignature.
(** Source for [value]: the original locally flat image for support-proper f, Federer
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
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f) (T:(@current_space R h2 n U hU m))
    (hT:@is_locally_flat_current R h2 n m U hU T)
    (hProper:@is_current_proper_on_support R h2 n nu m U hU V T f hImage),(@current_space R h2 nu V hV m).
(** Source for [laws]: local flatness and the literal all-cutoff defining equation, Federer
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
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f) (T:(@current_space R h2 n U hU m))
    (hT:@is_locally_flat_current R h2 n m U hU T)
    (hProper:@is_current_proper_on_support R h2 n nu m U hU V T f hImage),
  @is_current_lipschitz_image R h2 n nu m U V hU hV f hImage hLocal T (@value R h2 n nu m U V hU hV f hImage hLocal T hT hProper).
End CurrentLipschitzPushforwardSignature.

Module CurrentLipschitzPushforward:CurrentLipschitzPushforwardSignature.
(** Source for [value]: select one independently proved actual local image, Federer
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
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f) (T:(@current_space R h2 n U hU m))
    (hT:@is_locally_flat_current R h2 n m U hU T)
    (hProper:@is_current_proper_on_support R h2 n nu m U hU V T f hImage):(@current_space R h2 nu V hV m):=
  projT1 (cid (@current_lipschitz_image_exists R h2 n nu m U V hU hV f hImage hLocal T hT hProper)).
(** Source for [laws]: the selected current has every independent original local law, Federer
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
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f) (T:(@current_space R h2 n U hU m))
    (hT:@is_locally_flat_current R h2 n m U hU T)
    (hProper:@is_current_proper_on_support R h2 n nu m U hU V T f hImage):
  @is_current_lipschitz_image R h2 n nu m U V hU hV f hImage hLocal T (@value R h2 n nu m U V hU hV f hImage hLocal T hT hProper).
Proof. exact:projT2 (cid (@current_lipschitz_image_exists R h2 n nu m U V hU hV f hImage hLocal T hT hProper)). Qed.
End CurrentLipschitzPushforward.

Arguments CurrentLipschitzPushforward.value : clear implicits.

Arguments CurrentLipschitzPushforward.laws : clear implicits.
