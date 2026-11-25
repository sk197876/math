(** Federer (1969), 4.1.14, pp. 370–371: seal the
    actual compact Lipschitz image map. Its independent
    original approximation law, sharp norm bound and
    actual-current evaluation are public. Normal limits,
    bounded-extension witnesses and source preimages stay
    hidden behind this module signature. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentSpaces FlatCurrentsUP FlatCurrentClosure
  FlatCurrentSpaces LinearSubspaceRepresentationUP CurrentLipschitzCompactImage
  CurrentLipschitzFlatCoefficient CurrentCompactLipschitzPushforwardUP
  CurrentCompactLipschitzPushforwardExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type CurrentCompactLipschitzPushforwardSignature.
(** Source for [map]: the original linear map between the actual flat spaces, Federer
    4.1.14, pp. 370–371. *)
Parameter map:forall (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U),Hom (@flat_current_space R h2 n m U hU K) (@flat_current_space R h2 nu m V hV (@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K)).
(** Source for [map_laws]: every original approximation requirement holds, Federer
    4.1.14, pp. 370–371. *)
Parameter map_laws:forall (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U),
  @is_current_compact_lipschitz_pushforward R h2 n nu m U V hU hV f hImage hLocal K (@map R h2 n nu m U V hU hV f hImage hLocal K).
(** Source for [map_bound]: the exact maximum of the adjacent Lipschitz powers, Federer
    4.1.14, pp. 370–371. *)
Parameter map_bound:forall (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U) (L:R),
  (@is_least_metric_lipschitz_constant R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu)))
      (smooth_compact_carrier K) f L) ->forall z,(@flat_current_norm R h2 nu m V hV (@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K) (@map R h2 n nu m U V hU hV f hImage hLocal K z))<=current_lipschitz_flat_coefficient m L*(@flat_current_norm R h2 n m U hU K z).
(** Source for [value]: the image of every original actual fixed-K flat current, Federer
    4.1.14, pp. 370–371. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U) (T:(@current_space R h2 n U hU m)) (hFlat:(@is_flat_current_supported_in R h2 n m U hU K) T),(@current_space R h2 nu V hV m).
(** Source for [laws]: the actual image satisfies the original point specification, Federer
    4.1.14, pp. 370–371. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U) (T:(@current_space R h2 n U hU m)) (hFlat:(@is_flat_current_supported_in R h2 n m U hU K) T),
  @is_current_compact_lipschitz_image R h2 n nu m U V hU hV f hImage hLocal K T (@value R h2 n nu m U V hU hV f hImage hLocal K T hFlat).
(** Source for [value_map]: agreement of the carrier and actual-current interfaces, Federer
    4.1.14, pp. 370–371. *)
Parameter value_map:forall (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U) (z:(@flat_current_space R h2 n m U hU K))
    (hFlat:(@is_flat_current_supported_in R h2 n m U hU K) ((@flat_current_inclusion R h2 n m U hU K) z)),
  @value R h2 n nu m U V hU hV f hImage hLocal K ((@flat_current_inclusion R h2 n m U hU K) z) hFlat=
    (@flat_current_inclusion R h2 nu m V hV (@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K)) (@map R h2 n nu m U V hU hV f hImage hLocal K z).
End CurrentCompactLipschitzPushforwardSignature.

Module CurrentCompactLipschitzPushforward:CurrentCompactLipschitzPushforwardSignature.
(** Source for [map]: select one independently proved compact flat map, Federer
    4.1.14, pp. 370–371. *)
Definition map (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U):Hom (@flat_current_space R h2 n m U hU K) (@flat_current_space R h2 nu m V hV (@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K)):=
  projT1 (cid (@current_compact_lipschitz_pushforward_exists R h2 n nu m U V hU hV f hImage hLocal K)).
(** Source for [map_laws]: the selected map has all independent original laws, Federer
    4.1.14, pp. 370–371. *)
Lemma map_laws (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U):
  @is_current_compact_lipschitz_pushforward R h2 n nu m U V hU hV f hImage hLocal K (@map R h2 n nu m U V hU hV f hImage hLocal K).
Proof. exact:(projT2 (cid (@current_compact_lipschitz_pushforward_exists R h2 n nu m U V hU hV f hImage hLocal K))).1. Qed.
(** Source for [map_bound]: the selected map retains the proved sharp bound, Federer
    4.1.14, pp. 370–371. *)
Lemma map_bound (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U) (L:R):
  (@is_least_metric_lipschitz_constant R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu)))
      (smooth_compact_carrier K) f L) ->forall z,(@flat_current_norm R h2 nu m V hV (@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K) (@map R h2 n nu m U V hU hV f hImage hLocal K z))<=current_lipschitz_flat_coefficient m L*(@flat_current_norm R h2 n m U hU K z).
Proof. exact:(projT2 (cid (@current_compact_lipschitz_pushforward_exists R h2 n nu m U V hU hV f hImage hLocal K))).2. Qed.
(** Source for [representative]: a carrier preimage used only inside the sealed implementation, Federer
    4.1.14, pp. 370–371. *)
Definition representative (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U) (T:(@current_space R h2 n U hU m)) (hFlat:(@is_flat_current_supported_in R h2 n m U hU K) T):(@flat_current_space R h2 n m U hU K):=
  projT1 (cid (subspace_representation_full (@flat_current_space_laws R h2 n m U hU K) hFlat)).
(** Source for [representative_value]: the hidden preimage is the original source current, Federer
    4.1.14, pp. 370–371. *)
Lemma representative_value (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U) (T:(@current_space R h2 n U hU m)) (hFlat:(@is_flat_current_supported_in R h2 n m U hU K) T):
  (@flat_current_inclusion R h2 n m U hU K) (@representative R h2 n nu m U V hU hV f hImage hLocal K T hFlat)=T.
Proof. exact:projT2 (cid (subspace_representation_full (@flat_current_space_laws R h2 n m U hU K) hFlat)). Qed.
(** Source for [value]: evaluate the proved map on a hidden source carrier preimage, Federer
    4.1.14, pp. 370–371. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U) (T:(@current_space R h2 n U hU m)) (hFlat:(@is_flat_current_supported_in R h2 n m U hU K) T):(@current_space R h2 nu V hV m):=
  (@flat_current_inclusion R h2 nu m V hV (@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K)) (@map R h2 n nu m U V hU hV f hImage hLocal K (@representative R h2 n nu m U V hU hV f hImage hLocal K T hFlat)).
(** Source for [laws]: the actual image has the independent original point law, Federer
    4.1.14, pp. 370–371. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U) (T:(@current_space R h2 n U hU m)) (hFlat:(@is_flat_current_supported_in R h2 n m U hU K) T):
  @is_current_compact_lipschitz_image R h2 n nu m U V hU hV f hImage hLocal K T (@value R h2 n nu m U V hU hV f hImage hLocal K T hFlat).
Proof.
have h:=@map_laws R h2 n nu m U V hU hV f hImage hLocal K (@representative R h2 n nu m U V hU hV f hImage hLocal K T hFlat).
by rewrite (@representative_value R h2 n nu m U V hU hV f hImage hLocal K T hFlat) in h.
Qed.
(** Source for [value_map]: source inclusion injectivity removes the hidden preimage, Federer
    4.1.14, pp. 370–371. *)
Lemma value_map (R:realType) (h2:(1+1:R)!=0) (n nu m:nat)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U) (z:(@flat_current_space R h2 n m U hU K))
    (hFlat:(@is_flat_current_supported_in R h2 n m U hU K) ((@flat_current_inclusion R h2 n m U hU K) z)):
  @value R h2 n nu m U V hU hV f hImage hLocal K ((@flat_current_inclusion R h2 n m U hU K) z) hFlat=
    (@flat_current_inclusion R h2 nu m V hV (@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K)) (@map R h2 n nu m U V hU hV f hImage hLocal K z).
Proof.
have hEqual:@representative R h2 n nu m U V hU hV f hImage hLocal K ((@flat_current_inclusion R h2 n m U hU K) z) hFlat=z.
  apply:(subspace_representation_injective (@flat_current_space_laws R h2 n m U hU K)).
  exact:@representative_value R h2 n nu m U V hU hV f hImage hLocal K ((@flat_current_inclusion R h2 n m U hU K) z) hFlat.
by rewrite /value hEqual.
Qed.
End CurrentCompactLipschitzPushforward.

Arguments CurrentCompactLipschitzPushforward.map : clear implicits.

Arguments CurrentCompactLipschitzPushforward.map_laws : clear implicits.

Arguments CurrentCompactLipschitzPushforward.map_bound : clear implicits.

Arguments CurrentCompactLipschitzPushforward.value : clear implicits.

Arguments CurrentCompactLipschitzPushforward.laws : clear implicits.

Arguments CurrentCompactLipschitzPushforward.value_map : clear implicits.
