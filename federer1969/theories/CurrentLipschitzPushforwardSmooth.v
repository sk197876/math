(** Federer (1969), 4.1.14, p. 371: the
    original locally flat Lipschitz image extends
    the smooth image and preserves the identity.
    Use the independent local smooth-agreement law
    and the original identity pullback on actual
    compact tests; no mass or support compactness
    is needed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP CurrentSpaces
  CurrentSupportGeometry CurrentEvaluation CurrentProperSupport
  CurrentPushforwardUP CurrentPushforwardSealed CurrentElementaryPullbacks
  CurrentOpenIdentitySmooth SmoothFormPullbackSealed SmoothTestSpaces
  FlatCurrentsUP CurrentLipschitzPushforwardSealed CurrentLipschitzImageSmoothAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_lipschitz_pushforward_smooth]:
    the original locally Lipschitz image agrees
    with the original smooth pushforward, Federer
    4.1.14, p. 371. Properness remains only
    on the actual source support. *)
Theorem current_lipschitz_pushforward_smooth
    (R:realType) (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (hf:norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U f)
    (T:@current_space R h2 n U hU m)
    (hT:@is_locally_flat_current R h2 n m U hU T)
    (hProper:@is_current_proper_on_support R h2 n nu m U hU V T f hImage):
  @CurrentLipschitzPushforward.value R h2 n nu m U V hU hV
    f hImage hLocal T hT hProper=
  @CurrentPushforward.value R h2 n nu m U V hU hV T f hImage hf hProper.
Proof.
exact:(@current_lipschitz_image_smooth_agreement R h2 n nu m U V hU hV
  f hImage hLocal hf T hT hProper _
  (@CurrentLipschitzPushforward.laws R h2 n nu m U V hU hV
    f hImage hLocal T hT hProper)).
Qed.

(** Source for [current_support_proper_identity_pushforward]:
    identity pushforward fixes every original current
    under its support properness, by the identity
    pullback in Federer 4.1.10, p. 364,
    supporting the local identity law of 4.1.14,
    p. 371. Compactness of the source support
    is not required for this supporting extension. *)
Theorem current_support_proper_identity_pushforward
    (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hImage:forall x,U x->U x)
    (hf:norm_class_all_orders
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U (fun x=>x))
    (T:@current_space R h2 n U hU m)
    (hProper:@is_current_proper_on_support R h2 n n m U hU U T (fun x=>x) hImage):
  @CurrentPushforward.value R h2 n n m U U hU hU T (fun x=>x) hImage hf hProper=T.
Proof.
apply:(@current_values_extensional R h2 n m U hU)=>phi.
apply:(@CurrentPushforward.laws R h2 n n m U U hU hU T (fun x=>x)
  hImage hf hProper phi phi).
exists U;split.
- rewrite openE=>x hx.
  exact:(@norm_domain_interior_neighbourhood R (R_n R n)
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) U x).1 (@hU x hx).
split;first by move=>x hx;exact:hx.1.
split;first by move=>x hx.
move=>x hx;rewrite (@current_identity_pullback R h2 n U hU m hImage hf).
by [].
Qed.

(** Source for [current_lipschitz_pushforward_identity]:
    the original identity image is T itself,
    Federer 4.1.14, p. 371, for every
    locally flat current, including noncompact support
    and arbitrary original open or empty domains. *)
Theorem current_lipschitz_pushforward_identity
    (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) U (fun x=>x))
    (T:@current_space R h2 n U hU m)
    (hT:@is_locally_flat_current R h2 n m U hU T)
    (hProper:@is_current_proper_on_support R h2 n n m U hU U T (fun x=>x)
      (fun x (hx:U x)=>hx)):
  @CurrentLipschitzPushforward.value R h2 n n m U U hU hU (fun x=>x)
    (fun x (hx:U x)=>hx) hLocal T hT hProper=T.
Proof.
rewrite (@current_lipschitz_pushforward_smooth R h2 n n m U U hU hU
  (fun x=>x) (fun x (hx:U x)=>hx) hLocal
  (@current_open_identity_smooth R n U hU) T hT hProper).
exact:current_support_proper_identity_pushforward.
Qed.
