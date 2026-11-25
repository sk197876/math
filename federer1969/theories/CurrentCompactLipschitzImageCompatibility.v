(** Federer (1969), 4.1.14, p. 371: the
    compact image maps combine on the union of the
    fixed-support flat spaces. Compare two original
    compact indices in their union; neither current
    is redefined and no new compact exhaustion is used. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentSpaces FlatCurrentsUP
  CurrentLipschitzCompactImage CurrentFlatCompactMonotone
  CurrentCompactLipschitzPushforwardUP CurrentCompactLipschitzImageUniqueness
  CurrentCompactLipschitzImageCompactMonotone CurrentCompactLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactLipschitzImageCompatibility.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variables K L:smooth_compact_set hNX U.
Variable T:@current_space R h2 n U hU m.
Hypothesis hK:@is_flat_current_supported_in R h2 n m U hU K T.
Hypothesis hL:@is_flat_current_supported_in R h2 n m U hU L T.

(** Source for [current_compact_lipschitz_images_compatible]:
    any two original compact-index definitions give the
    same actual current, Federer 4.1.14, p. 371.
    The indices need not be nested or nonempty. *)
Theorem current_compact_lipschitz_images_compatible
    (Q P:@current_space R h2 nu V hV m):
  @is_current_compact_lipschitz_image R h2 n nu m U V hU hV
    f hImage hLocal K T Q ->
  @is_current_compact_lipschitz_image R h2 n nu m U V hU hV
    f hImage hLocal L T P ->Q = P.
Proof.
move=>hQ hP.
pose J:=smooth_compact_union K L.
have hKJ:smooth_compact_carrier K `<=` smooth_compact_carrier J by move=>x hx;left.
have hLJ:smooth_compact_carrier L `<=` smooth_compact_carrier J by move=>x hx;right.
have hFlatJ:=@flat_current_compact_monotone R h2 n m U hU K J hKJ T hK.
have hQJ:=@current_compact_lipschitz_image_compact_mono R h2 n nu m U V hU hV
  f hImage hLocal K J hKJ T hK Q hQ.
have hPJ:=@current_compact_lipschitz_image_compact_mono R h2 n nu m U V hU hV
  f hImage hLocal L J hLJ T hL P hP.
exact:(@current_compact_lipschitz_image_unique R h2 n nu m U V hU hV
  f hImage hLocal J T hFlatJ Q P hQJ hPJ).
Qed.

(** Source for [current_compact_lipschitz_pushforward_compatible]:
    the sealed actual values agree for any two original
    compact indices, Federer 4.1.14, p. 371. *)
Theorem current_compact_lipschitz_pushforward_compatible:
  @CurrentCompactLipschitzPushforward.value R h2 n nu m U V hU hV
    f hImage hLocal K T hK=
  @CurrentCompactLipschitzPushforward.value R h2 n nu m U V hU hV
    f hImage hLocal L T hL.
Proof.
apply:current_compact_lipschitz_images_compatible.
- exact:(@CurrentCompactLipschitzPushforward.laws R h2 n nu m U V hU hV
    f hImage hLocal K T hK).
- exact:(@CurrentCompactLipschitzPushforward.laws R h2 n nu m U V hU hV
    f hImage hLocal L T hL).
Qed.
End CurrentCompactLipschitzImageCompatibility.
