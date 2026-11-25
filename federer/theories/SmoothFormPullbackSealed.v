(** Federer (1969), 4.1.7, p. 359:
    the actual original smooth form
    pullback is opaque. Its independently
    specified graph law is public;
    continuity is proved separately from
    the original coordinate generators. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothFormPullbackUP SmoothFormPullbackExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type SmoothFormPullbackSignature.
(** Source for [operator]: the original
    pullback on actual smooth form
    spaces, supporting Federer 4.1.7,
    p. 359, by 4.1.6, p. 354. *)
Parameter operator:forall (R:realType) (h2:(1+1:R)!=0) (v n m:nat)
    (U:R_n R v->Prop) (V:R_n R n->Prop)
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R v)) U x)
    (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y)
    (f:R_n R v->R_n R n),
  (forall x,U x->V (f x))->
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R v))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) U f->
  Hom (@current_smooth_space R h2 n V hV m) (@current_smooth_space R h2 v U hU m).
(** Source for [laws]: exact agreement
    with the original partial pullback
    at every domain point, supporting
    Federer 4.1.7, p. 359. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (v n m:nat)
    (U:R_n R v->Prop) (V:R_n R n->Prop)
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R v)) U x)
    (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y)
    (f:R_n R v->R_n R n) (hImage:forall x,U x->V (f x))
    (hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R v))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U f),
  is_smooth_form_pullback U V (@current_smooth_value R h2 n V hV m)
    (@current_smooth_value R h2 v U hU m) f
    (@operator R h2 v n m U V hU hV f hImage hf).
End SmoothFormPullbackSignature.
Module SmoothFormPullback:SmoothFormPullbackSignature.
(** Source for [operator]: seal a
    proved linear pullback witness, supporting
    Federer 4.1.7, p. 359. *)
Definition operator (R:realType) (h2:(1+1:R)!=0) (v n m:nat)
    (U:R_n R v->Prop) (V:R_n R n->Prop)
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R v)) U x)
    (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y)
    (f:R_n R v->R_n R n) (hImage:forall x,U x->V (f x))
    (hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R v))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U f):
    Hom (@current_smooth_space R h2 n V hV m) (@current_smooth_space R h2 v U hU m):=
  projT1 (cid (@smooth_form_pullback_exists R h2 v n m U V hU hV f hImage hf)).
(** Source for [laws]: the opaque
    witness satisfies the independent original
    graph specification, supporting Federer 4.1.7,
    p. 359. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (v n m:nat)
    (U:R_n R v->Prop) (V:R_n R n->Prop)
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R v)) U x)
    (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y)
    (f:R_n R v->R_n R n) (hImage:forall x,U x->V (f x))
    (hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R v))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U f):
  is_smooth_form_pullback U V (@current_smooth_value R h2 n V hV m)
    (@current_smooth_value R h2 v U hU m) f
    (@operator R h2 v n m U V hU hV f hImage hf).
Proof.
exact:(projT2 (cid (@smooth_form_pullback_exists R h2 v n m U V hU hV f hImage hf))).
Qed.
End SmoothFormPullback.
