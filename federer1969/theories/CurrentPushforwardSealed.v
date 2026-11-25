(** Federer (1969), 4.1.7, p. 359:
    opaque original proper pushforward of
    a current. Existence and final-topology
    continuity are proved before this seal.
    The public law retains every compact
    replacement of the actual smooth pullback. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentProperSupport
  CurrentPushforwardUP CurrentPushforwardExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentPushforwardSignature.
(** Source for [value]: f#T with
    the original properness restriction on
    spt T, Federer 4.1.7, p. 359. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (v n m:nat)
    (U:R_n R v->Prop) (V:R_n R n->Prop)
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R v)) U x)
    (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y)
    (T:@current_space R h2 v U hU m) (f:R_n R v->R_n R n)
    (hImage:forall x,U x->V (f x))
    (hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R v))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U f)
    (hProper:@is_current_proper_on_support R h2 v n m U hU V T f hImage),
  @current_space R h2 n V hV m.
(** Source for [laws]: the actual
    original compact-cutoff action, expressed through
    its proved independent replacement law,
    Federer 4.1.7, p. 359. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (v n m:nat)
    (U:R_n R v->Prop) (V:R_n R n->Prop)
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R v)) U x)
    (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y)
    (T:@current_space R h2 v U hU m) (f:R_n R v->R_n R n)
    (hImage:forall x,U x->V (f x))
    (hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R v))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U f)
    (hProper:@is_current_proper_on_support R h2 v n m U hU V T f hImage),
  @is_current_pushforward R h2 v n m U V hU hV T f hImage hf
    (@value R h2 v n m U V hU hV T f hImage hf hProper).
End CurrentPushforwardSignature.
Module CurrentPushforward:CurrentPushforwardSignature.
(** Source for [value]: hide the
    proved actual current witness of
    Federer 4.1.7, p. 359. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (v n m:nat)
    (U:R_n R v->Prop) (V:R_n R n->Prop)
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R v)) U x)
    (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y)
    (T:@current_space R h2 v U hU m) (f:R_n R v->R_n R n)
    (hImage:forall x,U x->V (f x))
    (hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R v))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U f)
    (hProper:@is_current_proper_on_support R h2 v n m U hU V T f hImage):
    @current_space R h2 n V hV m:=
  projT1 (cid (@current_pushforward_exists R h2 v n m U V hU hV T f hImage hf hProper)).
(** Source for [laws]: the opaque
    witness satisfies the independently specified
    original action, Federer 4.1.7, p. 359. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (v n m:nat)
    (U:R_n R v->Prop) (V:R_n R n->Prop)
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R v)) U x)
    (hV:forall y,V y->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) V y)
    (T:@current_space R h2 v U hU m) (f:R_n R v->R_n R n)
    (hImage:forall x,U x->V (f x))
    (hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R v))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U f)
    (hProper:@is_current_proper_on_support R h2 v n m U hU V T f hImage):
  @is_current_pushforward R h2 v n m U V hU hV T f hImage hf
    (@value R h2 v n m U V hU hV T f hImage hf hProper).
Proof.
exact:(projT2 (cid (@current_pushforward_exists R h2 v n m U V hU hV T f hImage hf hProper))).
Qed.
End CurrentPushforward.
