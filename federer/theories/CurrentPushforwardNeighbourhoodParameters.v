(** Federer (1969), 4.1.13, pp. 369–370: source
    neighbourhood naturality with arbitrary evidence for the
    smaller map's image and smoothness. Reuse the preceding
    original composition proof and proof-data independence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentProperSupport CurrentPushforwardSealed CurrentOpenRestriction
  SmoothFormPullbackComposition CurrentPushforwardSourceNeighbourhood
  CurrentPushforwardDataIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentPushforwardNeighbourhoodParameters.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U V:set X) (W:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall x,V x->norm_domain_interior NX V x.
Hypothesis hW:forall y,W y->norm_domain_interior NY W y.
Hypothesis hUV:forall x,U x->V x.
Hypothesis hId:norm_class_all_orders hNX hNX U (fun x:X=>x).
Variable f:X->Y.
Hypothesis hImage:forall x,V x->W (f x).
Hypothesis hf:norm_class_all_orders hNX hNY V f.
Hypothesis hImageSmall:forall x,U x->W (f x).
Hypothesis hfSmall:norm_class_all_orders hNX hNY U f.
Local Notation compositeImage := (@current_smooth_composite_image R n n nu
  U V W (fun x:X=>x) f hUV hImage).
Local Notation compositeClass := (@current_smooth_composite_class R n n nu
  U V (fun x:X=>x) f hUV hId hf).
Variable T:@current_space R h2 n V hV m.
Hypothesis hSupport:@current_support R h2 n V hV m T `<=` U.
Local Notation S := (@current_open_restriction R h2 n m U V hU hV hUV T).
Hypothesis hpI:@is_current_proper_on_support R h2 n n m U hU V S (fun x:X=>x) hUV.
Hypothesis hpSmall:@is_current_proper_on_support R h2 n nu m U hU W S f hImageSmall.
Hypothesis hpLarge:@is_current_proper_on_support R h2 n nu m V hV W T f hImage.

(** Source for [current_pushforward_neighbourhood_parameters]:
    replacing the original source by a neighbourhood of its
    support preserves f#T, with every original smoothness
    and support-properness witness, supporting Federer
    4.1.13, pp. 369–370. *)
Theorem current_pushforward_neighbourhood_parameters:
  @CurrentPushforward.value R h2 n nu m V W hV hW T f hImage hf hpLarge=
    @CurrentPushforward.value R h2 n nu m U W hU hW S f hImageSmall hfSmall hpSmall.
Proof.
have hImages:compositeImage=hImageSmall:=Prop_irrelevance _ _.
have hpComposite:@is_current_proper_on_support R h2 n nu m U hU W S f compositeImage.
  by rewrite hImages.
have hSource:=@current_pushforward_source_neighbourhood R h2 n nu m
  U V W hU hV hW hUV hId f hImage hf T hSupport hpI hpComposite hpLarge.
have hReplace:=@current_pushforward_data_independent R h2 n nu m U W hU hW
  S f compositeImage hImageSmall compositeClass hfSmall hpComposite hpSmall.
exact:(eq_trans hSource hReplace).
Qed.
End CurrentPushforwardNeighbourhoodParameters.
