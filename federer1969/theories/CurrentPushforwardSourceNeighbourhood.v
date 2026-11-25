(** Federer (1969), 4.1.13, pp. 369–370: pushing
    forward a current is unchanged when its source is
    replaced by an open neighbourhood of the support.
    Recover the original current through inclusion and reuse
    the proper composition law of 4.1.7, p. 359. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentProperSupport CurrentPushforwardSealed CurrentPushforwardCongruence
  CurrentPushforwardCompositionParameters SmoothFormPullbackComposition
  CurrentOpenRestriction CurrentNeighbourhoodInclusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentPushforwardSourceNeighbourhood.
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
Local Notation hSmallImage := (@current_smooth_composite_image R n n nu
  U V W (fun x:X=>x) f hUV hImage).
Local Notation hSmallClass := (@current_smooth_composite_class R n n nu
  U V (fun x:X=>x) f hUV hId hf).
Variable T:@current_space R h2 n V hV m.
Hypothesis hSupport:@current_support R h2 n V hV m T `<=` U.
Local Notation S := (@current_open_restriction R h2 n m U V hU hV hUV T).
Hypothesis hpI:@is_current_proper_on_support R h2 n n m U hU V S (fun x:X=>x) hUV.
Hypothesis hpSmall:@is_current_proper_on_support R h2 n nu m U hU W S f hSmallImage.
Hypothesis hpLarge:@is_current_proper_on_support R h2 n nu m V hV W T f hImage.
Local Notation inclusion := (@CurrentPushforward.value R h2 n n m U V hU hV S
  (fun x:X=>x) hUV hId hpI).

(** Source for [current_pushforward_source_neighbourhood]:
    the original f#T is preserved by the support-neighbourhood
    replacement in Federer 4.1.13, pp. 369–370.
    All three properness witnesses refer only to actual
    current supports, and compactness supplies them in the
    original normal-current application. *)
Theorem current_pushforward_source_neighbourhood:
  @CurrentPushforward.value R h2 n nu m V W hV hW T f hImage hf hpLarge=
  @CurrentPushforward.value R h2 n nu m U W hU hW S f hSmallImage hSmallClass hpSmall.
Proof.
have hRecovery:inclusion=T:=@current_neighbourhood_inclusion_recovery R h2 n m
  U V hU hV hUV hId T hSupport hpI.
have hpAfter:@is_current_proper_on_support R h2 n nu m V hV W inclusion f hImage.
  by rewrite hRecovery.
have hCompose:=@current_pushforward_composition_parameters R h2 n n nu m
  U V W hU hV hW (fun x:X=>x) f hUV hImage hId hf S hpSmall hpI hpAfter.
have hReplace:=@current_pushforward_current_congruence R h2 n nu m V W hV hW
  f hImage hf inclusion T hpAfter hpLarge hRecovery.
exact:(esym (eq_trans hCompose hReplace)).
Qed.
End CurrentPushforwardSourceNeighbourhood.
