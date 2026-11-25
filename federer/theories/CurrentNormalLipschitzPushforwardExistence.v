(** Federer (1969), 4.1.14, pp. 370–371: existence
    of the original linear normal-current image. Select
    actual images only inside the proof, prove linearity
    from their original approximation law, and corestrict
    through the existing opaque flat-current inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct LipschitzUP SmoothCompactSet CurrentSpaces
  NormalCurrentsUP NormalCurrentSpaces FlatCurrentsUP FlatCurrentFinite FlatCurrentClosure
  FlatCurrentSpaces LinearSubspaceRepresentationUP LinearSubspaceLiftSealed
  CurrentLipschitzCompactImage CurrentCompactLipschitzPushforwardUP
  CurrentNormalLipschitzPushforwardUP CurrentNormalLipschitzImageExistence
  CurrentCompactLipschitzImageLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentNormalLipschitzPushforwardExistence.
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
Variable K:smooth_compact_set hNX U.
Local Notation fK:=(@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K).
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation D:=(@current_space R h2 nu V hV m).
Local Notation A:=(@supported_normal_current_space R h2 n U hU m K).
Local Notation B:=(@flat_current_space R h2 nu m V hV fK).
Local Notation incA:=(@supported_normal_current_inclusion R h2 n U hU m K).
Local Notation incB:=(@flat_current_inclusion R h2 nu m V hV fK).
Local Notation hA:=(@supported_normal_current_space_laws R h2 n U hU m K).
Local Notation hB:=(@flat_current_space_laws R h2 nu m V hV fK).
Local Notation flatB:=(@flat_current_subspace R h2 nu m V hV fK).
Local Notation Image:=(@is_current_compact_lipschitz_image R h2 n nu m U V hU hV
  f hImage hLocal K).

(** Source for [current_normal_lipschitz_pushforward_exists]:
    the linear map on N_(m,K)(U) exists before its
    extension to F_(m,K)(U), Federer 4.1.14, pp. 370–371.
    Its actual images satisfy every original approximation
    condition. The choice of their witnesses is not public. *)
Theorem current_normal_lipschitz_pushforward_exists:
  exists P:Hom A B,@is_current_normal_lipschitz_pushforward R h2 n nu m U V hU hV
    f hImage hLocal K P.
Proof.
have hExist a:exists Q:D,@is_normal_current R h2 nu V hV m Q /\Image (incA a) Q.
  have hMember:=subspace_representation_member hA a.
  exact:(@current_normal_lipschitz_image_exists R h2 n nu m U V hU hV
    f hImage hLocal K (incA a) hMember.1 hMember.2).
have[q hq]:=choice hExist.
have hFlat a:@is_flat_current_supported_in R h2 n m U hU K (incA a).
  exact:(@supported_normal_current_is_flat R h2 n m U hU K (incA a)
    (subspace_representation_member hA a)).
have hLinear:linear q.
  move=>c a b.
  have hInclusion:incA (c*:a+b)=c*:incA a+incA b:=linearP incA c a b.
  have hCombination:@is_flat_current_supported_in R h2 n m U hU K
      (c*:incA a+incA b).
    by rewrite -hInclusion;exact:hFlat (c*:a+b).
  have hCandidate:Image (c*:incA a+incA b) (q (c*:a+b)).
    by rewrite -hInclusion;exact:(hq (c*:a+b)).2.
  exact:(@current_compact_lipschitz_image_linear R h2 n nu m U V hU hV
    f hImage hLocal K c (incA a) (incA b) (q a) (q b) (q (c*:a+b))
    (hFlat a) (hFlat b) (hq a).2 (hq b).2 hCandidate).
pose F:Hom A D:=@HomMap R A D q (introT (asboolP _) hLinear).
have hRange a:flatB (F a):=(hq a).2.1.
pose P:=@LinearSubspaceLift.map R A B D flatB incB hB F hRange.
have hValue a:incB (P a)=q a.
  exact:(@LinearSubspaceLift.evaluation R A B D flatB incB hB F hRange a).
exists P=>a;rewrite hValue;exact:hq a.
Qed.
End CurrentNormalLipschitzPushforwardExistence.
