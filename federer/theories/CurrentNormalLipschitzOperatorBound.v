(** Federer (1969), 4.1.14, p. 371: express the
    original sharp flat estimate on the actual opaque
    normal and flat carriers. Their inclusions and
    exact norms are the existing 4.1.12 interfaces;
    no new completion or norm is constructed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentSpaces CurrentFlatNorm NormalCurrentsUP NormalCurrentSpaces
  FlatCurrentSpaces LinearSubspaceRepresentationUP CurrentNormalFlatInclusion
  CurrentLipschitzCompactImage CurrentLipschitzFlatCoefficient
  CurrentNormalLipschitzPushforwardUP CurrentNormalLipschitzImageFlatBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentNormalLipschitzOperatorBound.
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
Local Notation A:=(@supported_normal_current_space R h2 n U hU m K).
Local Notation W:=(@flat_current_space R h2 nu m V hV fK).
Local Notation incA:=(@supported_normal_current_inclusion R h2 n U hU m K).
Local Notation incW:=(@flat_current_inclusion R h2 nu m V hV fK).
Local Notation SourceNorm:=(@flat_current_norm R h2 n m U hU K).
Local Notation TargetNorm:=(@flat_current_norm R h2 nu m V hV fK).
Local Notation i:=(@current_normal_flat_inclusion R h2 n m U hU K).
Variable P:Hom A W.
Hypothesis hP:@is_current_normal_lipschitz_pushforward R h2 n nu m U V hU hV
  f hImage hLocal K P.

(** Source for [current_normal_lipschitz_operator_bound]:
    the bounded linear normal-domain map in Federer
    4.1.14, p. 371, has the printed maximum
    coefficient in the exact original flat norms. *)
Theorem current_normal_lipschitz_operator_bound (L:R):
  @is_metric_lipschitz_bound R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) (smooth_compact_carrier K) f L ->
  forall a:A,TargetNorm (P a)<=current_lipschitz_flat_coefficient m L*SourceNorm (i a).
Proof.
move=>hL a.
have hNormal:=subspace_representation_member
  (@supported_normal_current_space_laws R h2 n U hU m K) a.
have hBound:=@current_normal_lipschitz_image_flat_bound R h2 n nu m U V hU hV
  f hImage hLocal K (incA a) (incW (P a)) L hNormal (hP a).2 hL.
have hSource:@current_flat_norm R h2 n m U hU K (incA a)=(SourceNorm (i a))%:E.
  by rewrite -(@current_normal_flat_inclusion_value R h2 n m U hU K a)
    flat_current_norm_value.
by rewrite flat_current_norm_value hSource -EFinM lee_fin in hBound.
Qed.
End CurrentNormalLipschitzOperatorBound.
