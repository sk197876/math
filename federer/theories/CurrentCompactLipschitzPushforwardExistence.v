(** Federer (1969), 4.1.14, p. 371: extend the
    original normal-current map uniquely to the complete
    flat-current space, retaining the sharp coefficient
    and every original smooth-approximation condition.
    The old opaque normal and flat carriers are used
    throughout; completeness is needed only in the target. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP LipschitzBasic LipschitzConstant OpenLocalLipschitzCompact SmoothCompactSet
  CurrentSpaces NormalCurrentSpaces FlatCurrentsUP FlatCurrentSpaces
  LinearSubspaceRepresentationUP CurrentNormalFlatInclusion
  CurrentLipschitzCompactImage CurrentLipschitzFlatCoefficient
  CurrentCompactLipschitzPushforwardUP CurrentCompactLipschitzImageUniqueness
  CurrentNormalLipschitzPushforwardUP CurrentNormalLipschitzPushforwardExistence
  CurrentNormalLipschitzOperatorBound CurrentBoundedNormalExtensionImage
  BanachDenseLinearExtensionUP BanachDenseLinearExtensionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentCompactLipschitzPushforwardExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation YT:=(real_norm_metric_space hNY).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hLocal:@is_locally_metric_lipschitz R XT YT U f.
Variable K:smooth_compact_set hNX U.
Local Notation fK:=(@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K).
Local Notation A:=(@supported_normal_current_space R h2 n U hU m K).
Local Notation Source:=(@flat_current_space R h2 n m U hU K).
Local Notation Target:=(@flat_current_space R h2 nu m V hV fK).
Local Notation SourceNorm:=(@flat_current_norm R h2 n m U hU K).
Local Notation TargetNorm:=(@flat_current_norm R h2 nu m V hV fK).
Local Notation i:=(@current_normal_flat_inclusion R h2 n m U hU K).
Local Notation Spec:=(@is_current_compact_lipschitz_pushforward R h2 n nu m U V hU hV
  f hImage hLocal K).

(** Source for [current_compact_lipschitz_pushforward_exists]:
    the original compact flat image map exists and has
    the exact norm bound with the least compact-restriction
    Lipschitz constant, Federer 4.1.14, p. 371. The
    selected normal map and extension remain witnesses
    of this existence proof, not caller hypotheses. *)
Theorem current_compact_lipschitz_pushforward_exists:
  exists G:Hom Source Target,Spec G /\
    forall L:R,@is_least_metric_lipschitz_constant R XT YT
      (smooth_compact_carrier K) f L ->
      forall z,TargetNorm (G z)<=current_lipschitz_flat_coefficient m L*SourceNorm z.
Proof.
have[P hP]:=@current_normal_lipschitz_pushforward_exists R h2 n nu m U V hU hV
  f hImage hLocal K.
pose hLip:=@norm_open_local_lipschitz_compact R X Y NX NY hNX hNY U f
  (smooth_compact_carrier K) hU hLocal (smooth_compact_is_compact K)
  (smooth_compact_in_domain K).
pose L:=metric_lipschitz_constant hLip.
pose hLeast:=metric_lipschitz_constant_specification hLip.
pose C:=current_lipschitz_flat_coefficient m L.
have hC:0<=C:=@current_lipschitz_flat_coefficient_nonnegative R m L
  (least_metric_lipschitz_bound hLeast).1.
have hDense:@is_norm_dense_linear_image R A Source SourceNorm i.
  exact:(@current_normal_flat_inclusion_dense R h2 n m U hU K).
have hNormalBound:forall a,TargetNorm (P a)<=C*SourceNorm (i a).
  exact:(@current_normal_lipschitz_operator_bound R h2 n nu m U V hU hV
    f hImage hLocal K P hP L (least_metric_lipschitz_bound hLeast)).
have[G hExtension]:=@bounded_dense_linear_extension_exists R A Source Target
  SourceNorm TargetNorm (@flat_current_norm_is_norm R h2 n m U hU K)
  (@flat_current_norm_is_norm R h2 nu m V hV fK)
  (@flat_current_complete R h2 nu m V hV fK) i P C hC hDense hNormalBound.
exists G;split.
- exact:(@current_bounded_normal_extension_image R h2 n nu m U V hU hV
    f hImage hLocal K P hP G C hC hExtension.1 hExtension.2).
- move=>L' hLeast' z.
  have hEquality:L=L'.
    exact:(@least_metric_lipschitz_unique R XT YT (smooth_compact_carrier K)
      f L L' hLeast hLeast').
  rewrite -hEquality;exact:hExtension.2 z.
Qed.

(** Source for [current_compact_lipschitz_pushforward_unique]:
    the original independent approximation law determines
    one actual compact linear map, Federer 4.1.14,
    pp. 370–371. Pointwise uniqueness and the actual
    opaque flat inclusion suffice; no candidate norm
    bound is postulated for this uniqueness theorem. *)
Theorem current_compact_lipschitz_pushforward_unique (G H:Hom Source Target):
  Spec G->Spec H->G=H.
Proof.
move=>hG hH;apply:hom_ext=>z.
apply:(subspace_representation_injective (@flat_current_space_laws R h2 nu m V hV fK)).
exact:(@current_compact_lipschitz_image_unique R h2 n nu m U V hU hV
  f hImage hLocal K (@flat_current_inclusion R h2 n m U hU K z)
  (subspace_representation_member (@flat_current_space_laws R h2 n m U hU K) z)
  _ _ (hG z) (hH z)).
Qed.
End CurrentCompactLipschitzPushforwardExistence.
