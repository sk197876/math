(** Federer (1969), 4.1.24, p. 380: two
    original image witnesses already placed in the same
    source add by the additive polyhedral subgroup and
    the actual linearity of its Lipschitz image. This
    algebraic step is separate from the preceding geometric
    placement existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces LipschitzUP LipschitzBasic FlatCurrentsUP FlatCurrentUnion
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic
  PolyhedralCurrentAlgebra PolyhedralCurrentFlat RectifiableCurrentApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectifiableCommonSourceImages.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables d n m:nat.
Variables (Z:set (R_n R d)) (U:set (R_n R n)).
Hypothesis hZ:forall x,Z x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R d)) Z x.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable C:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R d)) Z.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Variable f:R_n R d->R_n R n.
Hypothesis hImage:forall x,Z x->U (f x).
Hypothesis hLip:@is_metric_lipschitz R
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) Z f.
Hypothesis hCK:forall x,smooth_compact_carrier C x->smooth_compact_carrier K (f x).
Local Notation CU:=(@current_space R h2 n U hU m).
Local Notation CZ:=(@current_space R h2 d Z hZ m).
Local Notation Image:=(@polyhedral_lipschitz_image R h2 d n m Z U hZ hU C
  f hImage hLip).

(** Source for [polyhedral_lipschitz_image_add]: addition in
    the common integral polyhedral source gives actual
    addition of its original image currents, 4.1.24,
    p. 380. Membership witnesses are arbitrary. *)
Lemma polyhedral_lipschitz_image_add (P Q:CZ)
    (hP:@integral_polyhedral_current_class R h2 d m Z hZ C P)
    (hQ:@integral_polyhedral_current_class R h2 d m Z hZ C Q)
    (hSum:@integral_polyhedral_current_class R h2 d m Z hZ C (P+Q)):
  Image hSum=Image hP+Image hQ.
Proof.
pose hF:=metric_lipschitz_is_local hLip.
pose hPFlat:@is_flat_current R h2 d m Z hZ P:=ex_intro _ C
  (@integral_polyhedral_current_flat_supported R h2 d m Z hZ C P hP).
pose hQFlat:@is_flat_current R h2 d m Z hZ Q:=ex_intro _ C
  (@integral_polyhedral_current_flat_supported R h2 d m Z hZ C Q hQ).
pose hSumFlat:@is_flat_current R h2 d m Z hZ (P+Q):=ex_intro _ C
  (@integral_polyhedral_current_flat_supported R h2 d m Z hZ C (P+Q) hSum).
pose hCombination:=@flat_current_linear_combination R h2 d m Z hZ 1 P Q hPFlat hQFlat.
have hInput:(1:R)*:P+Q= P+Q by rewrite scale1r.
have hCongruence:=@current_flat_lipschitz_pushforward_congruence
  R h2 d n m Z U hZ hU f hImage hF
  ((1:R)*:P+Q) (P+Q) hCombination hSumFlat hInput.
have hLinear:=@current_flat_lipschitz_pushforward_linear
  R h2 d n m Z U hZ hU f hImage hF 1 P Q hPFlat hQFlat.
unfold polyhedral_lipschitz_image.
apply:(eq_trans (esym hCongruence));apply:(eq_trans hLinear).
by rewrite scale1r.
Qed.

(** Source for [rectifiable_common_source_image_sum]: two
    placed polyhedral image terms have one genuine
    original defining witness for their sum, retaining
    the exact target K, Federer 4.1.24, p. 380. *)
Theorem rectifiable_common_source_image_sum (P Q:CZ)
    (hP:@integral_polyhedral_current_class R h2 d m Z hZ C P)
    (hQ:@integral_polyhedral_current_class R h2 d m Z hZ C Q):
  @is_rectifiable_image_approximant R h2 n m U hU K
    (Image hP+Image hQ).
Proof.
pose hSum:=@integral_polyhedral_current_add R h2 d m Z hZ C P Q hP hQ.
exists d,Z,hZ,C,f,hImage,hLip,(P+Q),hSum;split;first exact:hCK.
exact:polyhedral_lipschitz_image_add.
Qed.
End RectifiableCommonSourceImages.
