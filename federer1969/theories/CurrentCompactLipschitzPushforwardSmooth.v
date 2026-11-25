(** Federer (1969), 4.1.14, pp. 370–371: the
    Lipschitz image agrees with the earlier smooth
    image whenever f is smooth. The constant family
    g_i=f satisfies the literal defining condition;
    compactness supplies its K-only derivative bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormClassOneUP NormCompactFunctionBound InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates EuclideanHomOperator
  LipschitzUP SmoothCompactSet SmoothCompactSetExtensionality SmoothCompactNeighbourhoods
  CurrentSpaces CurrentCompactMapProper FlatCurrentsUP CurrentLipschitzCompactImage CurrentCompactLipschitzPushforwardUP
  CurrentSmoothApproximationUP CurrentMapDifferential CurrentMapDifferentialNormContinuity
  CurrentOpenIdentitySmooth CurrentElementaryPushforwards CurrentCompactMapProper
  CurrentCompactPushforwardAlgebra CurrentPushforwardDataIndependence
  CurrentFlatSequenceLimitUP CurrentFlatSequenceLimits CurrentCompactLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactLipschitzPushforwardSmooth.
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
Arguments hImage : clear implicits.
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable K:smooth_compact_set hNX U.
Variable T:@current_space R h2 n U hU m.
Hypothesis hFlat:@is_flat_current_supported_in R h2 n m U hU K T.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation hCompact:=(@flat_supported_current_compact R h2 n m U hU K T hFlat).
Local Notation Push:=(@current_compact_map_pushforward R h2 n nu U V hU hV
  f hImage hf m T hCompact).

(** Source for [current_compact_lipschitz_image_smooth]:
    every candidate satisfying the original definition
    equals the original smooth image when f is smooth,
    Federer 4.1.14, pp. 370–371. A constant sequence
    is permitted, including empty K and degree zero. *)
Theorem current_compact_lipschitz_image_smooth
    (Q:@current_space R h2 nu V hV m):
  @is_current_compact_lipschitz_image R h2 n nu m U V hU hV
    f hImage hLocal K T Q ->Q=Push.
Proof.
move=>hQ.
pose hUU:=fun x (hx:U x)=>hx.
pose hKU:=smooth_compact_in_domain K.
pose KU:=@current_compact_index_in_open R n U U K hKU.
have hIndex:KU=K by apply:smooth_compact_set_extensionality.
have hFlatU:@is_flat_current_supported_in R h2 n m U hU KU T by rewrite hIndex.
pose compU:=@flat_supported_current_compact R h2 n m U hU KU T hFlatU.
pose hId:=@current_open_identity_smooth R n U hU.
have hInclusion:=@current_compact_identity_pushforward R h2 n U hU m T compU hUU
  hId (@current_compact_map_proper R h2 n n m U U hU T (fun x:X=>x) hUU
    (norm_class_continuous (hId 0%N)) compU).
pose OP:=@euclidean_operator_norm R n nu.
pose DF:=@current_map_differential R n nu U f.
have hDF:=@current_class_one_differential_continuous R n nu U f (hf 1%N).
have[M [hM hBound]]:=@norm_class_zero_compact_bounded R X (Hom X Y) NX OP
  hNX (@euclidean_operator_norm_is_norm R n nu) U (smooth_compact_carrier K) DF
  (smooth_compact_is_compact K) (smooth_compact_in_domain K) hDF.
have hG:@is_current_smooth_approximation R n nu U V KU f (fun _=>f).
  constructor.
  - move=>i x hx;exact:hImage x hx.
  - by move=>i.
  - exists M;split;first exact:ltW hM.
    move=>i x hx;exact:hBound x hx.
  - move=>epsilon hEpsilon;exists 0%N=>i _ x hx.
    by rewrite subrr (real_seminorm_zero hNY.1).
pose fK:=@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K.
have[E hE]:=@smooth_compact_neighbourhood_exists R Y NY hNY nu
  (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV fK.
have hInside x (hx:smooth_compact_carrier K x):
    norm_domain_interior NY (smooth_compact_carrier E) (f x).
  apply:hE;by exists x.
have hLimit:=hQ.2 E hInside U hU hUU hKU T hFlatU hInclusion (fun _=>f) hG.
have hEndpoint i:@current_compact_map_pushforward R h2 n nu U V hU hV f
    (current_smooth_approximation_image hG i)
    (current_smooth_approximation_class hG i) m T compU=Push.
  exact:(@current_pushforward_data_independent R h2 n nu m U V hU hV T f
    (current_smooth_approximation_image hG i) hImage
    (current_smooth_approximation_class hG i) hf _ _).
have hSequence:(fun i=>@current_compact_map_pushforward R h2 n nu U V hU hV f
    (current_smooth_approximation_image hG i)
    (current_smooth_approximation_class hG i) m T compU)=(fun _:nat=>Push).
  by apply:funext=>i;exact:hEndpoint i.
rewrite hSequence in hLimit.
exact:(@current_flat_sequence_limit_unique R h2 nu m V hV E (fun _=>Push) Q Push
  hLimit (@current_flat_sequence_limit_constant R h2 nu m V hV E Push)).
Qed.

(** Source for [current_compact_lipschitz_pushforward_smooth]:
    the actual sealed Lipschitz operator restricts to
    the original smooth image, Federer 4.1.14,
    pp. 370–371. Only its independent laws are used. *)
Theorem current_compact_lipschitz_pushforward_smooth:
  @CurrentCompactLipschitzPushforward.value R h2 n nu m U V hU hV f hImage hLocal
    K T hFlat=Push.
Proof.
apply:current_compact_lipschitz_image_smooth.
exact:(@CurrentCompactLipschitzPushforward.laws R h2 n nu m U V hU hV f hImage hLocal
  K T hFlat).
Qed.
End CurrentCompactLipschitzPushforwardSmooth.
