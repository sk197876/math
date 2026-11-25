(** Federer (1969), 4.1.14, pp. 370–371: apply
    the original universal approximation law on the original
    source itself. Every original smooth approximation is
    allowed; no compact-closure or whole-source bound is
    required of the family. The identity pushforward
    supplies the printed source representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct LipschitzUP SmoothCompactSet SmoothCompactNeighbourhoods
  SmoothCompactSetExtensionality CurrentSpaces FlatCurrentsUP
  CurrentLipschitzCompactImage CurrentCompactLipschitzPushforwardUP
  CurrentSmoothApproximationUP CurrentCompactPushforwardAlgebra
  CurrentElementaryPushforwards CurrentOpenIdentitySmooth CurrentCompactMapProper
  CurrentPushforwardDataIndependence CurrentWeakSequenceLimit CurrentFlatSequenceLimitUP CurrentFlatSequenceLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentLipschitzImageOriginalApproximation.
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
Variable T:@current_space R h2 n U hU m.
Hypothesis hFlat:@is_flat_current_supported_in R h2 n m U hU K T.
Variable Q:@current_space R h2 nu V hV m.
Hypothesis hQ:@is_current_compact_lipschitz_image R h2 n nu m U V hU hV
  f hImage hLocal K T Q.
Variable g:nat->X->Y.
Hypothesis hG:@is_current_smooth_approximation R n nu U V K f g.
Local Notation hCompact:=(@flat_supported_current_compact R h2 n m U hU K T hFlat).

(** Source for [current_lipschitz_image_original_approximation_flat]:
    every original same-source smooth family converges in
    F_E for every compact target neighbourhood E of f(K),
    exactly as required in Federer 4.1.14, p. 370.
    No representation, normality or stronger family premise is added. *)
Theorem current_lipschitz_image_original_approximation_flat
    (E:smooth_compact_set hNY V)
    (hInside:forall x,smooth_compact_carrier K x->
      norm_domain_interior NY (smooth_compact_carrier E) (f x)):
  @is_current_flat_sequence_limit R h2 nu m V hV E
    (fun i=>@current_compact_map_pushforward R h2 n nu U V hU hV
      (g i) (current_smooth_approximation_image hG i)
      (current_smooth_approximation_class hG i) m T hCompact) Q.
Proof.
pose hUU:=fun x (hx:U x)=>hx.
pose hKU:=smooth_compact_in_domain K.
pose KU:=@current_compact_index_in_open R n U U K hKU.
have hIndex:KU=K by apply:smooth_compact_set_extensionality.
have hFlatU:@is_flat_current_supported_in R h2 n m U hU KU T by rewrite hIndex.
have hGU:@is_current_smooth_approximation R n nu U V KU f g by rewrite hIndex.
pose compU:=@flat_supported_current_compact R h2 n m U hU KU T hFlatU.
pose hId:=@current_open_identity_smooth R n U hU.
have hInclusion:=@current_compact_identity_pushforward R h2 n U hU m T compU hUU
  hId (@current_compact_map_proper R h2 n n m U U hU T (fun x:X=>x) hUU
    (norm_class_continuous (hId 0%N)) compU).
have hLimit:=hQ.2 E hInside U hU hUU hKU T hFlatU hInclusion g hGU.
pose P:=fun i=>@current_compact_map_pushforward R h2 n nu U V hU hV
  (g i) (current_smooth_approximation_image hGU i)
  (current_smooth_approximation_class hGU i) m T compU.
have hSame i:P i=@current_compact_map_pushforward R h2 n nu U V hU hV
    (g i) (current_smooth_approximation_image hG i)
    (current_smooth_approximation_class hG i) m T hCompact.
  exact:(@current_pushforward_data_independent R h2 n nu m U V hU hV T (g i)
    (current_smooth_approximation_image hGU i) (current_smooth_approximation_image hG i)
    (current_smooth_approximation_class hGU i) (current_smooth_approximation_class hG i) _ _).
move=>eps hEps.
have[N hN]:=@hLimit eps hEps.
exists N=>i hi;rewrite -(hSame i);exact:hN i hi.
Qed.

(** Source for [current_lipschitz_image_original_approximation_weak]:
    every original same-source smooth family converges weakly
    to any candidate satisfying the original image definition,
    supporting Federer 4.1.14, pp. 370–371. No
    representation or normality of the input or limit is needed. *)
Theorem current_lipschitz_image_original_approximation_weak:
  @is_current_weak_sequence_limit R h2 nu m V hV
    (fun i=>@current_compact_map_pushforward R h2 n nu U V hU hV
      (g i) (current_smooth_approximation_image hG i)
      (current_smooth_approximation_class hG i) m T hCompact) Q.
Proof.
pose fK:=@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K.
have[E hE]:=@smooth_compact_neighbourhood_exists R Y NY hNY nu
  (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV fK.
have hInside x (hx:smooth_compact_carrier K x):
    norm_domain_interior NY (smooth_compact_carrier E) (f x).
  apply:hE;by exists x.
exact:(@current_flat_sequence_limit_weak R h2 nu m V hV E _ Q
  (@current_lipschitz_image_original_approximation_flat E hInside)).
Qed.
End CurrentLipschitzImageOriginalApproximation.
