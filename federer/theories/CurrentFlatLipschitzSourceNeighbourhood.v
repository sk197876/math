(** Federer (1969), 4.1.14, pp. 370–371: the
    compact image is unchanged when its source is
    restricted to an open neighbourhood of the actual
    support. The original compact flat index is first
    localised inside that neighbourhood by 4.1.12,
    p. 368. It is not replaced by spt T. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates LipschitzUP SmoothCompactSet SmoothCompactNeighbourhoods
  CurrentSpaces CurrentSupportGeometry FlatCurrentsUP CurrentOpenRestriction
  CurrentLipschitzCompactImage CurrentCompactLipschitzPushforwardUP
  CurrentCompactSmoothApproximationUP CurrentCompactSmoothApproximation
  CurrentCompactSmoothApproximationOriginal CurrentSmoothApproximationUP
  CurrentApproximationOpenRestriction CurrentFlatOpenRestriction
  CurrentOpenRestrictionTransitive CurrentCompactPushforwardAlgebra
  CurrentPushforwardDataIndependence CurrentFlatSequenceLimits
  CurrentCompactLipschitzImageChosenApproximation CurrentWeakSequenceLimit
  CurrentFlatCompactIndexNeighbourhood CurrentFlatLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatLipschitzSourceNeighbourhood.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U W:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hW:forall x,W x->norm_domain_interior NX W x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Hypothesis hWU:forall x,W x->U x.
Arguments hWU : clear implicits.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Local Notation hImageW:=(fun x (hx:W x)=>hImage x (hWU x hx)).
Local Notation hLocalW:=(@metric_local_lipschitz_domain_restriction R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U W f hWU hLocal).
Local Notation Restrict:=(@current_open_restriction R h2 n m W U hW hU hWU).

(** Source for [current_compact_lipschitz_image_open_restriction]:
    compare two original defining images on one common
    smaller smooth family, Federer 4.1.14, pp. 370–371.
    The supplied K lies in W; no normality or
    finite mass of the original current is needed. *)
Theorem current_compact_lipschitz_image_open_restriction
    (K:smooth_compact_set hNX U)
    (hKW:smooth_compact_carrier K `<=` W)
    (T:@current_space R h2 n U hU m)
    (hT:@is_flat_current_supported_in R h2 n m U hU K T)
    (Q P:@current_space R h2 nu V hV m):
  @is_current_compact_lipschitz_image R h2 n nu m U V hU hV
    f hImage hLocal K T Q ->
  @is_current_compact_lipschitz_image R h2 n nu m W V hW hV
    f hImageW hLocalW (@current_compact_index_in_open R n U W K hKW)
    (Restrict T) P -> Q = P.
Proof.
move=>hQ hP.
pose KW:=@current_compact_index_in_open R n U W K hKW.
have hS:=@flat_current_open_restriction R h2 n m U W hU hW hWU K hKW T hT.
have[L [Z [g [hLeast hApprox]]]]:=
  @current_lipschitz_compact_smooth_approximation_exists R n nu
    W V hW hV KW f hLocalW hImageW.
pose hZ:=current_compact_smooth_domain_open hApprox.
pose hZW:=@current_compact_smooth_domain_in_domain R n nu W V KW f L Z g hApprox.
pose hZU:=fun x (hx:Z x)=>hWU x (hZW x hx).
pose hKZ:=fun x (hx:smooth_compact_carrier K x)=>
  current_compact_smooth_domain_contains hApprox hx.
pose KZ:=@current_compact_index_in_open R n U Z K hKZ.
pose SZ:=@current_open_restriction R h2 n m Z U hZ hU hZU T.
pose hSZ:=@flat_current_open_restriction R h2 n m U Z hU hZ hZU K hKZ T hT.
pose compactSZ:=@flat_supported_current_compact R h2 n m Z hZ KZ SZ hSZ.
pose hGW:=@current_compact_smooth_original_approximation R n nu
  W V KW f L Z g hApprox.
have hGU:@is_current_smooth_approximation R n nu Z V KZ f g.
  constructor.
  - exact:current_smooth_approximation_image hGW.
  - exact:current_smooth_approximation_class hGW.
  - exact:current_smooth_approximation_bound hGW.
  - exact:current_smooth_approximation_uniform hGW.
pose u:=fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
  (g i) (current_smooth_approximation_image hGU i)
  (current_smooth_approximation_class hGU i) m SZ compactSZ.
pose fK:=@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K.
have[E hE]:=@smooth_compact_neighbourhood_exists R Y NY hNY nu
  (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV fK.
have hInside x (hx:smooth_compact_carrier K x):
    norm_domain_interior NY (smooth_compact_carrier E) (f x).
  apply:hE;by exists x.
have hRecovery:=@flat_current_neighbourhood_inclusion_recovery R h2 n m
  U Z hU hZ hZU K hKZ T hT compactSZ.
have hLimitQ:=hQ.2 E hInside Z hZ hZU hKZ SZ hSZ hRecovery g hGU.
have hLimitP:=@current_compact_lipschitz_image_chosen_approximation R h2
  n nu m W V hW hV f hImageW hLocalW KW (Restrict T) hS P hP
  L Z g hApprox E hInside.
pose SZW:=@current_open_restriction R h2 n m Z W hZ hW hZW (Restrict T).
have hTransitive:SZW=SZ.
  exact:(@current_open_restriction_transitive R h2 n m Z W U
    hZ hW hU hZW hWU hZU T).
pose KZW:=@current_compact_index_in_open R n W Z KW
  (current_compact_smooth_domain_contains hApprox).
pose hSZW:=@flat_current_open_restriction R h2 n m W Z hW hZ hZW KW
  (current_compact_smooth_domain_contains hApprox) (Restrict T) hS.
pose compactSZW:=@flat_supported_current_compact R h2 n m Z hZ KZW SZW hSZW.
have hSequence:(fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
    (g i) (current_smooth_approximation_image hGW i)
    (current_smooth_approximation_class hGW i) m SZW compactSZW)=u.
  apply:funext=>i.
  have hEqual:=@current_compact_map_pushforward_congruence R h2 n nu Z V hZ hV
    (g i) (current_smooth_approximation_image hGW i)
    (current_smooth_approximation_class hGW i) m SZW SZ compactSZW compactSZ hTransitive.
  rewrite hEqual /u /current_compact_map_pushforward.
  exact:current_pushforward_data_independent.
rewrite hSequence in hLimitP.
exact:(@current_weak_sequence_limit_unique R h2 nu m V hV u Q P
  (@current_flat_sequence_limit_weak R h2 nu m V hV E u Q hLimitQ)
  (@current_flat_sequence_limit_weak R h2 nu m V hV E u P hLimitP)).
Qed.

(** Source for [current_flat_lipschitz_pushforward_open_restriction]:
    restriction to an original support neighbourhood does
    not change the compact flat image, Federer 4.1.14,
    p. 371. Only spt T must lie in W;
    the original flat index need not lie there.
    The restricted membership evidence is arbitrary. *)
Theorem current_flat_lipschitz_pushforward_open_restriction
    (T:@current_space R h2 n U hU m)
    (hT:@is_flat_current R h2 n m U hU T)
    (hSupport:@current_support R h2 n U hU m T `<=` W)
    (hS:@is_flat_current R h2 n m W hW (Restrict T)):
  @CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
    f hImage hLocal T hT=
  @CurrentFlatLipschitzPushforward.value R h2 n nu m W V hW hV
    f hImageW hLocalW (Restrict T) hS.
Proof.
have[K hKT]:=hT.
have[L [hLW hTL]]:=@flat_current_compact_index_neighbourhood R h2 n m
  U W hU hW K T hKT hSupport.
pose LW:=@current_compact_index_in_open R n U W L hLW.
have hSL:=@flat_current_open_restriction R h2 n m U W hU hW hWU L hLW T hTL.
exact:(@current_compact_lipschitz_image_open_restriction L hLW T hTL _ _
  ((@CurrentFlatLipschitzPushforward.laws R h2 n nu m U V hU hV
    f hImage hLocal T hT).2 L hTL)
  ((@CurrentFlatLipschitzPushforward.laws R h2 n nu m W V hW hV
    f hImageW hLocalW (Restrict T) hS).2 LW hSL)).
Qed.
End CurrentFlatLipschitzSourceNeighbourhood.
