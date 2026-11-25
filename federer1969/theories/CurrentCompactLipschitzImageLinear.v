(** Federer (1969), 4.1.14, pp. 370–371: compact
    Lipschitz images preserve real linear combinations.
    Test every candidate on one common original smooth
    family, use the earlier smooth linearity, and pass
    to the original weak limits. No mass or normality
    hypothesis is needed for this compatibility law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom Bilinear ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates LipschitzUP SmoothCompactSet SmoothCompactNeighbourhoods
  CurrentSpaces FlatCurrentsUP FlatCurrentClosure CurrentOpenRestriction CurrentLipschitzCompactImage
  CurrentCompactLipschitzPushforwardUP CurrentCompactSmoothApproximationUP
  CurrentCompactSmoothApproximation CurrentCompactSmoothApproximationOriginal
  CurrentFlatOpenRestriction CurrentCompactPushforwardAlgebra
  CurrentCompactLipschitzImageChosenApproximation CurrentFlatSequenceLimits
  CurrentWeakSequenceLimit CurrentWeakSequenceLinear CurrentSmoothApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactLipschitzImageLinear.
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
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation D:=(@current_space R h2 nu V hV m).
Local Notation Flat:=(@is_flat_current_supported_in R h2 n m U hU K).
Local Notation Image:=(@is_current_compact_lipschitz_image R h2 n nu m U V hU hV
  f hImage hLocal K).

(** Source for [current_compact_lipschitz_image_linear]: the
    original compact image is linear, Federer 4.1.14,
    pp. 370–371. Fixed-K flat membership supplies all
    actual restricted representatives; their normality and
    finite mass are not assumed. *)
Theorem current_compact_lipschitz_image_linear c (T S:C) (Q P A:D):
  Flat T->Flat S->
  Image T Q->Image S P->Image (c*:T+S) A->A=c*:Q+P.
Proof.
move=>hT hS hQ hP hA.
have hTSub:(@flat_current_subspace R h2 n m U hU K) T:=hT.
have hSSub:(@flat_current_subspace R h2 n m U hU K) S:=hS.
have hCombination:Flat (c*:T+S).
  exact:subspace_add (subspace_scale c hTSub) hSSub.
have[L [Z [g [hLeast hApprox]]]]:=
  @current_lipschitz_compact_smooth_approximation_exists R n nu
    U V hU hV K f hLocal hImage.
pose hZ:=current_compact_smooth_domain_open hApprox.
pose hZU:=@current_compact_smooth_domain_in_domain R n nu U V K f L Z g hApprox.
pose hKZ:=current_compact_smooth_domain_contains hApprox.
pose KZ:=@current_compact_index_in_open R n U Z K hKZ.
pose restriction:=@current_open_restriction R h2 n m Z U hZ hU hZU.
pose hG:=@current_compact_smooth_original_approximation R n nu U V K f L Z g hApprox.
pose hRT:=@flat_current_open_restriction R h2 n m U Z hU hZ hZU K hKZ T hT.
pose hRS:=@flat_current_open_restriction R h2 n m U Z hU hZ hZU K hKZ S hS.
pose hRC:=@flat_current_open_restriction R h2 n m U Z hU hZ hZU K hKZ
  (c*:T+S) hCombination.
pose compT:=@flat_supported_current_compact R h2 n m Z hZ KZ (restriction T) hRT.
pose compS:=@flat_supported_current_compact R h2 n m Z hZ KZ (restriction S) hRS.
pose compC:=@flat_supported_current_compact R h2 n m Z hZ KZ (restriction (c*:T+S)) hRC.
pose push:=fun i X hX=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
  (g i) (current_smooth_approximation_image hG i)
  (current_smooth_approximation_class hG i) m X hX.
pose u:=fun i=>push i (restriction T) compT.
pose v:=fun i=>push i (restriction S) compS.
pose w:=fun i=>push i (restriction (c*:T+S)) compC.
pose fK:=@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K.
have[E hE]:=@smooth_compact_neighbourhood_exists R Y NY hNY nu
  (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV fK.
have hInside x (hx:smooth_compact_carrier K x):
    norm_domain_interior NY (smooth_compact_carrier E) (f x).
  apply:hE;by exists x.
have hUWeak:=@current_flat_sequence_limit_weak R h2 nu m V hV E u Q
  (@current_compact_lipschitz_image_chosen_approximation R h2 n nu m U V hU hV
    f hImage hLocal K T hT Q hQ L Z g hApprox E hInside).
have hVWeak:=@current_flat_sequence_limit_weak R h2 nu m V hV E v P
  (@current_compact_lipschitz_image_chosen_approximation R h2 n nu m U V hU hV
    f hImage hLocal K S hS P hP L Z g hApprox E hInside).
have hWWeak:=@current_flat_sequence_limit_weak R h2 nu m V hV E w A
  (@current_compact_lipschitz_image_chosen_approximation R h2 n nu m U V hU hV
    f hImage hLocal K (c*:T+S) hCombination A hA L Z g hApprox E hInside).
have hRestricted:restriction (c*:T+S)=c*:restriction T+restriction S:=linearP restriction c T S.
have hCompactCombination:@compact (real_norm_metric_space hNX)
    (@current_support R h2 n Z hZ m (c*:restriction T+restriction S)).
  by rewrite -hRestricted;exact:compC.
have hImages i:w i=c*:u i+v i.
  have hEqual:=@current_compact_map_pushforward_congruence R h2 n nu Z V hZ hV
    (g i) (current_smooth_approximation_image hG i)
    (current_smooth_approximation_class hG i) m
    (restriction (c*:T+S)) (c*:restriction T+restriction S) compC
    hCompactCombination hRestricted.
  rewrite /w /push hEqual.
  exact:(@current_compact_map_pushforward_linear R h2 n nu Z V hZ hV
    (g i) (current_smooth_approximation_image hG i)
    (current_smooth_approximation_class hG i) m c
    (restriction T) (restriction S) compT compS hCompactCombination).
have hSequence:w=(fun i=>c*:u i+v i) by apply:funext=>i;exact:hImages i.
rewrite hSequence in hWWeak.
exact:(@current_weak_sequence_limit_unique R h2 nu m V hV _ A (c*:Q+P)
  hWWeak (@current_weak_sequence_limit_linear R h2 nu m V hV u v Q P c hUWeak hVWeak)).
Qed.
End CurrentCompactLipschitzImageLinear.
