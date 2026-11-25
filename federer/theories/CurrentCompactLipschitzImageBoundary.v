(** Federer (1969), 4.1.14, p. 371: the compact
    Lipschitz image commutes with the positive-degree
    boundary. Use one original smooth approximation,
    the preceding smooth boundary formula and continuity
    of boundary on original tests. The degree-zero
    exception introduces no negative-degree current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates LipschitzUP SmoothCompactSet
  SmoothCompactNeighbourhoods CurrentSpaces CurrentBoundary FlatCurrentsUP FlatCurrentBoundary
  CurrentOpenRestriction CurrentOpenRestrictionBoundary CurrentLipschitzCompactImage
  CurrentCompactLipschitzPushforwardUP CurrentCompactSmoothApproximationUP
  CurrentCompactSmoothApproximation CurrentCompactSmoothApproximationOriginal
  CurrentFlatOpenRestriction CurrentCompactPushforwardAlgebra CurrentCompactMapProper
  CurrentPushforwardBoundary CurrentPushforwardCongruence
  CurrentCompactLipschitzImageChosenApproximation CurrentFlatSequenceLimits
  CurrentWeakSequenceLimit CurrentWeakLimitOperations CurrentSmoothApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactLipschitzImageBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu d:nat.
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
Local Notation bd:=(@current_boundary R h2 n d U hU).
Local Notation targetBd:=(@current_boundary R h2 nu d V hV).

(** Source for [current_compact_lipschitz_image_boundary]:
    boundary(f#T)=f#(boundary T), Federer 4.1.14,
    p. 371. Both candidates satisfy the original defining
    approximation law; no normality or finite-mass
    premise is imposed on T or its boundary. *)
Theorem current_compact_lipschitz_image_boundary
    (T:@current_space R h2 n U hU d.+1)
    (hFlat:@is_flat_current_supported_in R h2 n d.+1 U hU K T)
    (Q:@current_space R h2 nu V hV d.+1)
    (P:@current_space R h2 nu V hV d):
  @is_current_compact_lipschitz_image R h2 n nu d.+1 U V hU hV
    f hImage hLocal K T Q ->
  @is_current_compact_lipschitz_image R h2 n nu d U V hU hV
    f hImage hLocal K (bd T) P ->targetBd Q = P.
Proof.
move=>hQ hP.
pose hBoundaryFlat:=@flat_current_boundary_supported R h2 n d U hU K T hFlat.
have[L [Z [g [hLeast hApprox]]]]:=
  @current_lipschitz_compact_smooth_approximation_exists R n nu
    U V hU hV K f hLocal hImage.
pose hZ:=current_compact_smooth_domain_open hApprox.
pose hZU:=@current_compact_smooth_domain_in_domain R n nu U V K f L Z g hApprox.
pose hKZ:=current_compact_smooth_domain_contains hApprox.
pose KZ:=@current_compact_index_in_open R n U Z K hKZ.
pose S:=@current_open_restriction R h2 n d.+1 Z U hZ hU hZU T.
pose B:=@current_open_restriction R h2 n d Z U hZ hU hZU (bd T).
pose hS:=@flat_current_open_restriction R h2 n d.+1 U Z hU hZ hZU K hKZ T hFlat.
pose hB:=@flat_current_open_restriction R h2 n d U Z hU hZ hZU K hKZ (bd T) hBoundaryFlat.
pose compS:=@flat_supported_current_compact R h2 n d.+1 Z hZ KZ S hS.
pose compB:=@flat_supported_current_compact R h2 n d Z hZ KZ B hB.
pose hG:=@current_compact_smooth_original_approximation R n nu U V K f L Z g hApprox.
pose u:=fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
  (g i) (current_smooth_approximation_image hG i)
  (current_smooth_approximation_class hG i) d.+1 S compS.
pose v:=fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
  (g i) (current_smooth_approximation_image hG i)
  (current_smooth_approximation_class hG i) d B compB.
pose fK:=@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K.
have[E hE]:=@smooth_compact_neighbourhood_exists R Y NY hNY nu
  (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV fK.
have hInside x (hx:smooth_compact_carrier K x):
    norm_domain_interior NY (smooth_compact_carrier E) (f x).
  apply:hE;by exists x.
have hUWeak:=@current_flat_sequence_limit_weak R h2 nu d.+1 V hV E u Q
  (@current_compact_lipschitz_image_chosen_approximation R h2 n nu d.+1 U V hU hV
    f hImage hLocal K T hFlat Q hQ L Z g hApprox E hInside).
have hVWeak:=@current_flat_sequence_limit_weak R h2 nu d V hV E v P
  (@current_compact_lipschitz_image_chosen_approximation R h2 n nu d U V hU hV
    f hImage hLocal K (bd T) hBoundaryFlat P hP L Z g hApprox E hInside).
have hRestrict:B=@current_boundary R h2 n d Z hZ S.
  exact:(@current_open_restriction_boundary R h2 n d Z U hZ hU hZU T).
have hImages i:targetBd (u i)=v i.
  pose fi:=g i.
  pose hFI:=current_smooth_approximation_image hG i.
  pose hFS:=current_smooth_approximation_class hG i.
  pose hProper:=@current_compact_map_proper R h2 n nu d.+1 Z V hZ S fi hFI
    (norm_class_continuous (hFS 0%N)) compS.
  have hCommute:=@current_pushforward_boundary R h2 n nu d Z V hZ hV
    S fi hFI hFS hProper.
  apply:(eq_trans hCommute).
  exact:(@current_pushforward_current_congruence R h2 n nu d Z V hZ hV
    fi hFI hFS (@current_boundary R h2 n d Z hZ S) B _ _ (esym hRestrict)).
have hSequence:(fun i=>targetBd (u i))=v by apply:funext=>i;exact:hImages i.
have hBoundaryWeak:=@current_weak_limit_boundary R h2 nu d V hV u Q hUWeak.
rewrite hSequence in hBoundaryWeak.
exact:(@current_weak_sequence_limit_unique R h2 nu d V hV v
  (targetBd Q) P hBoundaryWeak hVWeak).
Qed.
End CurrentCompactLipschitzImageBoundary.
