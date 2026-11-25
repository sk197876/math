(** Federer (1969), 4.1.14, p. 371: the original
    compact image is independent of enlarging the source
    compact index. Every printed flat representative is
    the actual restriction; the same smooth family may
    therefore be tested with the smaller original index. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct LipschitzUP SmoothCompactSet CurrentSpaces
  FlatCurrentsUP CurrentLipschitzCompactImage CurrentCompactLipschitzPushforwardUP
  CurrentCompactLipschitzImageUniqueness CurrentSmoothApproximationUP
  CurrentSmoothApproximationCompactMonotone CurrentFlatCompactMonotone
  CurrentFlatNeighbourhoodRepresentative CurrentFlatOpenRestriction
  CurrentCompactPushforwardAlgebra CurrentPushforwardDataIndependence
  CurrentOpenRestriction CurrentOpenIdentitySmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactLipschitzImageCompactMonotone.
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
Variables K L:smooth_compact_set hNX U.
Hypothesis hKL:smooth_compact_carrier K `<=` smooth_compact_carrier L.
Arguments hKL : clear implicits.
Local Notation fK:=(@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K).
Local Notation fL:=(@current_lipschitz_compact_image R n nu U V hU f hImage hLocal L).

(** Source for [current_compact_lipschitz_image_compact_mono]:
    a compact image for K also satisfies the original
    defining law for every larger compact index L,
    Federer 4.1.14, p. 371. No extra flat membership
    of the arbitrary printed representative is assumed;
    its smaller-index membership is derived by restriction. *)
Theorem current_compact_lipschitz_image_compact_mono
    (T:@current_space R h2 n U hU m)
    (hFlat:@is_flat_current_supported_in R h2 n m U hU K T)
    (Q:@current_space R h2 nu V hV m):
  @is_current_compact_lipschitz_image R h2 n nu m U V hU hV
    f hImage hLocal K T Q ->
  @is_current_compact_lipschitz_image R h2 n nu m U V hU hV
    f hImage hLocal L T Q.
Proof.
move=>hQ;split.
- apply:(@flat_current_compact_monotone R h2 nu m V hV fK fL _ Q hQ.1).
  move=>y [x hx <-];exists x;[exact:hKL x hx|by []].
- move=>E hInterior Z hZ hZU hLZ S hS hInclusion g hG.
  pose hKZ:=fun x (hx:smooth_compact_carrier K x)=>hLZ x (hKL x hx).
  pose KZ:=@current_compact_index_in_open R n U Z K hKZ.
  pose LZ:=@current_compact_index_in_open R n U Z L hLZ.
  have hSIdentity:S=@current_open_restriction R h2 n m Z U hZ hU hZU T.
    exact:(@current_flat_representative_is_open_restriction R h2 n m U Z
      hU hZ hZU L hLZ T S hS hInclusion).
  have hSK:@is_flat_current_supported_in R h2 n m Z hZ KZ S.
    rewrite hSIdentity.
    exact:(@flat_current_open_restriction R h2 n m U Z hU hZ hZU K hKZ T hFlat).
  pose compK:=@flat_supported_current_compact R h2 n m Z hZ KZ S hSK.
  pose compL:=@flat_supported_current_compact R h2 n m Z hZ LZ S hS.
  have hInclusionK:@current_compact_map_pushforward R h2 n n Z U hZ hU
      (fun x:X=>x) hZU (@current_open_identity_smooth R n Z hZ) m S compK=T.
    have hEqual:=@current_compact_map_pushforward_congruence R h2 n n Z U hZ hU
      (fun x:X=>x) hZU (@current_open_identity_smooth R n Z hZ)
      m S S compK compL (erefl S).
    exact:eq_trans hEqual hInclusion.
  have hIndex: smooth_compact_carrier KZ `<=` smooth_compact_carrier LZ:=hKL.
  pose hGK:=@current_smooth_approximation_compact_mono R n nu Z V KZ LZ hIndex f g hG.
  have hInsideK x (hx:smooth_compact_carrier K x):
      norm_domain_interior NY (smooth_compact_carrier E) (f x):=hInterior x (hKL x hx).
  have hLimit:=hQ.2 E hInsideK Z hZ hZU hKZ S hSK hInclusionK g hGK.
  have hImages i:@current_compact_map_pushforward R h2 n nu Z V hZ hV
      (g i) (current_smooth_approximation_image hGK i)
      (current_smooth_approximation_class hGK i) m S compK=
      @current_compact_map_pushforward R h2 n nu Z V hZ hV
      (g i) (current_smooth_approximation_image hG i)
      (current_smooth_approximation_class hG i) m S compL.
    exact:(@current_pushforward_data_independent R h2 n nu m Z V hZ hV S (g i)
      (current_smooth_approximation_image hGK i) (current_smooth_approximation_image hG i)
      (current_smooth_approximation_class hGK i) (current_smooth_approximation_class hG i) _ _).
  have hSequence:(fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
      (g i) (current_smooth_approximation_image hGK i)
      (current_smooth_approximation_class hGK i) m S compK)=
      (fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
      (g i) (current_smooth_approximation_image hG i)
      (current_smooth_approximation_class hG i) m S compL).
    by apply:funext=>i;exact:hImages i.
  by rewrite hSequence in hLimit.
Qed.
End CurrentCompactLipschitzImageCompactMonotone.
