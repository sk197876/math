(** Federer (1969), 4.1.23, p. 379:
    reduce a normal current on its original
    open U to the whole Euclidean space
    without increasing mass or changing its support
    index. The original restriction recovers the current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormRegularityOperations NormClassOneUP
  NormLocalLipschitzScalarProduct NormOpenDomainLaws InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP CurrentSpaces NormalCurrentsUP SmoothCompactSet
  SmoothCompactSetExtensionality FlatCurrentsUP FlatCurrentFinite
  CurrentLipschitzCompactImage CurrentNormalLipschitzImageExistence
  CurrentNormalLipschitzMassBound CurrentCompactLipschitzPushforwardSmooth
  CompactRepresentedCurrentMass CurrentCompactMapProper
  CurrentCompactPushforwardAlgebra CurrentCompactInclusionRestriction
  CurrentOpenIdentitySmooth CurrentOpenRestriction CurrentMassSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normal_current_ambient_inclusion]: the
    original-open reduction in Federer 4.1.23,
    p. 379, by the normal pushforward,
    sharp identity-map mass bound and exact inclusion/
    restriction laws of 4.1.7 and 4.1.14.
    Empty U and K, n=0 and every
    degree are retained. No new finite-mass premise
    is needed for an original normal current. *)
Theorem normal_current_ambient_inclusion (R : realType)
    (h2 : (1+1:R)!=0) n m (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K : smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T : @current_space R h2 n U hU m)
    (hNormal : @normal_currents_supported_in R h2 n U hU m K T) :
  let Full := fun _ : R_n R n => True in
  let hFull := fun (x : R_n R n) (_ : True) =>
    norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x in
  let KF := @current_compact_index_in_open R n U Full K (fun _ _ => Logic.I) in
  exists Q : @current_space R h2 n Full hFull m,
    @normal_currents_supported_in R h2 n Full hFull m KF Q /\
    @current_open_restriction R h2 n m U Full hU hFull (fun _ _ => Logic.I) Q=T /\
    (@CurrentMass.value R h2 n m Full hFull Q<=
      @CurrentMass.value R h2 n m U hU T)%E.
Proof.
move=> Full hFull KF.
pose X := R_n R n.
pose NX := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
pose idX := fun x : X => x.
pose image := fun (x : X) (_ : U x) => Logic.I.
pose hId := @current_open_identity_smooth R n U hU.
have hLocal : @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNX) U idX.
  apply: (@norm_class_one_locally_metric_lipschitz R X X NX NX hNX hNX U idX).
  apply: ((@norm_class_firstP R X X NX NX hNX hNX U idX).1).
  exact: hId 1%N.
have [Q [hNQ hQ]] := @current_normal_lipschitz_image_exists R h2 n n m
  U Full hU hFull idX image hLocal K T hNormal.1 hNormal.2.
pose fK := @current_lipschitz_compact_image R n n U Full hU idX image hLocal K.
have hIndex : fK=KF.
  apply: smooth_compact_set_extensionality.
  rewrite current_lipschitz_compact_image_carrier.
  apply/seteqP; split.
  - by move=> x [y hy <-].
  - move=> x hx; by exists x.
have hFlat := @supported_normal_current_is_flat R h2 n m U hU K T hNormal.
have hFinite := @compact_represented_current_finite_mass R h2 n m U hU
  T hNormal.1.1.1 hNormal.1.2.
have hBound : @is_metric_lipschitz_bound R (real_norm_metric_space hNX)
    (real_norm_metric_space hNX) (smooth_compact_carrier K) idX 1.
  split; first exact: ler01.
  by move=> x y _ _; rewrite mul1r.
have hMass := @current_flat_lipschitz_image_mass_bound R h2 n n m U Full hU hFull
  idX image hLocal K T Q 1 hFlat hFinite hQ hBound.
rewrite expr1n mul1e in hMass.
have hSmooth := @current_compact_lipschitz_image_smooth R h2 n n m
  U Full hU hFull idX image hLocal K T hFlat hId Q hQ.
have hRecovery : @current_open_restriction R h2 n m U Full hU hFull image Q=T.
  rewrite hSmooth.
  exact: (@current_compact_inclusion_restriction R h2 n U Full hU hFull image
    m T (@flat_supported_current_compact R h2 n m U hU K T hFlat) hId
    (@current_compact_map_proper R h2 n n m U Full hU T idX image
      (norm_class_continuous (hId 0%N))
      (@flat_supported_current_compact R h2 n m U hU K T hFlat))).
have hQFlat : @is_flat_current_supported_in R h2 n m Full hFull KF Q.
  have h : @is_flat_current_supported_in R h2 n m Full hFull fK Q := hQ.1.
  by rewrite hIndex in h.
exists Q; split.
- split; first exact: hNQ.
  exact: (@flat_current_supported_support R h2 n m Full hFull KF Q hQFlat).
split; [exact: hRecovery|exact: hMass].
Qed.
