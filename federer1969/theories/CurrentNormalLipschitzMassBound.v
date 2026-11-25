(** Federer (1969), 4.1.14, p. 370: the sharp mass estimate
    follows by extending f restricted to K with its least
    Lipschitz constant, smoothing and passing to the weak limit.
    The same proof works for every finite-mass flat input.
    The candidate image is specified by the original universal
    approximation law; no selected pushforward is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct LipschitzUP LipschitzConstant
  OpenLocalLipschitzCompact SmoothCompactSet SmoothCompactInteriorThickening
  CurrentSpaces CurrentOpenRestriction CurrentOpenRestrictionSupport
  CurrentOpenRestrictionMass CurrentMassSealed CurrentMassBasic CurrentMassWeakLowerLimit
  CurrentFiniteMassRepresentation CompactRepresentedCurrentMass
  CurrentCompactMapProper CurrentCompactPushforwardAlgebra
  CurrentOpenIdentitySmooth CurrentLipschitzCompactImage
  FlatCurrentsUP FlatCurrentFinite NormalCurrentsUP
  CurrentFlatOpenRestriction CurrentFlatSequenceLimits
  CurrentCompactLipschitzPushforwardUP CurrentSmoothApproximationUP
  CurrentSmoothPushforwardMassBound
  CurrentCompactSmoothApproximationUP CurrentCompactSmoothApproximationSealed
  CurrentCompactSmoothApproximationOriginal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentNormalLipschitzMassBound.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n nu m : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Variables (U : set X) (V : set Y).
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Hypothesis hV : forall y, V y -> norm_domain_interior NY V y.
Variable f : X -> Y.
Hypothesis hImage : forall x, U x -> V (f x).
Hypothesis hLocal : @is_locally_metric_lipschitz R XT YT U f.
Variable K : smooth_compact_set hNX U.
Local Notation fK := (@current_lipschitz_compact_image R n nu U V hU
  f hImage hLocal K).
Local Notation CU := (@current_space R h2 n U hU m).
Local Notation CV := (@current_space R h2 nu V hV m).
Local Notation MU := (@CurrentMass.value R h2 n m U hU).
Local Notation MV := (@CurrentMass.value R h2 nu m V hV).
Local Notation Image := (@is_current_compact_lipschitz_image R h2 n nu m
  U V hU hV f hImage hLocal K).

(** Source for [current_flat_lipschitz_image_mass_bound]: the
    sharp smoothing argument of Federer 4.1.14, p. 370,
    applies to every original flat input with finite mass.
    A bound only on f restricted to K suffices, including
    L=0 and degree zero. No normality of T or its image is
    assumed in this supporting extension of the printed proof. *)
Theorem current_flat_lipschitz_image_mass_bound (T : CU) (Q : CV) (L : R) :
  @is_flat_current_supported_in R h2 n m U hU K T ->
  (MU T < +oo)%E -> Image T Q ->
  @is_metric_lipschitz_bound R XT YT (smooth_compact_carrier K) f L ->
  (MV Q <= (L^+m)%:E*MU T)%E.
Proof.
move=> hFlat hFinite hQ hBoundK.
have hImageK : forall x, smooth_compact_carrier K x -> V (f x).
  move=> x hx; exact: @hImage x (smooth_compact_in_domain K x hx).
pose data := @CurrentCompactSmoothApproximation.value R n nu U V hU hV
  K f L hBoundK hImageK.
pose hApprox := @CurrentCompactSmoothApproximation.laws R n nu U V hU hV
  K f L hBoundK hImageK.
pose Z := data.1.
pose g := data.2.
pose hZ := current_compact_smooth_domain_open hApprox.
pose hKZ := current_compact_smooth_domain_contains hApprox.
pose hZU := @current_compact_smooth_domain_in_domain R n nu U V K f L Z g hApprox.
pose KZ := @current_compact_index_in_open R n U Z K hKZ.
pose S := @current_open_restriction R h2 n m Z U hZ hU hZU T.
have hSFlat : @is_flat_current_supported_in R h2 n m Z hZ KZ S :=
  @flat_current_open_restriction R h2 n m U Z hU hZ hZU K hKZ T hFlat.
pose hCompact := @flat_supported_current_compact R h2 n m Z hZ KZ S hSFlat.
have hRecovery := @flat_current_neighbourhood_inclusion_recovery R h2 n m
  U Z hU hZ hZU K hKZ T hFlat hCompact.
have hG := @current_compact_smooth_original_approximation R n nu
  U V K f L Z g hApprox.
have [radius [hRadius [E [hImageE hTube]]]] :=
  @smooth_compact_interior_thickening R Y NY hNY nu
    (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV fK.
have hInterior : forall x, smooth_compact_carrier K x ->
    norm_domain_interior NY (smooth_compact_carrier E) (f x).
  move=> x hx; exists radius; split; first exact: hRadius.
  move=> h hh; apply: (hTube (f x+h) (f x)).
  - change ((f @` smooth_compact_carrier K) (f x)); by exists x.
  - rewrite [f x+h]addrC addrK; exact: ltW hh.
pose P := fun i => @current_compact_map_pushforward R h2 n nu Z V hZ hV
  (g i) (current_smooth_approximation_image hG i)
  (current_smooth_approximation_class hG i) m S hCompact.
have hLimit := (proj2 hQ) E hInterior Z hZ hZU hKZ S hSFlat hRecovery g hG.
have hWeak := @current_flat_sequence_limit_weak R h2 nu m V hV E P Q hLimit.
have hRestrictionMass := @current_open_restriction_mass_bound R h2 n m
  Z U hZ hU hZU T.
have hSFinite : (@CurrentMass.value R h2 n m Z hZ S < +oo)%E :=
  le_lt_trans hRestrictionMass hFinite.
have hSRepresented := @current_finite_mass_representation R h2 n m Z hZ S hSFinite.
have hSSupport := @flat_current_supported_support R h2 n m Z hZ KZ S hSFlat.
apply: (@current_mass_weak_closed_bound R h2 nu m V hV P Q
  ((L^+m)%:E*MU T)%E 0%N hWeak).
move=> i _.
pose gi := g i.
pose hGiImage := current_smooth_approximation_image hG i.
pose hGiClass := current_smooth_approximation_class hG i.
pose hp := @current_compact_map_proper R h2 n nu m Z V hZ S gi hGiImage
  (norm_class_continuous (hGiClass 0%N)) hCompact.
have hMass := @current_smooth_pushforward_mass_bound_on_compact R h2 n nu m
  Z V hZ hV S gi hGiImage hGiClass hp hSRepresented KZ L hBoundK.1 hSSupport
  (fun x hx => @current_compact_smooth_differential_bound R n nu U V K f L Z g
    hApprox i x (hKZ x hx)).
have hCoefficient : (0 <= (L^+m)%:E)%E.
  rewrite lee_fin; apply: exprn_ge0; exact: hBoundK.1.
exact: le_trans hMass (lee_wpmul2l hCoefficient hRestrictionMass).
Qed.

(** Source for [current_flat_lipschitz_image_least_mass_bound]:
    retain the least compact-restriction constant in the
    mass estimate proved through 2.10.43 in Federer 4.1.14,
    p. 370. Finite-mass flat inputs are allowed. *)
Corollary current_flat_lipschitz_image_least_mass_bound
    (T : CU) (Q : CV) (L : R) :
  @is_flat_current_supported_in R h2 n m U hU K T ->
  (MU T < +oo)%E -> Image T Q ->
  @is_least_metric_lipschitz_constant R XT YT
    (smooth_compact_carrier K) f L ->
  (MV Q <= (L^+m)%:E*MU T)%E.
Proof.
move=> hFlat hFinite hQ hLeast.
exact: @current_flat_lipschitz_image_mass_bound T Q L hFlat hFinite hQ
  (least_metric_lipschitz_bound hLeast).
Qed.

(** Source for [current_normal_lipschitz_image_mass_bound]:
    exactly M(f#T)<=Lip(f restricted to K)^m M(T),
    the final normal-current assertion on Federer 4.1.14,
    p. 370. Normality supplies finite mass and flat
    membership; neither is an additional hypothesis. *)
Theorem current_normal_lipschitz_image_mass_bound
    (T : CU) (Q : CV) (L : R) :
  @normal_currents_supported_in R h2 n U hU m K T -> Image T Q ->
  @is_least_metric_lipschitz_constant R XT YT
    (smooth_compact_carrier K) f L ->
  (MV Q <= (L^+m)%:E*MU T)%E.
Proof.
move=> hNormal hQ hLeast.
have hFlat := @supported_normal_current_is_flat R h2 n m U hU K T hNormal.
have hFinite := @compact_represented_current_finite_mass R h2 n m U hU
  T hNormal.1.1.1 hNormal.1.2.
exact: @current_flat_lipschitz_image_least_mass_bound T Q L
  hFlat hFinite hQ hLeast.
Qed.

(** Source for [current_flat_lipschitz_image_finite_mass]: the
    original finite-mass flat input has a finite-mass image,
    supporting the continuous-form assertion at the end of
    Federer 4.1.14, p. 372. Local Lipschitz regularity supplies
    a finite compact bound internally; no constant is an extra
    hypothesis of this conclusion. *)
Corollary current_flat_lipschitz_image_finite_mass (T : CU) (Q : CV) :
  @is_flat_current_supported_in R h2 n m U hU K T ->
  (MU T < +oo)%E -> Image T Q -> (MV Q < +oo)%E.
Proof.
move=> hFlat hFinite hQ.
have hKLocal := @norm_open_local_lipschitz_compact R X Y NX NY hNX hNY
  U f (smooth_compact_carrier K) hU hLocal (smooth_compact_is_compact K)
  (smooth_compact_in_domain K).
pose L := metric_lipschitz_constant hKLocal.
have hLeast := metric_lipschitz_constant_specification hKLocal.
have hBound := @current_flat_lipschitz_image_mass_bound T Q L
  hFlat hFinite hQ (least_metric_lipschitz_bound hLeast).
have [mass [hMassNonnegative hMass]] := @current_finite_mass_value
  R h2 n m U hU T hFinite.
rewrite hMass -EFinM in hBound.
exact: le_lt_trans hBound (ltry (L^+m*mass)).
Qed.
End CurrentNormalLipschitzMassBound.
