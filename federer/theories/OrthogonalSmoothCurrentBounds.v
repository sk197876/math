(** Federer (1969), 4.1.23, p. 379:
    rotating cell approximations preserves their
    mass and flat-error upper bounds. The
    preceding sharp smooth-image estimates apply
    with the actual differential cap one,
    including degree zero and R^0. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom AffineMaps RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLinear NormOpenDomainLaws NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanAffineSmooth EuclideanHomOperator HomSpaceTopology
  OrthogonalMaps CurrentSpaces CurrentMapDifferential CurrentIntegrationCriterion
  CurrentFiniteMassRepresentation CurrentMassSealed CurrentCompactMapProper
  CurrentCompactPushforwardAlgebra CurrentSmoothPushforwardMassBound
  CurrentSmoothPushforwardFlatBound CurrentLipschitzFlatCoefficient
  CurrentFlatNorm SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OrthogonalCurrentBounds.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation B := (@euclidean_inner_product R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation NX := (inner_norm hB).
Local Notation hNX := (inner_norm_real_norm hB).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Variable g : {linear X->X}.
Hypothesis hOrthogonal : is_orthogonal_map B B g.
Local Notation L := (hom_of_linear g).
Local Notation hf := (@euclidean_affine_map_smooth R n n Full hFull g (linear_affine_map g)).
Local Notation hImage := (fun (x : X) (_ : True) => Logic.I).
Local Notation Current := (@current_space R h2 n Full hFull m).
Local Notation M := (@CurrentMass.value R h2 n m Full hFull).
Local Notation Compact := (fun T : Current => @compact (real_norm_metric_space hNX)
  (@current_support R h2 n Full hFull m T)).
Local Notation Push := (fun (T : Current) (hT : Compact T) =>
  @current_compact_map_pushforward R h2 n n Full Full
    hFull hFull g hImage hf m T hT).

(** Source for [orthogonal_current_differential_cap]:
    the actual differential of the
    original orthogonal map has operator
    norm at most one, supporting
    the rotation reduction in Federer
    4.1.23, p. 379.
    R^0 requires the non-strict cap,
    without asserting its norm equals one. *)
Lemma orthogonal_current_differential_cap x :
  @euclidean_operator_norm R n n (@current_map_differential R n n Full g x)<=1.
Proof.
have hBounded : norm_bounded_linear NX NX L.
  exists 1; split; first exact: ler01.
  move=> v; change (is_true (NX (g v)<=1*NX v)).
  by rewrite (@orthogonal_map_norm R X X B B hB hB g hOrthogonal v) mul1r.
have hDifferential := @norm_differential_linear R X X NX NX hNX hNX
  Full x L (hFull x Logic.I) hBounded.
change (has_norm_differential NX NX Full g x L) in hDifferential.
rewrite (@current_map_differential_unique R n n Full g x L hDifferential)
  /euclidean_operator_norm.
apply: hom_operator_norm_least; first exact: ler01.
move=> v; change (is_true (NX (g v)<=1*NX v)).
by rewrite (@orthogonal_map_norm R X X B B hB hB g hOrthogonal v) mul1r.
Qed.

(** Source for [orthogonal_compact_current_mass_bound]:
    the original orthogonal image of
    every compact finite-mass current has
    no greater mass, supporting the
    rotation of the polyhedral approximant
    in Federer 4.1.23, p. 379.
    Finite mass supplies representation internally. *)
Theorem orthogonal_compact_current_mass_bound (T : Current) (hCompact : Compact T) :
  (M T< +oo)%E -> (M (Push T hCompact)<=M T)%E.
Proof.
move=> hFinite.
pose hProper := @current_compact_map_proper R h2 n n m Full Full hFull T
  g hImage (norm_class_continuous (hf 0%N)) hCompact.
have h := @current_smooth_pushforward_mass_bound_on_support R h2 n n m
  Full Full hFull hFull T g hImage hf hProper
  (@current_finite_mass_representation R h2 n m Full hFull T hFinite)
  1 ler01 (fun x _ => orthogonal_current_differential_cap x).
by rewrite expr1n mul1e in h.
Qed.

(** Source for [orthogonal_compact_current_flat_bound]:
    the original F_(g(K)) error
    is at most F_K before
    the rotation, supporting Federer
    4.1.23, p. 379.
    Only the displayed flat value
    is assumed finite, with no
    normality or flat-closure premise. *)
Theorem orthogonal_compact_current_flat_bound
    (K E : smooth_compact_set hNX Full)
    (hIndex : forall x, smooth_compact_carrier K x -> smooth_compact_carrier E (g x))
    (T : Current) (hCompact : Compact T)
    (hSupport : @current_support R h2 n Full hFull m T `<=` smooth_compact_carrier K) :
  (@current_flat_norm R h2 n m Full hFull K T< +oo)%E ->
  (@current_flat_norm R h2 n m Full hFull E (Push T hCompact)<=
    @current_flat_norm R h2 n m Full hFull K T)%E.
Proof.
move=> hFinite.
have h := @current_smooth_pushforward_flat_bound R h2 n n m Full Full hFull hFull
  g hImage hf K E hIndex 1 ler01
  (fun x _ => orthogonal_current_differential_cap x) T hCompact hSupport hFinite.
by rewrite /current_lipschitz_flat_coefficient !expr1n maxxx mul1e in h.
Qed.
End OrthogonalCurrentBounds.
