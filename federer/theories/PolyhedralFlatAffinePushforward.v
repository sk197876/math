(** Federer (1969), 4.1.24, p. 380: the
    actual flat pushforward by the auxiliary affine
    source inclusions is integral polyhedral in the
    exact image compact. Combine the preceding affine
    polyhedral theorem with the registered smooth agreement
    of the opaque flat pushforward. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom AffineMaps RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanAffineSmooth SmoothCompactSet CurrentSpaces LipschitzUP FlatCurrentsUP
  CurrentLipschitzCompactImage CurrentFlatLipschitzPushforwardSealed
  CurrentCompactLipschitzPushforwardSmooth PolyhedralCurrentAlgebra
  PolyhedralCurrentFlat PolyhedralAffinePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [integral_polyhedral_current_flat_affine_pushforward]:
    every original affine source placement used for
    addition in 4.1.24, p. 380, preserves integral
    polyhedral membership at its specified compact. Neither
    compact need be convex. The supplied flat-membership
    witness only types the actual original image. *)
Theorem integral_polyhedral_current_flat_affine_pushforward
    (R:realType) (h2:(1+1:R)!=0) d n m
    (Z:set (R_n R d)) (U:set (R_n R n))
    (hZ:forall x,Z x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R d)) Z x)
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (f:R_n R d->R_n R n) (hAffine:is_affine_map f)
    (hImage:forall x,Z x->U (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) Z f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R d)) Z)
    (L:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hKL:forall x,smooth_compact_carrier K x->smooth_compact_carrier L (f x))
    (T:@current_space R h2 d Z hZ m)
    (hPoly:@integral_polyhedral_current_class R h2 d m Z hZ K T)
    (hFlat:@is_flat_current R h2 d m Z hZ T):
  @integral_polyhedral_current_class R h2 n m U hU L
    (@CurrentFlatLipschitzPushforward.value R h2 d n m Z U hZ hU
      f hImage hLocal T hFlat).
Proof.
pose hK:=@integral_polyhedral_current_flat_supported R h2 d m Z hZ K T hPoly.
pose hSmooth:=@euclidean_affine_map_smooth R d n Z hZ f hAffine.
rewrite (@CurrentFlatLipschitzPushforward.compact_value R h2 d n m
  Z U hZ hU f hImage hLocal T hFlat K hK).
rewrite (@current_compact_lipschitz_pushforward_smooth R h2 d n m
  Z U hZ hU f hImage hLocal K T hK hSmooth).
exact:(@integral_polyhedral_current_affine_pushforward R h2 d n m Z U hZ hU
  f hAffine hImage K L hKL T hPoly
  (@flat_supported_current_compact R h2 d m Z hZ K T hK)).
Qed.
