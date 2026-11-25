(** Federer (1969), 3.2.47, pp. 282–283: compact
    base cores have compact whole preimages in the actual
    orthogonal group. The ambient evaluation is bounded linear,
    hence globally Lipschitz, and the group is compact by
    the already proved 3.2.28 development. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  OrthogonalMaps EuclideanHomInnerCharts EuclideanStiefelCompact
  NormDifferentialUP NormMetricScaleContinuity LipschitzUP LipschitzBasic
  SphericalOrthogonalOrbitDifferential SphericalProductPreimageImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_orthogonal_orbit_lipschitz]: actual
    ambient evaluation is globally Lipschitz in the Hilbert
    Hom and Euclidean metrics; supporting Phi in 3.2.47,
    pp. 282–283. No unit-vector premise is needed here. *)
Theorem spherical_orthogonal_orbit_lipschitz (R:realType) N (c:R_n R N):
  @is_metric_lipschitz R (inner_metric_space (@euclidean_hom_inner_productP R N N))
    (inner_metric_space (@euclidean_inner_productP R N)) setT (spherical_orthogonal_orbit c).
Proof.
have [L [hL hBound]]:=norm_differential_bounded
  (@spherical_orthogonal_orbit_differential R N c 0).
apply:(@metric_lipschitz_of_bound R (inner_metric_space (@euclidean_hom_inner_productP R N N))
  (inner_metric_space (@euclidean_inner_productP R N)) setT (spherical_orthogonal_orbit c) L).
split; first exact hL.
move=>g h _ _; rewrite !inner_metric_distanceE.
change (is_true (inner_norm (@euclidean_inner_productP R N)
  (spherical_orthogonal_orbit c g-spherical_orthogonal_orbit c h)<=
  L*inner_norm (@euclidean_hom_inner_productP R N N) (g-h))).
rewrite -linearB; exact:hBound.
Qed.

(** Source for [spherical_orthogonal_preimage_compact]: every
    compact base core has compact whole actual preimage,
    supporting the compact H_e argument of 3.2.47, p. 283.
    Empty cores and arbitrary positions relative to the sphere remain. *)
Theorem spherical_orthogonal_preimage_compact (R:realType) N
    (c:R_n R N) (K:set (R_n R N)):
  @compact (inner_metric_space (@euclidean_inner_productP R N)) K ->
  @compact (inner_metric_space (@euclidean_hom_inner_productP R N N))
    (spherical_orthogonal_preimage c K).
Proof.
move=>hK.
pose X:=inner_metric_space (@euclidean_hom_inner_productP R N N).
pose Y:=inner_metric_space (@euclidean_inner_productP R N).
have [L [_ hBound]]:=spherical_orthogonal_orbit_lipschitz c.
have hContinuous:continuous (fun g:X=>(spherical_orthogonal_orbit c g:Y)).
  exact (metric_fixed_lipschitz_continuous hBound.1 (fun x y=>hBound.2 x y I I)).
have hClosedK:=compact_closed (@metric_hausdorff R Y) hK.
have hOpen:@open X (spherical_orthogonal_orbit c @^-1` ~`K).
  exact (@open_comp X Y (fun g:X=>(spherical_orthogonal_orbit c g:Y)) (~`K)
    (fun g _=>hContinuous g) (closed_openC hClosedK)).
have hClosed:=open_closedC hOpen.
rewrite -preimage_setC setCK in hClosed.
exact (@compact_closedI X
  [set g|is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g)]
  (spherical_orthogonal_orbit c @^-1` K) (@euclidean_stiefel_compact R N N) hClosed).
Qed.
