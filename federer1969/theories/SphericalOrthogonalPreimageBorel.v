(** Federer (1969), 3.2.47(3), p. 283: Borel
    base sets have Borel whole orthogonal preimages.
    The actual group is compact by 3.2.28, and
    actual evaluation is continuous; no completed preimage
    measurability principle is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  OrthogonalMaps EuclideanHomInnerCharts EuclideanStiefelCompact
  SphericalOrthogonalOrbitDifferential SphericalOrbitCompactness SphericalProductPreimageImage
  LipschitzUP NormMetricScaleContinuity TopologicalBorel BorelFamilyBasic ContinuousBorelPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_orthogonal_preimage_borel]: actual
    Borel preimages used in the coarea proof of
    3.2.47(3), p. 283, from continuity of
    Phi and compactness of the original O(n).
    Arbitrary ambient dimensions and original Borel sets remain. *)
Lemma spherical_orthogonal_preimage_borel (R:realType) N (c:R_n R N) (E:set (R_n R N)):
  @borel_set (inner_metric_space (@euclidean_inner_productP R N)) E ->
  @borel_set (inner_metric_space (@euclidean_hom_inner_productP R N N))
    (spherical_orthogonal_preimage c E).
Proof.
move=>hE.
pose X:=inner_metric_space (@euclidean_hom_inner_productP R N N).
pose Y:=inner_metric_space (@euclidean_inner_productP R N).
have hO:@borel_set X [set g|is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g)].
  apply:closed_borel_set.
  exact (compact_closed (@metric_hausdorff R X) (@euclidean_stiefel_compact R N N)).
have [L [_ hBound]]:=spherical_orthogonal_orbit_lipschitz c.
have hContinuous:continuous (fun g:X=>(spherical_orthogonal_orbit c g:Y)).
  exact (metric_fixed_lipschitz_continuous hBound.1 (fun x y=>hBound.2 x y I I)).
exact (borel_family_binary_intersection (borel_sets_family X) hO (continuous_borel_preimage hContinuous hE)).
Qed.
