(** Federer (1969), 3.2.47, pp. 282–283:
    actual evaluation in orthonormal ambient coordinates is
    bounded linear, hence globally Lipschitz, and Borel
    sources have Borel fibres. These facts discharge the
    original coarea hypotheses in the hull comparison. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  EuclideanHomInnerCharts NormDifferentialUP NormFiniteLinearBound
  SphericalOrthogonalOrbitDifferential LipschitzUP LipschitzBasic NormMetricScaleContinuity
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMappingMultiplicity
  TopologicalBorel BorelFamilyBasic ContinuousBorelPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_coordinate_orbit_lipschitz]: actual
    evaluation in original ambient coordinates is Lipschitz,
    supporting 3.2.22 in 3.2.47(3), p. 283.
    No unit-vector or isometry premise is required here. *)
Theorem spherical_coordinate_orbit_lipschitz (R:realType) N d
    (e:Hom (R_n R d) (Hom (R_n R N) (R_n R N))) (c:R_n R N):
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R d))
    (inner_metric_space (@euclidean_inner_productP R N)) setT (fun x=>e x c).
Proof.
pose L:=hom_comp (spherical_orthogonal_orbit c) e.
have [C [hC hBound]]:=@norm_finite_linear_bounded R (R_n R d) (R_n R N) _ _
  (inner_norm_real_norm (@euclidean_inner_productP R d))
  (inner_norm_real_norm (@euclidean_inner_productP R N)) d
  (@coordinate_basis R d) (@coordinate_basisP R d) L.
apply:(@metric_lipschitz_of_bound R (inner_metric_space (@euclidean_inner_productP R d))
  (inner_metric_space (@euclidean_inner_productP R N)) setT (fun x=>e x c) C).
split; first exact hC.
move=>x y _ _; rewrite !inner_metric_distanceE.
change (is_true (inner_norm (@euclidean_inner_productP R N) (L x-L y)<=
  C*inner_norm (@euclidean_inner_productP R d) (x-y))).
rewrite -linearB; exact:hBound.
Qed.

(** Source for [spherical_coordinate_fibre_borel]: every
    actual fibre of a Borel source under Phi is
    Borel, supporting 3.2.47(3), p. 283. The
    equality is with the whole original partial-map fibre,
    and no fibre-mass finiteness is assumed. *)
Lemma spherical_coordinate_fibre_borel (R:realType) N d
    (e:Hom (R_n R d) (Hom (R_n R N) (R_n R N))) (c:R_n R N)
    (W:set (R_n R d)) z:
  @borel_set (inner_metric_space (@euclidean_inner_productP R d)) W ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R d))
    (partial_mapping_fibre (partial_function_source_restrict W
      (partial_function_total (fun x=>e x c))) z).
Proof.
move=>hW.
pose X:=inner_metric_space (@euclidean_inner_productP R d).
pose Y:=inner_metric_space (@euclidean_inner_productP R N).
have [L [_ hBound]]:=@spherical_coordinate_orbit_lipschitz R N d e c.
have hContinuous:continuous (fun x:X=>(e x c:Y)).
  exact (metric_fixed_lipschitz_continuous hBound.1 (fun x y=>hBound.2 x y I I)).
have hSingleton:@borel_set Y [set z].
  exact (closed_borel_set (compact_closed (@metric_hausdorff R Y) (@compact_set1 Y z))).
exact (borel_family_binary_intersection (borel_sets_family X) hW
  (continuous_borel_preimage hContinuous hSingleton)).
Qed.
