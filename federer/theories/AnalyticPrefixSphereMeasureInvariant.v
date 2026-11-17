(** Federer (1969), 3.4.8(6), p. 328:
    the actual prefix sphere Hausdorff measure is
    invariant under H_p on every subset. The
    ambient orthogonal action is isometric in the
    original restricted metric. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  LinearBasis OrthonormalFamilies OrthogonalMaps HomInner OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  LinearGroupTopology LinearGroupSealed TopologicalGroupUP TopologicalGroupLaws IsotropyGroupTopology
  HomogeneousSpaceUP HomogeneousSpaceLaws MetricSubsetBackground HausdorffMeasure MeasurePushforward
  OrthogonalCoordinateFixing AnalyticPrefixSphereAction HausdorffIsometryMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Invariance.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable p:nat.
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation H:=(@analytic_prefix_rotation_group R X B hB n e he p).
Local Notation XT:=(inner_metric_space hB).
Local Notation S:=(@analytic_prefix_unit_sphere R X B hB n e p).
Local Notation M:=([the metricType R of metric_subset S]).
Local Notation A:=(@analytic_prefix_sphere_action R X B hB n e he p).

(** Source for [analytic_prefix_sphere_action_distance]: actual
    H_p evaluation preserves the restricted original
    metric, supporting 3.4.8(6), p. 328. *)
Lemma analytic_prefix_sphere_action_distance (g:H) (u v:M):
  mdist (A g u:M) (A g v:M) = mdist u v.
Proof.
rewrite !metric_subset_distanceE !inner_metric_distanceE.
have hOrthogonal:=@orthogonal_element_orthogonal R X B hB n e he (set_val g).
have hNorm:=@orthogonal_map_norm R X X B B hB hB
  (hom_as_linear (@orthogonal_element_map R X B hB n e he (set_val g))) hOrthogonal (set_val u-set_val v).
rewrite hom_as_linearE linearB /= in hNorm;exact:hNorm.
Qed.

Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he) O mulO invO unitO.
Variables (mulH:H->H->H) (invH:H->H) (unitH:H).
Hypothesis hH:is_subgroup_restriction mulO invO unitO H mulH invH unitH.

(** Source for [analytic_prefix_sphere_hausdorff_invariant]:
    actual Hausdorff measure on the original prefix
    sphere is invariant, 3.4.8(6), p. 328.
    Apply the theorem already proved for 2.10.11
    in HausdorffIsometryMeasurability; it covers
    all subsets without a measurability hypothesis. *)
Theorem analytic_prefix_sphere_hausdorff_invariant:
  orthonormal_family B e ->(p<=n)%N ->forall g:H,
    measure_pushforward (A g) (@hausdorff_measure R M (p-1)) = @hausdorff_measure R M (p-1).
Proof.
move=>hON hPN g.
have hHomogeneous:=@analytic_prefix_sphere_homogeneous R X B hB n e he p
  mulO invO unitO hO mulH invH unitH hH hON hPN.
have hGroup:=topological_group_laws (subgroup_restriction_topological hH
  (lch_group_topological (@orthogonal_group_lch R X B hB n e he mulO invO unitO hO))).
exact:(@hausdorff_bijective_isometry_pushforward R M M (A g) (A (invH g))
  (homogeneous_translation_inverse_left hGroup hHomogeneous g)
  (homogeneous_translation_inverse_right hGroup hHomogeneous g)
  (analytic_prefix_sphere_action_distance g) (p-1)).
Qed.
End Invariance.
