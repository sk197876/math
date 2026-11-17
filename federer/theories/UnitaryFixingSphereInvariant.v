(** Federer (1969), 3.4.12, p. 339: the original
    coordinate-fixing unitary sphere action preserves Hausdorff measure
    on every subset. Reuse the already proved bijective-isometry
    pushforward theorem of 2.10.11. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws
  HermitianUP HermitianRealImaginary HermitianComplexLinearity InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  OrthogonalMaps OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  UnitaryGroup UnitaryComplexMapSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
From Federer Require Import HomSpaceTopology TopologicalGroupUP IsotropyGroupTopology TopologicalProductMaps
  SubtypeCompactHausdorff HomogeneousSpaceUP CompactGroupHomogeneousMeasures UnitaryGroupClosed
  UnitaryCoordinateFixing UnitaryCoordinateFixingHaar UnitarySphereTransitivity UnitaryHermitianPreservation.
From Federer Require Import MetricSubsetBackground TopologicalGroupLaws HomogeneousSpaceLaws
  UnitaryFixingSphereAction HausdorffMeasure HausdorffIsometryMeasurability MeasurePushforward.
Section Invariance.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Variable N:nat.
Variable r:'I_N->XR.
Variable hr:is_basis r.
Local Notation O:=(@orthogonal_group R XR B hB N r hr).
Local Notation U:=(@unitary_group R X H hH N r hr).
Local Notation L:=(fun g:U=>@UnitaryComplexMap.value R X H hH N r hr g).

Variable n:nat.
Variable e:'I_n->X.
Variable J:set 'I_n.
Local Notation S:=(@unitary_coordinate_fixing_group R X H hH N r hr n e J).
Local Notation XT:=(inner_metric_space hB).
Local Notation HT:=(inner_metric_space (hom_inner_productP hB hB hr)).

Local Notation V:=(@unitary_fixing_sphere R X H hH n e J).
Local Notation M:=([the metricType R of metric_subset V]).
Local Notation A:=(@unitary_fixing_sphere_action R X H hH N r hr n e J).

(** Source for [unitary_fixing_sphere_action_distance]: the actual
    unitary action preserves the original restricted metric,
    3.4.12, p. 339. *)
Lemma unitary_fixing_sphere_action_distance (g:S) (u v:M):
  mdist (A g u:M) (A g v:M)=mdist u v.
Proof.
rewrite !metric_subset_distanceE !inner_metric_distanceE.
change (inner_norm hB (L (set_val g) (set_val u)-L (set_val g) (set_val v))=
  inner_norm hB (set_val u-set_val v)).
have hNorm:=@unitary_element_norm R X H hH N r hr (set_val g) (set_val u-set_val v).
rewrite -(@UnitaryComplexMap.laws R X H hH N r hr (set_val g) (set_val u-set_val v)) linearB in hNorm.
exact:hNorm.
Qed.
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Variable hO:is_subgroup_restriction (@linear_group_mul R XR B hB N r hr)
  (@linear_group_inv R XR B hB N r hr) (@linear_group_unit R XR B hB N r hr) O mulO invO unitO.
Variables (mulU:U->U->U) (invU:U->U) (unitU:U).
Variable hU:is_subgroup_restriction mulO invO unitO U mulU invU unitU.
Variables (mulS:S->S->S) (invS:S->S) (unitS:S).
Variable hS:is_subgroup_restriction mulU invU unitU S mulS invS unitS.


(** Source for [unitary_fixing_sphere_hausdorff_invariant]: actual
    Hausdorff measure is invariant under each original unitary fixing
    transformation, in every natural degree, 3.4.12, p. 339. *)
Theorem unitary_fixing_sphere_hausdorff_invariant d (g:S):
  measure_pushforward (A g) (@hausdorff_measure R M d)=@hausdorff_measure R M d.
Proof.
have hLocal:=@unitary_fixing_group_lch R X H hH N r hr n e J
  mulO invO unitO hO mulU invU unitU hU mulS invS unitS hS.
have hHomogeneous:=@unitary_fixing_sphere_homogeneous R X H hH N r hr n e J
  mulO invO unitO hO mulU invU unitU hU mulS invS unitS hS.
have hGroup:=topological_group_laws (lch_group_topological hLocal).
exact:(@hausdorff_bijective_isometry_pushforward R M M (A g) (A (invS g))
  (homogeneous_translation_inverse_left hGroup hHomogeneous g)
  (homogeneous_translation_inverse_right hGroup hHomogeneous g)
  (unitary_fixing_sphere_action_distance g) d).
Qed.
End Invariance.
