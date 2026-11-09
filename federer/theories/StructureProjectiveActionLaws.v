(** Federer (1969), 3.3.4, p. 290: actual
    orthogonal multiplication and inversion act on
    T(U) through the symmetric-power functor. The
    established continuous transitive action is a
    homogeneous-space action in the book's sense. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric SymmetricGrading SymmetricMaps SymmetricPowerFunctor InnerSymmetricPositivity
  StructureProjectiveSphere StructureProjectiveSpace StructureProjectiveRotation
  StructureProjectiveActionTopology MetricSubsetBackground
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP HomogeneousSpaceUP CompactGroupHomogeneousMeasures.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Laws.
Variable R:realType.
Variable m:nat.
Local Notation hB:=(@euclidean_inner_productP R m.+1).
Local Notation hb:=(@coordinate_basisP R m.+1).
Local Notation O:=(euclidean_orthogonal_group R m.+1).
Local Notation M:=(structure_projective_space R m).
Variables (mulS:O->O->O) (invS:O->O) (eS:O).
Hypothesis hS:is_subgroup_restriction (linear_group_mul hB hb)
  (linear_group_inv hB hb) (linear_group_unit hB hb) O mulS invS eS.

(** Source for [structure_projective_action_compatible]:
    the composition law for the actual action on
    T(U), Federer 3.3.4, p. 290, follows
    from the exact symmetric-power composition law. *)
Lemma structure_projective_action_compatible g h (z:M):
  structure_projective_action (mulS g h) z=
    structure_projective_action g (structure_projective_action h z).
Proof.
apply:val_inj.
change (symmetric_power_map (hom_as_linear (orthogonal_element_map (mulS g h))) 2 (val z)=
  symmetric_power_map (hom_as_linear (orthogonal_element_map g)) 2
    (symmetric_power_map (hom_as_linear (orthogonal_element_map h)) 2 (val z))).
rewrite symmetric_power_map_composition.
apply:symmetric_power_map_ext=>x.
change (orthogonal_element_map (mulS g h) x=orthogonal_element_map g (orthogonal_element_map h x)).
exact:orthogonal_element_mulE hS g h x.
Qed.

(** Source for [structure_projective_action_cancel]:
    both actual inverse laws on T(U), supporting
    the measure invariance in Federer 3.3.4,
    p. 290. No selected point or fibre is used. *)
Lemma structure_projective_action_cancel g:
  cancel (structure_projective_action g) (structure_projective_action (invS g)) /\
  cancel (structure_projective_action (invS g)) (structure_projective_action g).
Proof.
have [hLeft hRight]:=structure_projective_rotation_cancel hS g; split=>z; apply:val_inj.
- exact:hLeft (val z).
- exact:hRight (val z).
Qed.

(** Source for [structure_projective_homogeneous]: the
    actual T(U) is a homogeneous orthogonal-group
    space, Federer 3.3.4, p. 290. Continuity,
    composition, openness and surjectivity of the
    orbit maps are all proved conclusions. *)
Theorem structure_projective_homogeneous:
  is_homogeneous_space mulS (@structure_projective_action R m).
Proof.
exact:(@compact_transitive_homogeneous [the topologicalType of set_type O]
  M mulS invS eS (@structure_projective_action R m)
  (lch_group_topological (orthogonal_group_lch hS))
  (@orthogonal_group_compact_space R (R_n R m.+1) (@euclidean_inner_product R m.+1)
    hB m.+1 (@coordinate_basis R m.+1) hb)
  (@metric_hausdorff R M) (@structure_projective_action_continuous R m)
  structure_projective_action_compatible (@structure_projective_action_transitive R m)).
Qed.
End Laws.
