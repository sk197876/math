(** Federer (1969), 3.3.4, p. 290: the actual
    orthogonal action on T(U), as the existing
    symmetric-power functor. Prove image preservation,
    isometricity and inverses solely from public laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric SymmetricGrading SymmetricMaps SymmetricPowerFunctor
  InnerSymmetricPositivity SymmetricSquareGeometry StructureProjectiveSphere
  StructureProjectiveTransport UnitSphereSpace EuclideanOrthogonalInvariantMeasures
  OrthogonalGroupHaarMeasure OrthogonalMaps IsotropyGroupTopology LinearGroupTopology LinearGroupSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projective_rotation]: the
    induced isometric action on T(U) in Federer
    3.3.4, p. 290. The map is defined on
    the actual symmetric ambient space; its
    restriction to the original image is proved below. *)
Definition structure_projective_rotation (R:realType) m
    (g:euclidean_orthogonal_group R m.+1):=
  symmetric_power_map (hom_as_linear (orthogonal_element_map g)) 2.

(** Source for [structure_projective_rotation_member]:
    the orthogonal action preserves the actual
    T(U), Federer 3.3.4, p. 290. *)
Lemma structure_projective_rotation_member (R:realType) m
    (g:euclidean_orthogonal_group R m.+1) z:
  @structure_projective_sphere R m z ->
  @structure_projective_sphere R m (structure_projective_rotation g z).
Proof.
move=>[x hx <-]; exists (orthogonal_element_map g x).
- change (inner_norm (@euclidean_inner_productP R m.+1) (orthogonal_element_map g x)= 1).
  by rewrite (orthogonal_map_norm (@euclidean_inner_productP R m.+1)
    (@euclidean_inner_productP R m.+1) (orthogonal_element_orthogonal g)).
- symmetry; exact:structure_projective_square_natural.
Qed.

(** Source for [structure_projective_rotation_isometry]:
    every actual group element acts isometrically
    on T(U), Federer 3.3.4, p. 290. All
    actual projective points are retained. *)
Theorem structure_projective_rotation_isometry (R:realType) m
    (g:euclidean_orthogonal_group R m.+1)
    (z w:inner_metric_space (@symmetric_inner_productP R (R_n R m.+1)
      (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1) 2)):
  @structure_projective_sphere R m z ->@structure_projective_sphere R m w ->
  mdist (structure_projective_rotation g z:
      inner_metric_space (@symmetric_inner_productP R (R_n R m.+1)
        (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1) 2))
    (structure_projective_rotation g w)=mdist z w.
Proof.
move=>[x hx <-] [y hy <-]; rewrite !inner_metric_distanceE.
exact:(@structure_projective_orthogonal_isometry R (R_n R m.+1)
  (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1)
  (hom_as_linear (orthogonal_element_map g)) x y
  (orthogonal_element_orthogonal g) hx hy).
Qed.

Section Inverses.
Variable R:realType.
Variable m:nat.
Local Notation hB:=(@euclidean_inner_productP R m.+1).
Local Notation hb:=(@coordinate_basisP R m.+1).
Local Notation O:=(euclidean_orthogonal_group R m.+1).
Variables (mulS:O->O->O) (invS:O->O) (eS:O).
Hypothesis hS:is_subgroup_restriction (linear_group_mul hB hb)
  (linear_group_inv hB hb) (linear_group_unit hB hb) O mulS invS eS.

(** Source for [structure_projective_rotation_cancel]:
    the inverse group element gives the actual
    inverse symmetric-power action, supporting Federer
    3.3.4, p. 290. No section or selected
    projective representative is introduced. *)
Theorem structure_projective_rotation_cancel g:
  cancel (structure_projective_rotation g) (structure_projective_rotation (invS g)) /\
  cancel (structure_projective_rotation (invS g)) (structure_projective_rotation g).
Proof.
have [hLeft hRight]:=orthogonal_element_inv hS g; split.
- exact:(@symmetric_power_mapK R (R_n R m.+1) (R_n R m.+1)
    (hom_as_linear (orthogonal_element_map g))
    (hom_as_linear (orthogonal_element_map (invS g))) hLeft 2).
- exact:(@symmetric_power_mapK R (R_n R m.+1) (R_n R m.+1)
    (hom_as_linear (orthogonal_element_map (invS g)))
    (hom_as_linear (orthogonal_element_map g)) hRight 2).
Qed.
End Inverses.
