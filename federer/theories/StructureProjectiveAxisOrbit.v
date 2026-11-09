(** Federer (1969), 3.3.4, pp. 290–291: a local actual base
    point for the normalized projective orbit F. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm EuclideanCoordinateMetric StructureProjectiveSphere StructureProjectiveSpace
  StructureProjectiveRotation StructureProjectiveTransport EuclideanOrthogonalInvariantMeasures
  OrthogonalGroupHaarMeasure SymmetricSquareGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [structure_projective_axis_orbit_exists]: the actual
    map F(h)=T(h(g_j)) in Federer 3.3.4, pp. 290–291, is the orbit
    of the projective square of the distinguished active unit axis.
    This is local existential data, without a global chosen direction
    or a selected representative for any projective point. *)
Theorem structure_projective_axis_orbit_exists (R:realType) m:
  exists z0:structure_projective_space R m,
    val z0=inner_projective_square (@coordinate_basis R m.+1 (lshift m (ord0:'I_1))) /\
    forall h:euclidean_orthogonal_group R m.+1,
      val (structure_projective_action h z0)=inner_projective_square
        (orthogonal_element_map h (@coordinate_basis R m.+1 (lshift m (ord0:'I_1)))).
Proof.
pose v:=@coordinate_basis R m.+1 (lshift m (ord0:'I_1)).
have hMember:@structure_projective_sphere R m (inner_projective_square v).
  exists v=>//; exact:euclidean_coordinate_unit_norm.
exists (Sub (inner_projective_square v) (mem_set hMember)); split=>// h.
change (structure_projective_rotation h (inner_projective_square v)=
  inner_projective_square (orthogonal_element_map h v)).
exact:structure_projective_square_natural.
Qed.
