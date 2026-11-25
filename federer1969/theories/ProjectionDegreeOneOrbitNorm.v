(** Federer (1969), 3.2.13, p. 251: identify the
    degree-one projection orbit norm with the absolute first
    coordinate of the reversed orthogonal sphere orbit. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric Hom
  FirstCoordinateProjection ExteriorPowers OrthogonalProjectionConstants OrthogonalInjectionSpaces
  OrthogonalGroupHaarMeasure EuclideanOrthogonalInvariantMeasures IsotropyGroupTopology
  LinearGroupTopology LinearGroupSealed UnitSphereSpace UnitSphereOrthogonalAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OrbitNorm.
Variable R:realType.
Variable m:nat.
Variable hm:(0<m)%N.
Local Notation V:=(R_n R m).
Local Notation hB:=(@euclidean_inner_productP R m).
Local Notation hb:=(@coordinate_basisP R m).
Local Notation O:=(set_type (euclidean_orthogonal_group R m)).
Variables (mulS:O->O->O) (invS:O->O) (eS:O).
Hypothesis hS:is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb)
  (linear_group_unit hB hb) (euclidean_orthogonal_group R m) mulS invS eS.

(** Source for [first_projection_point_value]: the distinguished
    projection q evaluates to the first coordinate, Federer
    3.2.13, p. 251, through the compact parameter-space interface. *)
Lemma first_projection_point_value (v:V):
  orthogonal_projection_map (@first_coordinate_projection_point R m hm) v ord0=v (Ordinal hm).
Proof.
change (first_coordinate_projection hm v ord0=v (Ordinal hm)).
exact:first_coordinate_projection_value.
Qed.

(** Source for [projection_degree_one_orbit_norm]: the
    O*(m,1) orbit integrand is |q(g^-1 C)|, the
    degree-one identification used in Federer 3.2.13, p. 251. *)
Lemma projection_degree_one_orbit_norm (h2:(1+1:R)!=0)
    (g:O) (C:V):
  projection_norm h2 (exterior_first_inclusion V C)
    (orthogonal_projection_action (@euclidean_inner_productP R 1) hB hb hS g
      (@first_coordinate_projection_point R m hm))=
  `|orthogonal_element_map (invS g) C (Ordinal hm)|.
Proof.
rewrite projection_first_inclusion_norm orthogonal_projection_actionE first_projection_point_value.
by [].
Qed.
End OrbitNorm.
