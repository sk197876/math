(** Federer (1969), 3.2.13, p. 251: q in O*(m,1)
    sends u to its first coordinate. Use the existing coordinate
    projection laws and the abstract degree-one exterior identifications. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  EuclideanOneCoordinate EuclideanOneNormDifferential InitialIndices CoordinateProjection AdjointUP Hom
  OrthogonalMaps OrthogonalInjectionSpaces EuclideanOrthogonalInvariantMeasures
  OrthogonalProjectionConstants ExteriorPowers ExteriorDegreeOneNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [first_coordinate_projection]: the printed q(u)=u_1
    in Federer 3.2.13, p. 251, expressed in the one-coordinate
    Euclidean target. *)
Definition first_coordinate_projection (R:realType) m (hm:(0<m)%N):
    {linear R_n R m->R_n R 1}:=
  GRing.Linear.clone _ _ _ _ (@coordinate_projection R m 1 (Lambda_initial hm)) _.
Arguments first_coordinate_projection {R m} hm.

(** Source for [first_coordinate_projection_member]: q belongs
    to O*(m,1), Federer 3.2.13, p. 251, by the
    coordinate projection theorem 1.7.4, p. 31. *)
Lemma first_coordinate_projection_member (R:realType) m (hm:(0<m)%N):
  is_orthogonal_projection (@euclidean_inner_product R m) (@euclidean_inner_product R 1)
    (first_coordinate_projection hm).
Proof.
apply:(O_star_projection _).1; exact:coordinate_projection_orthogonal.
Qed.

(** Source for [first_coordinate_projection_value]: q(u)=u_1,
    Federer 3.2.13, p. 251, with zero-based ordinal indices. *)
Lemma first_coordinate_projection_value (R:realType) m (hm:(0<m)%N) (u:R_n R m):
  first_coordinate_projection hm u ord0=u (Ordinal hm).
Proof.
rewrite /first_coordinate_projection /= coordinate_projectionE /Lambda_initial /initial_tuple tnth_mktuple.
congr (u _); exact:val_inj.
Qed.

(** Source for [first_coordinate_projection_point]: q regarded
    as a point of the compact orthogonal-projection space,
    Federer 3.2.13, p. 251. *)
Definition first_coordinate_projection_point (R:realType) m (hm:(0<m)%N):
    set_type (euclidean_orthogonal_projections R m 1):=
  orthogonal_projection_of (@euclidean_inner_productP R 1) (@euclidean_inner_productP R m)
    (@coordinate_basisP R m) (@first_coordinate_projection_member R m hm).
Arguments first_coordinate_projection_point {R m} hm.

(** Source for [projection_first_inclusion_norm]: the norm
    |Lambda_1 p(C)| is |p(C)|, 1.7.5, pp. 31–32,
    used in Federer 3.2.13, p. 251. *)
Lemma projection_first_inclusion_norm (R:realType) (h2:(1+1:R)!=0) m
    (p:set_type (euclidean_orthogonal_projections R m 1)) (v:R_n R m):
  projection_norm h2 (exterior_first_inclusion (R_n R m) v) p=
    `|(orthogonal_projection_map p v) ord0|.
Proof.
rewrite /projection_norm exterior_map_first_inclusion exterior_first_norm hom_as_linearE.
exact:euclidean_one_norm_coordinate.
Qed.
