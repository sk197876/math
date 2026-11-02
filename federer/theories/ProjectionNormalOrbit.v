(** Normal vectors along the actual orthogonal-group orbit, supporting
    Federer (1969), 2.10.16, p. 178. The action p -> p composed with g
    inverse of 2.7.16(6), p. 139, has adjoint g composed with p adjoint, by
    1.7.4, p. 30. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOrthogonalInvariantMeasures Hom TensorUP InnerProductUP AdjointUP Adjoint AdjointLaws
  EuclideanProjectionSpace EuclideanProjectionMetric OrthogonalGroupHaarMeasure OrthogonalGroupTopology
  OrthogonalInjectionSpaces IsotropyGroupTopology LinearGroupTopology LinearGroupSealed
  ProjectionNormalVector ExteriorGrading ExteriorMaps ExteriorMapScaling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section NormalOrbit.
Variable R : realType.
Variables n m : nat.
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hBm := (@euclidean_inner_productP R m).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation O := (euclidean_orthogonal_group R n).
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn)
  (linear_group_inv hBn hbn) (linear_group_unit hBn hbn) O mulO invO eO.
Local Notation Ap := (orthogonal_projection_action hBm hBn hbn hO).
Local Notation om := (@orthogonal_element_map R (R_n R n) _ hBn n _ hbn).

(** Source for [projection_orbit_adjoint]: supporting adjoint
    evaluation along the projection orbit in 2.10.16,
    p. 178. This is the adjoint-composition law of
    1.7.4, p. 30, with the inverse of an orthogonal map. *)
Lemma projection_orbit_adjoint (p : orthogonal_projection_metric_space R n m) (g : O) :
  inner_adjoint hBn hBm hbn (euclidean_projection_linear (Ap g p)) =1
    linear_comp (hom_as_linear (om g)) (inner_adjoint hBn hBm hbn (euclidean_projection_linear p)).
Proof.
apply: (@adjoint_unique R (R_n R n) (R_n R m)
  (@euclidean_inner_product R n) (@euclidean_inner_product R m) hBn).
- exact: inner_adjointP.
- move=> x y.
  change (euclidean_inner_product x (om g (inner_adjoint hBn hBm hbn (euclidean_projection_linear p) y))=
    euclidean_inner_product (orthogonal_projection_map (Ap g p) x) y).
  have [_ hig] := orthogonal_element_inv hO g.
  rewrite orthogonal_projection_actionE -{1}(hig x) (orthogonal_element_inner g).
  exact: inner_adjointP.
Qed.

(** Source for [projection_normal_orbit]: supporting exterior
    equivariance of the normal vector in 2.10.16,
    p. 178, from 1.3.1, pp. 12–14, and
    1.7.4, p. 30. No choice of orientation along
    a parameter family is introduced. *)
Lemma projection_normal_orbit (p : orthogonal_projection_metric_space R n m) (g : O) :
  projection_normal_vector (Ap g p)=
    exterior_power_map (hom_as_linear (om g)) m (projection_normal_vector p).
Proof.
rewrite /projection_normal_vector exterior_power_map_composition.
apply: exterior_power_map_ext=> x; exact: projection_orbit_adjoint.
Qed.
End NormalOrbit.
