(** Federer (1969), 2.6.5, pp. 119–120: L^2 is the Cartesian product of the
    two scalar Lebesgue factors under the usual coordinate map. This adapter
    supplies exactly the L^2 convention used in the nonmeasurability claim
    of 2.5.10, p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanOneCoordinate
  EuclideanCoordinateSplit EuclideanPlaneCoordinates MeasureUP MeasurePushforward
  MeasureBijectionUP MeasureBijectionLaws ProductMeasure ProductMeasureBijections
  ProductMeasureTranspose LebesgueScalarMeasure EuclideanLebesgue EuclideanLebesgueDimensions
  EuclideanLebesgueBijections PushforwardMeasurabilityTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_plane_lebesgue_bijection]:
    the usual two-factor identification in Federer
    2.6.5, pp. 119–120, for the exact
    Cartesian coordinates in 2.5.10, p. 101.
    Equality holds for outer measures on all subsets. *)
Lemma euclidean_plane_lebesgue_bijection (R : realType) :
  is_measure_bijection (@euclidean_lebesgue_measure R 2)
    (product_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R))
    (@euclidean_plane_split R) (@euclidean_plane_join R).
Proof.
pose h := lebesgue_scalar_is_measure R.
have h1 := @positive_euclidean_split_bijection R 0.
have h2 := @measure_bijection_product R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R 1)] R R R
  (@positive_euclidean_lebesgue_measure R 0) (@lebesgue_scalar_measure R)
  (@lebesgue_scalar_measure R) (@lebesgue_scalar_measure R)
  (positive_euclidean_lebesgue_is_measure R 0) h h h
  (@euclidean_one_project R) (@euclidean_one_embed R) (fun x => x) (fun x => x)
  (positive_euclidean_line_bijection R) (measure_bijection_identity (@lebesgue_scalar_measure R)).
have h3 : is_measure_bijection (product_measure h h) (product_measure h h)
    (fun p : R*R => (p.2,p.1)) (fun p : R*R => (p.2,p.1)).
  constructor; [by move=> [s t]|by move=> [s t]|].
  apply: funext=> A; exact: product_measure_transpose.
exact (measure_bijection_compose (measure_bijection_compose h1 h2) h3).
Qed.

(** Source for [euclidean_plane_lebesgue_preimage_measurable]:
    transfer of L^2 measurability to the scalar product
    coordinates used in the Fubini argument for Federer
    2.5.10, p. 101, from the defining identity
    2.6.5, pp. 119–120. *)
Lemma euclidean_plane_lebesgue_preimage_measurable (R : realType)
    (A : set (inner_metric_space (@euclidean_inner_productP R 2))) :
  measure_measurable (@euclidean_lebesgue_measure R 2) A ->
  measure_measurable
    (product_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R))
    ((@euclidean_plane_join R) @^-1` A).
Proof.
move=> hA.
have hi := measure_bijection_inverse (euclidean_plane_lebesgue_bijection R).
apply: (@measure_pushforward_preimage_measurable R [the choiceType of (R*R)%type]
  [the choiceType of inner_metric_space (@euclidean_inner_productP R 2)]
  (@euclidean_plane_join R) _ A (can_inj (@euclidean_plane_joinK R))).
by rewrite (measure_bijection_pushforward hi).
Qed.
