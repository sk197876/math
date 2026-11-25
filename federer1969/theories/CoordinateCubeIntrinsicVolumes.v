(** Federer (1969), 3.2.45, p. 280: the exact intrinsic
    volumes of the first-factor cube are already determined by 3.2.36. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry RectangularBoxIntrinsicVolumes
  ConstantEdgeSymmetricCoefficients IntegralGeometricGauge SteinerTubePolynomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_cube_intrinsic_volume]: the cube factors
    binomial(m,i) s^i in Federer 3.2.45, p. 280. This applies the
    existing full rectangular-box theorem of 3.2.36, p. 273, to the
    actual cube. No full-dimensionality or positive side is added. *)
Theorem coordinate_cube_intrinsic_volume (R : realType) n (a : R_n R n) (s : R)
    (P : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_euclidean_coordinate_cube a s P -> forall j : 'I_n.+1,
    @integral_geometric_gauge R n j (steiner_dimension_guard j) 1 P =
      ('C(n,j)%:R * s^+j)%:E.
Proof.
move=> hP j.
exact: (@rectangular_box_intrinsic_volume_coefficient R n a (@coordinate_basis R n)
  (fun _ => s) P (fun j : 'I_n.+1 => 'C(n,j)%:R * s^+j)
  (coordinate_cube_rectangular_box hP) (constant_edge_symmetric_coefficients n s) j).
Qed.
