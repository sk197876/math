(** Federer (1969), 3.3.4, pp. 290–291: the
    actual projective unit-sphere image T(U) is a
    compact smooth manifold with positive finite H^m
    mass. The original symmetric Hilbert metric and
    both antipodal unit-sphere points are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric SymmetricGrading InnerSymmetric InnerSymmetricPositivity
  SymmetricSquareGeometry SymmetricSquareSmooth SymmetricSquareSmoothSubmanifold
  SymmetricSquareManifoldArea FiniteInnerSmoothCompactImage
  FiniteInnerSubmanifoldUP FiniteInnerSmoothSubmanifoldUP
  UnitSphereSpace SphericalUnitSphereSmooth HausdorffMeasure
  HausdorffUnitSphereMass EuclideanBallVolume MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projective_sphere]: the actual
    T(U) in Federer 3.3.4, p. 290, in an
    orthonormal coordinate copy of its (m+1)-dimensional
    active space. No point or direction representative
    is selected to define this subset. *)
Definition structure_projective_sphere (R:realType) m:
    set (inner_metric_space (@symmetric_inner_productP R (R_n R m.+1)
      (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1) 2)):=
  (@inner_projective_square R (R_n R m.+1)) @` (@euclidean_unit_sphere_set R m.+1).

(** Source for [structure_projective_sphere_smooth]: the
    assertion that T(U) is an m-dimensional submanifold
    of class one, Federer 3.3.4, p. 290. In fact
    its already proved unit-sphere charts and the
    3.2.28(4) image theorem give every finite class. *)
Theorem structure_projective_sphere_smooth (R:realType) m:
  is_inner_smooth_submanifold
    (@symmetric_inner_form R (R_n R m.+1) (@euclidean_inner_product R m.+1)
      (@euclidean_inner_productP R m.+1) 2) m (@structure_projective_sphere R m).
Proof.
have hSource:=@spherical_unit_sphere_smooth R m.+1.
rewrite subn1 /= in hSource.
apply:(@inner_projective_square_smooth_submanifold R (R_n R m.+1)
  (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1)
  m.+1 (@coordinate_basis R m.+1) (@coordinate_basisP R m.+1)
  m (@euclidean_unit_sphere_set R m.+1) hSource).
- by move=>x hx.
- move=>x hx; change (inner_norm (@euclidean_inner_productP R m.+1) (-x)= 1).
  by rewrite inner_normN.
Qed.

(** Source for [structure_projective_sphere_compact]:
    compactness of the original T(U), Federer
    3.3.4, p. 290, as the continuous image
    of the actual compact unit sphere. *)
Theorem structure_projective_sphere_compact (R:realType) m:
  compact (@structure_projective_sphere R m).
Proof.
exact:(@inner_class_map_compact_image R (R_n R m.+1)
  (symmetric_power (R_n R m.+1) 2) (@euclidean_inner_product R m.+1)
  (@symmetric_inner_form R (R_n R m.+1) (@euclidean_inner_product R m.+1)
    (@euclidean_inner_productP R m.+1) 2)
  (@euclidean_inner_productP R m.+1)
  (@symmetric_inner_productP R (R_n R m.+1) (@euclidean_inner_product R m.+1)
    (@euclidean_inner_productP R m.+1) 2)
  (@inner_projective_square R (R_n R m.+1)) 0%N
  (@euclidean_unit_sphere_set R m.+1)
  (@inner_projective_square_smooth R (R_n R m.+1) (@euclidean_inner_product R m.+1)
    (@euclidean_inner_productP R m.+1) 0%N)
  (@euclidean_unit_sphere_compact R m.+1)).
Qed.

(** Source for [structure_projective_sphere_mass]: the
    positive finite mass used in Federer 3.3.4,
    pp. 290–291, computed by the actual two-to-one
    area identity of 3.2.28(4), p. 267, and
    the unit-sphere mass from 3.2.13, p. 250.
    Degree zero gives a single projective atom. *)
Theorem structure_projective_sphere_mass (R:realType) m:
  ((2:R)%:E * @hausdorff_measure R
    (inner_metric_space (@symmetric_inner_productP R (R_n R m.+1)
      (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1) 2))
      m (@structure_projective_sphere R m))%E=
    ((m.+1)%:R*euclidean_unit_ball_volume R m.+1)%:E.
Proof.
have hMan:=inner_smooth_submanifold_class (@spherical_unit_sphere_smooth R m.+1) 1%N.
rewrite subn1 /= in hMan.
have hArea:=@inner_projective_square_manifold_area R (R_n R m.+1)
  (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1)
  m.+1 (@coordinate_basis R m.+1) (@coordinate_basisP R m.+1)
  m 1%N (@euclidean_unit_sphere_set R m.+1) (leqnn 1%N) hMan
  (fun x hx=>hx)
  (fun x hx=>ltac:(change (inner_norm (@euclidean_inner_productP R m.+1) (-x)= 1);
    by rewrite inner_normN)).
have hSphere:=@hausdorff_unit_sphere_mass R m.+1 (ltn0Sn m).
rewrite subn1 /= in hSphere.
rewrite -hArea; exact:hSphere.
Qed.
