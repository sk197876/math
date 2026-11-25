(** Federer (1969), 3.3.4, p. 291: all
    actual projective reference ball ratios tend
    to one. Derive a point from the actual
    almost-everywhere theorem 3.2.19, then use
    transitive isometric invariance; no extra
    density hypothesis is supplied. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric SymmetricGrading InnerSymmetric InnerSymmetricPositivity
  StructureProjectiveSphere StructureProjectiveMassBounds StructureProjectiveSpace
  StructureProjectiveMeasure StructureProjectiveMeasureInvariant
  FiniteInnerSmoothSubmanifoldUP FiniteInnerManifoldDensityPoint
  HomogeneousMetricDensity MetricDensities PartialFunctionUP
  PositiveRightOrderLimit PositiveRadiusCommonOrderLimit
  EuclideanOrthogonalInvariantMeasures IsotropyGroupTopology LinearGroupTopology LinearGroupSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Density.
Variable R:realType.
Variable m:nat.
Local Notation hB:=(@euclidean_inner_productP R m.+1).
Local Notation hb:=(@coordinate_basisP R m.+1).
Local Notation O:=(euclidean_orthogonal_group R m.+1).
Local Notation M:=(structure_projective_space R m).
Variables (mulS:O->O->O) (invS:O->O) (eS:O).
Hypothesis hS:is_subgroup_restriction (linear_group_mul hB hb)
  (linear_group_inv hB hb) (linear_group_unit hB hb) O mulS invS eS.

(** Source for [structure_projective_density_one]:
    the reference density at every z in
    T(U) equals one, Federer 3.3.4, p. 291.
    Actual compact manifold rectifiability and
    positive mass discharge the almost-everywhere
    premise, and actual invariant balls transfer
    the common density to the original point. *)
Theorem structure_projective_density_one (x:M):
  partial_function_graph (metric_density m (@structure_projective_measure R m)) x 1%E.
Proof.
have hMan:=inner_smooth_submanifold_class (@structure_projective_sphere_smooth R m) 1%N.
have hPositive: (0<@HausdorffMeasure.hausdorff_measure R
    (inner_metric_space (@symmetric_inner_productP R (R_n R m.+1)
      (@euclidean_inner_product R m.+1) hB 2)) m (@structure_projective_sphere R m))%E:=
  (andP (@structure_projective_sphere_positive_finite R m)).1.
have [y hy]:=@finite_inner_compact_manifold_density_point R
  (symmetric_power (R_n R m.+1) 2)
  (@symmetric_inner_form R (R_n R m.+1) (@euclidean_inner_product R m.+1) hB 2)
  (@symmetric_inner_productP R (R_n R m.+1) (@euclidean_inner_product R m.+1) hB 2)
  m (@structure_projective_sphere R m) hMan (@structure_projective_sphere_compact R m) hPositive.
exact:(@metric_density_center_independent R M (@structure_projective_measure R m) m y x 1%E
  (@structure_projective_closed_ball_mass R m mulS invS eS hS y x)).1 hy.
Qed.

(** Source for [structure_projective_ball_density_limit]:
    the ordinary all-positive-radius limit one
    of the actual reference ball ratios in
    Federer 3.3.4, p. 291. Both independent
    upper and lower density values are used;
    no chosen radius sequence replaces the limit. *)
Theorem structure_projective_ball_density_limit (x:M):
  positive_right_extended_order_limit
    (metric_ball_density m (@structure_projective_measure R m) x) 1%E.
Proof.
have [hUpper hLower]:=(metric_density_graph m (@structure_projective_measure R m) x 1%E).1
  (structure_projective_density_one x).
exact:(positive_radius_common_order_limit hLower hUpper).
Qed.
End Density.
