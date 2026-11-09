(** Federer (1969), 3.3.17, p. 300: original uniform
    uniform cone tests with the original all-radius bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanBallVolume StructureConeDensityUP StructureSmallConeCriterionUP MetricDensities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_uniform_cone_test]: the all-radius
    bound in B(p,s,lambda,delta) in Federer 3.3.17, p. 300.
    The actual cost of 3.3.2 includes r^(-m)s^(-m); its bound
    is alpha(m)*lambda. All positive radii through delta remain. *)
Definition structure_uniform_cone_test (R:realType) n m (hmn:(m<=n)%N)
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (p:euclidean_projection_space R n m) (s lam delta:R):=
  [set a|forall r:R,0<r<=delta ->
    (structure_cone_cost hmn psi setT (a,p) r s<=(euclidean_unit_ball_volume R m*lam)%:E)%E].

(** Source for [structure_density_cone_test]: the ORIGINAL
    B(p,s,lambda,delta) in Federer 3.3.17, p. 300, retaining
    the all-radius cone bound and strict upper-density inequality.
    The original upper density may be infinite. No nullity or
    rectifiability conclusion is part of this definition. *)
Definition structure_density_cone_test (R:realType) n m (hmn:(m<=n)%N)
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (p:euclidean_projection_space R n m) (s lam delta:R):=
  structure_uniform_cone_test hmn psi p s lam delta `&`
    [set a|(lam%:E<(structure_small_cone_constant R m)%:E*upper_metric_density m psi a)%E].
