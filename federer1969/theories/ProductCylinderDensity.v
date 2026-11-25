(** Federer (1969), 2.6.6, p. 120: the directed union L is dense in K(X) for
    the norm nu. This proof combines finite-coordinate uniform control with
    the sealed norm laws, including the empty finite set of coordinates.
    Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP CompactProductCylinders
  CompactUniformNorm UniformFunctionNorm ProductCylinderLattice FunctionSeminormDistance
  ScalarLipschitzExtensionUP VectorFunctionLattice.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_product_cylinders_uniformly_dense]: actual
    density assertion in Federer 2.6.6, p. 120, formulated using
    the uniform norm and finite-coordinate dependence. No countability
    or metrizability of the product is assumed. *)
Theorem compact_product_cylinders_uniformly_dense (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (x0 : prod_topology Y) :
  compact [set: prod_topology Y] ->
  is_pseudometric_dense_subset (@compactly_supported_continuous_functions R (prod_topology Y))
    (@continuous_product_cylinders R I Y)
    (function_seminorm_distance (@compact_support_uniform_norm R (prod_topology Y))).
Proof.
move=> hc f hf e he.
have [F [g [hg [hdep hnear]]]] := @compact_product_cylinder_approximation R I Y x0 f e hc hf.1 he.
have hgK : compactly_supported_continuous_functions g.
  split=> //; exact: (subclosed_compact (@real_function_support_closed R (prod_topology Y) g) hc (@subsetT _ _)).
exists g; split; first by split=> //; exists F.
apply: compact_support_uniform_norm_strict_bound=> //.
exact: (@vector_function_lattice_difference R (prod_topology Y) _
  (@compact_support_vector_lattice R (prod_topology Y)) f g hf hgK).
Qed.
