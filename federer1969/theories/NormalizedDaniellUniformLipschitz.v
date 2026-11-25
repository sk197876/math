(** Federer (1969), 2.6.6, p. 120: normalized monotone Daniell functionals
    have norm one and are continuous for nu. These consequences support
    uniqueness from the finite marginals. Source context and norm
    conventions: UniformFunctionNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP CompactUniformNorm UniformFunctionNorm UniformFunctionNormUP
  NormalizedMonotoneUniformBound DaniellSpaceCompactSpace DaniellSpaceCompactness
  MonotoneDaniellIntegralUP MonotoneDaniellIntegralSum VectorFunctionLattice
  FunctionSeminormDistance ScalarLipschitzExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normalized_daniell_uniform_bound]: the norm-one
    estimate in Federer 2.6.6, p. 120, for every normalized
    monotone Daniell functional on K(X) when X is compact. *)
Lemma normalized_daniell_uniform_bound (R : realType) (X : topologicalType)
    (B : (X -> R) -> R) :
  compact (@setT X) -> is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) B ->
  B (fun _=>1) = 1 -> forall f, compactly_supported_continuous_functions f -> `|B f|<=compact_support_uniform_norm f.
Proof.
move=> hc hB hB1 f hf; apply: (@normalized_monotone_functional_uniform_bound R X _ B
  (@compact_support_vector_lattice R X) (@compact_space_constant_one R X hc)
  (@daniell_compact_support_linear R X B (monotone_daniell_integral_is_daniell hB)) hB1
  (@monotone_daniell_integral_monotone R X _ B hB) f _ hf).
exact: compact_support_uniform_norm_specification hf.
Qed.

(** Source for [normalized_daniell_uniform_lipschitz]: the uniform
    continuity bound used for uniqueness in Federer 2.6.6, p. 120. *)
Theorem normalized_daniell_uniform_lipschitz (R : realType) (X : topologicalType)
    (B : (X -> R) -> R) :
  compact (@setT X) -> is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) B ->
  B (fun _=>1) = 1 ->
  is_scalar_lipschitz_on_set (@compactly_supported_continuous_functions R X)
    (function_seminorm_distance (@compact_support_uniform_norm R X)) B.
Proof.
move=> hc hB hB1 f g hf hg.
have hK := @compact_support_vector_lattice R X.
have hlin := @daniell_compact_support_linear R X B (monotone_daniell_integral_is_daniell hB).
rewrite -(@vector_lattice_additive_difference R X _ B hK hlin.1 f g hf hg).
exact (@normalized_daniell_uniform_bound R X B hc hB hB1 (fun x=>f x-g x)
  (@vector_function_lattice_difference R X _ hK f g hf hg)).
Qed.
