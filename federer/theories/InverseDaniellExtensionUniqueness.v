(** Federer (1969), 2.6.6, pp. 120–121: uniqueness of the inverse-limit
    integral from all coordinate marginals. The proof uses the established
    uniform density and norm-one continuity of normalized monotone
    functionals. Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactInverseSystemUP CompactInverseLimitUP InverseDaniellFamilyUP
  InverseLimitPullbackLattice InverseLimitPullbackDensity InverseLimitClosedCoordinate NormalizedProductSpace
  CompactSupportFunctionUP CompactUniformNorm UniformFunctionNorm FunctionSeminormDistance
  NormalizedDaniellUniformLipschitz ScalarLipschitzExtensionUP DenseScalarExtensionUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inverse_limit_daniell_integral_unique]: uniqueness
    in the inverse-limit extension of Federer 2.6.6,
    pp. 120–121, on K(X). Ambient values outside K(X)
    are not claimed to be unique. *)
Theorem inverse_limit_daniell_integral_unique (R : realType) (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (X : topologicalType) (p : forall i, X -> Y i)
    (A : forall i, (Y i -> R) -> R) (B D : (X -> R) -> R) :
  is_compact_inverse_system le b -> is_compact_inverse_limit le b p ->
  is_consistent_inverse_daniell_family le b A ->
  is_inverse_limit_daniell_integral p A B -> is_inverse_limit_daniell_integral p A D ->
  forall f, compactly_supported_continuous_functions f -> B f=D f.
Proof.
move=> hs hl hA [hB [hB1 hBA]] [hD [hD1 hDA]].
have [u0 _] := @normalized_daniell_product_nonempty R I Y A
  (@inverse_daniell_family_integral R I le Y b A hA) (@inverse_daniell_family_one R I le Y b A hA).
have [u hu] := compact_inverse_family_exists u0 hs.
have [x0 hx0] := compact_inverse_limit_realizes_family hl hu.
pose K := @compactly_supported_continuous_functions R X.
pose L := @inverse_limit_pullbacks R I Y X p.
pose d := function_seminorm_distance (@compact_support_uniform_norm R X).
have hd := @function_seminorm_distance_laws R X K _ (@compact_support_vector_lattice R X) (@compact_support_uniform_norm_laws R X).
have hLK := @inverse_limit_pullback_membership R I le Y b X p hl.
have hc := compact_inverse_limit_compact hl.
have hBd := normalized_daniell_uniform_lipschitz hc hB hB1.
have hDd := normalized_daniell_uniform_lipschitz hc hD hD1.
have heB : is_scalar_lipschitz_extension K L d B B by split.
have heD : is_scalar_lipschitz_extension K L d B D.
  split=> // f [i [g [hg ->]]]; by rewrite (hDA i g hg) (hBA i g hg).
exact: (@dense_scalar_lipschitz_extension_unique R _ K L d B B D hd hLK
  (@inverse_limit_pullbacks_uniformly_dense R I le Y b X p x0 hs hl) heB heD).
Qed.
