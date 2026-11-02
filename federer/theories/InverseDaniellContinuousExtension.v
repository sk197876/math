(** Federer (1969), 2.6.6, pp. 120–121: the same continuous-extension
    characterization for compact inverse limits. Uniqueness here allows any
    continuous competitor agreeing on coordinate pullbacks. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import CompactInverseSystemUP CompactInverseLimitUP InverseDaniellFamilyUP
  InverseDaniellIntegral InverseLimitPullbackLattice InverseLimitPullbackDensity
  NormalizedProductSpace NormalizedDaniellUniformLipschitz DenseScalarContinuousUniqueness
  CompactSupportFunctionUP MonotoneDaniellIntegralSum FunctionSeminormDistance UniformFunctionNorm
  FunctionLatticeSeminormUP DaniellSpaceCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inverse_limit_integral_continuous_linear]:
    the continuous linear extension for inverse limits in
    Federer 2.6.6, pp. 120–121, for the uniform norm. *)
Theorem inverse_limit_integral_continuous_linear (R : realType) (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (X : topologicalType) (p : forall i, X -> Y i)
    (A : forall i, (Y i -> R) -> R)
    (hs : is_compact_inverse_system le b) (hl : is_compact_inverse_limit le b p)
    (hA : is_consistent_inverse_daniell_family le b A) :
  is_linear_functional_on_functions (@compactly_supported_continuous_functions R X)
    (@inverse_limit_daniell_integral R I le Y b X p A hs hl hA) /\
  is_scalar_continuous_on_set (@compactly_supported_continuous_functions R X)
    (function_seminorm_distance (@compact_support_uniform_norm R X))
    (@inverse_limit_daniell_integral R I le Y b X p A hs hl hA).
Proof.
have hB := @inverse_limit_daniell_integral_specification R I le Y b X p A hs hl hA.
split.
- exact: daniell_compact_support_linear (monotone_daniell_integral_is_daniell hB.1).
- apply: scalar_lipschitz_implies_continuous.
  exact: normalized_daniell_uniform_lipschitz (compact_inverse_limit_compact hl) hB.1 hB.2.1.
Qed.

(** Source for [inverse_limit_continuous_extension_unique]:
    uniqueness of the continuous extension in the inverse-limit
    generalization of Federer 2.6.6, pp. 120–121. *)
Theorem inverse_limit_continuous_extension_unique (R : realType) (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (X : topologicalType) (p : forall i, X -> Y i)
    (A : forall i, (Y i -> R) -> R)
    (hs : is_compact_inverse_system le b) (hl : is_compact_inverse_limit le b p)
    (hA : is_consistent_inverse_daniell_family le b A) (D : (X -> R) -> R) :
  is_scalar_continuous_on_set (@compactly_supported_continuous_functions R X)
    (function_seminorm_distance (@compact_support_uniform_norm R X)) D ->
  (forall i f, compactly_supported_continuous_functions f -> D (f \o p i)=A i f) ->
  forall f, compactly_supported_continuous_functions f ->
    D f=@inverse_limit_daniell_integral R I le Y b X p A hs hl hA f.
Proof.
move=> hD hDA.
have hB := @inverse_limit_daniell_integral_specification R I le Y b X p A hs hl hA.
have [x0 _] := normalized_daniell_space_nonempty (monotone_daniell_integral_is_daniell hB.1) hB.2.1.
apply: (@dense_scalar_continuous_unique R (X -> R) _ (@inverse_limit_pullbacks R I Y X p)).
- exact: (@inverse_limit_pullback_membership R I le Y b X p hl).
- exact: (@inverse_limit_pullbacks_uniformly_dense R I le Y b X p x0 hs hl).
- exact: hD.
- exact: (@inverse_limit_integral_continuous_linear R I le Y b X p A hs hl hA).2.
- move=> f [i [g [hg ->]]]; by rewrite (hDA i g hg) (hB.2.2 i g hg).
Qed.
