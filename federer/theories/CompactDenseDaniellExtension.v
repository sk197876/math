(** Federer (1969), 2.6.6, p. 120: a normalized, uniformly bounded linear
    functional on the dense union L extends to a monotone Daniell integral
    on K(X), using 2.5.13. This is the abstract extension step shared with
    the inverse-limit paragraph, pp. 120–121; the product-specific
    consistency and density are separate theorems. Source context:
    UniformFunctionNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import FunctionLatticeUP CompactSupportFunctionUP CompactSupportFunctionLattice DaniellSpaceCompactSpace
  UniformFunctionNormUP UniformFunctionNorm CompactUniformNorm NormalizedUniformFunctional
  DenseLinearFunctionExtension ScalarLipschitzExtensionUP FunctionSeminormDistance VectorFunctionLattice
  FunctionLatticeSeminormUP DaniellIntegralUP MonotoneDaniellIntegralUP ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_dense_daniell_extension_exists]: the continuous
    extension and Daniell conclusion in Federer 2.6.6, p. 120.
    The initial functional and its domain are explicit hypotheses;
    this lemma alone does not assert existence of product marginals. *)
Theorem compact_dense_daniell_extension_exists (R : realType) (X : topologicalType)
    (D : set (X -> R)) (A : (X -> R) -> R) :
  hausdorff_space X -> compact (@setT X) ->
  is_vector_function_lattice D -> D (fun _=>1) ->
  (forall f, D f -> compactly_supported_continuous_functions f) ->
  is_pseudometric_dense_subset (@compactly_supported_continuous_functions R X) D
    (function_seminorm_distance (@compact_support_uniform_norm R X)) ->
  is_linear_functional_on_functions D A -> A (fun _=>1) = 1 ->
  (forall f, D f -> `|A f|<=compact_support_uniform_norm f) ->
  exists B, is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) B /\
    B (fun _=>1) = 1 /\
    is_scalar_lipschitz_extension (@compactly_supported_continuous_functions R X) D
      (function_seminorm_distance (@compact_support_uniform_norm R X)) A B.
Proof.
move=> hh hc hD hD1 hDK hdense hA hA1 hb.
pose K := @compactly_supported_continuous_functions R X.
pose N := @compact_support_uniform_norm R X.
have hK := @compact_support_vector_lattice R X.
have hN := @compact_support_uniform_norm_laws R X.
have [B [hlin [hext hbound]]] := @dense_linear_function_extension_exists R X K D N A
  hK hD hDK hN hdense hA hb.
have hB1 : B (fun _=>1) = 1 by rewrite (hext.1 _ hD1) hA1.
have hmono : forall f g, K f -> K g -> function_le f g -> B f<=B g.
  exact: (@normalized_uniform_functional_monotone R X K N B hK (hDK _ hD1)
    (@compact_support_uniform_norm_specification R X) hlin hB1 hbound).
have hBd : is_daniell_integral K B.
  apply: (@sup_norm_bounded_daniell R X hh hc B hlin).
  exists 1; split; first exact: ler01.
  move=> f hf c hc0 hfc; rewrite mul1r.
  exact: le_trans (hbound f hf) (@uniform_function_norm_least R X f _ (compact_support_uniform_norm_specification hf) c hc0 hfc).
exists B; split; last by split.
constructor.
- exact: daniell_integral_add hBd.
- exact: daniell_integral_scale hBd.
- exact: hmono.
- move=> f g hf hg hi; split.
  + move=> n m hnm; rewrite lee_fin; apply: (@hmono (f n) (f m) (hf n) (hf m))=> x.
    exact: (hi x).1 n m hnm.
  + exact: (@daniell_integral_increasing_continuity R X K B hBd f g hf hg hi).
Qed.
