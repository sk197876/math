(** Federer (1969), 2.5.20, p. 114: private existence proof for the full
    first-paragraph disintegration. It uses the sealed K(Y), verifies the
    hypotheses of 2.5.12, transfers to actual Daniell integrals, and proves
    the support claim. The variation measure is retained through its
    abstract least-bound law for later identification. Source context:
    CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactFunctionSpaceUP CompactFunctionSpaceLaws CompactFunctionSpace
  CompactFunctionDualUP CompactFunctionDual CompactProductVectorRepresentation
  CompactProductDaniellDecomposition CompactProductVariation CompactProductVectorFunctional
  CompactPositiveRepresentationRadon PositiveDifferenceFunctional PositiveLatticeRegularity
  ContinuousVectorFamily CompactSupportVectorContinuity SubtypeCompactHausdorff
  CompactSupportFunctionUP CompactSupportFunctionLattice VectorDaniellHypotheses
  VectorDaniellNormalisationUP DaniellIntegralUP DaniellSpaceWeakTopology
  DaniellDisintegrationUP DaniellDisintegrationSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [daniell_disintegration_exists]: complete
    first-paragraph existence statement of Federer 2.5.20,
    p. 114, including the inferred support inclusion.
    All hypotheses of the vector representation are verified
    for the concrete compact metric spaces. *)
Theorem daniell_disintegration_exists (R : realType) (X Y : metricType R)
    (mu : ((X*Y) -> R) -> R) :
  compact (@setT X) -> compact (@setT Y) ->
  is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) mu ->
  exists phi : set X -> \bar R, exists k : X -> daniell_weak_space
    (@compactly_supported_continuous_functions R Y), is_daniell_disintegration mu phi k.
Proof.
move=> hX hY hmu.
pose E := compact_function_space R Y.
pose ev := @compact_function_evaluate R Y.
have hE := @compact_function_space_specification R Y.
have [phi [a [hm [hr [hrep [hreg ha]]]]]] := compact_product_vector_representation hE hX hY hmu.
pose F := @compact_function_dual_map R Y E ev hE (@metric_hausdorff R Y) hY.
have hF := @compact_function_dual_map_specification R Y E ev hE (@metric_hausdorff R Y) hY.
pose k x := F (a x).
have hk := @dual_family_daniell_decomposition R X Y E ev hE mu phi a F
  (@metric_hausdorff R Y) hY hm hF (normalised_vector_density_laws ha).
have hregK := (function_lattice_regular_positive_iff _ _).1 hreg.
have hrepK := positive_parts_extend_integral_representation hm
  (@compactly_supported_continuous_functions_lattice R X) hrep.
have hs := compact_daniell_decomposition_support hX hY hm hr hrepK hregK hmu hk.
have hQ := @continuous_normed_functions_vector_space R X E _ (compact_function_norm_laws hE).
have hM := @continuous_normed_functions_compact_module R X E _ (compact_function_norm_laws hE) hX.
have hT := compact_product_vector_functional_order_bounded hE hX hY hmu.
have hV := compact_support_vector_variation_functional
  (@metric_hausdorff R X) (compact_space_locally_compact hX) hQ hM hT.
exists phi,k; constructor=> //.
move=> f hf; exists (variation_integral (compact_function_norm ev)
  (@continuous_normed_functions R X E _ (compact_function_norm_laws hE))
  (compact_product_vector_functional ev mu) f); split.
- exact: hrep f hf.
- exact (@compact_product_vector_variation_specification R X Y E ev hE mu f
    (@metric_hausdorff R Y) hX hY hV hf).
Qed.

(** Source for [daniell_disintegration_pair_exists]: packaging
    the verified measure and kernel for the opaque interface
    of Federer 2.5.20, p. 114; this is implementation
    bookkeeping, not an additional mathematical assertion. *)
Theorem daniell_disintegration_pair_exists (R : realType) (X Y : metricType R)
    (mu : ((X*Y) -> R) -> R) :
  compact (@setT X) -> compact (@setT Y) ->
  is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) mu ->
  exists p : ((set X -> \bar R) * (X -> daniell_weak_space
    (@compactly_supported_continuous_functions R Y)))%type,
    is_daniell_disintegration mu p.1 p.2.
Proof.
move=> hX hY hmu; have [phi [k hk]] := daniell_disintegration_exists hX hY hmu.
by exists (phi,k).
Qed.
