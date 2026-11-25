(** Federer (1969), 2.5.20, p. 114: transfer the vector representation
    through the weakly continuous identification of E* with Daniell
    integrals on K(Y). These are the measurable-family and integral-formula
    conclusions; the support assertion is treated separately. Source
    context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactFunctionSpaceUP CompactFunctionSpaceLaws CompactFunctionCurrying
  CompactFunctionDualUP CompactFunctionDual CompactProductVectorFunctional
  CompactProductVectorRepresentation ContinuousVectorFamily DaniellDisintegrationUP
  CompactSupportFunctionUP CompactProductSections VectorDaniellHypotheses
  VectorDaniellRepresentationUP VectorDaniellNormalisationUP MeasureUP RadonMeasureUP
  MeasurableTotalBasic BorelFunctionBasic DaniellIntegralUP DaniellSpaceWeakTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dual_family_daniell_decomposition]: the
    first displayed formula of Federer 2.5.20, p. 114,
    follows from 2.5.12 after identifying E* with the
    Daniell integrals. No support assertion is assumed here. *)
Theorem dual_family_daniell_decomposition (R : realType) (X Y : topologicalType)
    (E : lmodType R) (ev : E -> Y -> R) (hE : is_compact_function_space ev)
    (mu : ((X*Y) -> R) -> R) (phi : set X -> \bar R)
    (k : X -> weak_dual_space (compact_function_norm_laws hE))
    (F : weak_dual_space (compact_function_norm_laws hE) ->
      daniell_weak_space (@compactly_supported_continuous_functions R Y)) :
  hausdorff_space Y -> compact (@setT Y) -> is_measure phi ->
  is_compact_function_dual_identification ev F ->
  is_vector_daniell_density phi
    (@continuous_normed_functions R X E _ (compact_function_norm_laws hE))
    (compact_product_vector_functional ev mu) k ->
  is_daniell_integral_decomposition phi mu (fun x => F (k x)).
Proof.
move=> hh hY hm hF hk; constructor.
- move=> x; exact (@compact_function_dual_daniell R Y E (compact_function_norm ev)
    (compact_function_norm_laws hE) ev F hF (k x)).
- exact (@measurable_total_borel_postcomposition R X
    (weak_dual_space (compact_function_norm_laws hE))
    (daniell_weak_space (@compactly_supported_continuous_functions R Y)) phi hm k F
    (vector_daniell_density_measurable hk)
    (continuous_borel_function (@compact_function_dual_continuous R Y E
      (compact_function_norm ev) (compact_function_norm_laws hE) ev F hF))).
- move=> f hf.
  have [w [hw he]] := compact_function_uncurry_surjective hE hh hY hf.
  have hi := vector_daniell_density_integral hk hw.
  have hpair : (fun x => F (k x) (fun y => f (x,y)))=(fun x => val (k x) (w x)).
    apply: funext=> x; rewrite -he /compact_function_uncurry.
    exact (@compact_function_dual_evaluation R Y E (compact_function_norm ev)
      (compact_function_norm_laws hE) ev F hF (k x) (w x)).
  rewrite hpair; move: hi; by rewrite /compact_product_vector_functional he.
Qed.

(** Source for [compact_product_daniell_decomposition_exists]:
    Radon measure and measurable Daniell-integral family in
    the first paragraph of Federer 2.5.20, p. 114.
    This theorem establishes the formula; the further support
    and graph-specialization claims remain distinct statements. *)
Theorem compact_product_daniell_decomposition_exists (R : realType) (X Y : metricType R)
    (E : lmodType R) (ev : E -> Y -> R) (hE : is_compact_function_space ev)
    (mu : ((X*Y) -> R) -> R) :
  compact (@setT X) -> compact (@setT Y) ->
  is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type) mu ->
  exists phi : set X -> \bar R, exists k : X -> daniell_weak_space
      (@compactly_supported_continuous_functions R Y),
    is_measure phi /\ is_radon_measure phi /\ is_daniell_integral_decomposition phi mu k.
Proof.
move=> hX hY hmu.
have [phi [k [hm [hr [hrep [hreg hk]]]]]] := compact_product_vector_representation hE hX hY hmu.
pose F := @compact_function_dual_map R Y E ev hE (@metric_hausdorff R Y) hY.
have hF := @compact_function_dual_map_specification R Y E ev hE (@metric_hausdorff R Y) hY.
exists phi,(fun x => F (k x)); split=> //; split=> //.
exact (@dual_family_daniell_decomposition R X Y E ev hE mu phi k F
  (@metric_hausdorff R Y) hY hm hF (normalised_vector_density_laws hk)).
Qed.
