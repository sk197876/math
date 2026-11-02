(** Federer (1969), 2.5.20, p. 114: complete graph specialization of the
    disintegration theorem. The measure and kernel come from the sealed
    disintegration of h#gamma; the formula, fibre support, and
    identification with the regular measure for g#(gamma+ + gamma-) are
    consequences. Source context: CompactPushforwardSupport.v and
    WeightedDaniellVariation.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportDaniellSupport
  CompactPushforwardSupport DaniellSpacePushforward DaniellSpaceWeakTopology
  DaniellIntegralUP DaniellVariationUP CompactDaniellTotalVariation
  DaniellDisintegrationUP DaniellDisintegration DaniellGraphDecomposition
  DaniellGraphVariationMeasure FunctionLatticeRegularityUP RealIntegralFunctionalUP
  MeasureIntegralUP SummableRealFunctionUP MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_metric_daniell_graph_disintegration]:
    all assertions of the second paragraph of Federer
    2.5.20, p. 114. The measure is the original
    disintegration variation measure, not an independently
    chosen measure asserted to have the same properties. *)
Theorem compact_metric_daniell_graph_disintegration (R : realType) (X Y : metricType R)
    (g : Y -> X) (A : (Y -> R) -> R) :
  compact (@setT X) -> compact (@setT Y) -> continuous g ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) A ->
  exists phi : set X -> \bar R, exists k : X -> daniell_weak_space
    (@compactly_supported_continuous_functions R Y),
    is_daniell_disintegration (daniell_pushforward (daniell_graph_map g) A) phi k /\
    (forall f, compactly_supported_continuous_functions f ->
      is_measure_integral phi (real_total_integrand (fun x => k x f)) (A f)%:E) /\
    measure_almost_everywhere phi [set x |
      compact_support_daniell_support (k x) `<=` [set y | g y=x]] /\
    forall P Q, is_daniell_positive_variation (@compactly_supported_continuous_functions R Y) A P ->
      is_daniell_negative_variation (@compactly_supported_continuous_functions R Y) A Q ->
      is_function_lattice_regular (@compactly_supported_continuous_functions R X) phi /\
      is_real_integral_functional phi (@compactly_supported_continuous_functions R X)
        (daniell_pushforward g (compact_daniell_total_variation P Q)).
Proof.
move=> hX hY hg hA.
have hmu := daniell_graph_pushforward_daniell hY hg hA.
pose phi := daniell_disintegration_measure_value hX hY hmu.
pose k := daniell_disintegration_kernel hX hY hmu.
have hD := compact_metric_daniell_disintegration hX hY hmu.
exists phi,k; split; first exact hD.
split; first exact: daniell_graph_decomposition_formula hX hD.
split; first exact: daniell_graph_decomposition_fibre_support hY hg hA hD.
move=> P Q hP hQ; exact: daniell_graph_variation_measure hY hg hA hP hQ hD.
Qed.
