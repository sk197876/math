(** Federer (1969), 2.5.20, p. 114: Phi is the K(X)-regular measure
    associated with g#(gamma+ + gamma-). The variation identity is proved in
    DaniellGraphVariation.v; here actual integrals transfer it to the SAME
    measure selected by disintegration. Positive parts extend the identity
    from K(X)+ to K(X), and 2.5.3 gives uniqueness. Source context:
    DaniellGraphVariation.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureIntegralUP SummableRealFunctionUP
  CompactSupportFunctionUP CompactSupportFunctionLattice FunctionLatticeUP
  FunctionLatticeRegularityUP FunctionLatticeRegularUniqueness RealIntegralFunctionalUP
  PositiveDifferenceFunctional CompactPositiveRepresentationRadon CompactDaniellTotalVariation
  CompactPushforwardSupport DaniellSpacePushforward DaniellSpaceWeakTopology
  DaniellIntegralUP DaniellVariationUP DaniellGraphVariation ProductFibreVariationUP
  DaniellDisintegrationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [daniell_graph_variation_positive_integral]:
    positive-test identity for the final assertion of Federer
    2.5.20, p. 114. Phi is the original disintegration
    measure; no new representing measure is substituted. *)
Theorem daniell_graph_variation_positive_integral (R : realType) (X Y : metricType R)
    (g : Y -> X) (A P Q : (Y -> R) -> R) (phi : set X -> \bar R)
    (k : X -> daniell_weak_space (@compactly_supported_continuous_functions R Y)) :
  compact (@setT Y) -> continuous g ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) A ->
  is_daniell_positive_variation (@compactly_supported_continuous_functions R Y) A P ->
  is_daniell_negative_variation (@compactly_supported_continuous_functions R Y) A Q ->
  is_daniell_disintegration (daniell_pushforward (daniell_graph_map g) A) phi k ->
  is_real_integral_functional phi
    (positive_function_lattice (@compactly_supported_continuous_functions R X))
    (fun f => P (f \o g)+Q (f \o g)).
Proof.
move=> hY hg hA hP hQ hD f hf.
have [a [hi ha]] := daniell_disintegration_variation hD hf.
have hvar := daniell_graph_fibre_variation hY hg hA hP hQ hf.
have he := product_fibre_variation_unique ha hvar.
by rewrite -he.
Qed.

(** Source for [daniell_graph_variation_measure]: the complete
    last sentence of Federer 2.5.20, p. 114: Phi is
    K(X) regular and represents g#(gamma+ + gamma-)
    on all K(X). The variations are extended from the
    positive cone by their linear parts formula. *)
Theorem daniell_graph_variation_measure (R : realType) (X Y : metricType R)
    (g : Y -> X) (A P Q : (Y -> R) -> R) (phi : set X -> \bar R)
    (k : X -> daniell_weak_space (@compactly_supported_continuous_functions R Y)) :
  compact (@setT Y) -> continuous g ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) A ->
  is_daniell_positive_variation (@compactly_supported_continuous_functions R Y) A P ->
  is_daniell_negative_variation (@compactly_supported_continuous_functions R Y) A Q ->
  is_daniell_disintegration (daniell_pushforward (daniell_graph_map g) A) phi k ->
  is_function_lattice_regular (@compactly_supported_continuous_functions R X) phi /\
  is_real_integral_functional phi (@compactly_supported_continuous_functions R X)
    (daniell_pushforward g (compact_daniell_total_variation P Q)).
Proof.
move=> hY hg hA hP hQ hD; split; first exact: daniell_disintegration_regular hD.
have hpos := daniell_graph_variation_positive_integral hY hg hA hP hQ hD.
have hfull := positive_parts_extend_integral_representation (daniell_disintegration_measure hD)
  (@compactly_supported_continuous_functions_lattice R X) hpos.
move=> f hf; exact: hfull f hf.
Qed.

(** Source for [daniell_graph_variation_measure_unique]:
    "the K(X) regular measure associated with" in the
    last sentence of Federer 2.5.20, p. 114, includes
    uniqueness from 2.5.3, p. 94. *)
Theorem daniell_graph_variation_measure_unique (R : realType) (X Y : metricType R)
    (g : Y -> X) (A P Q : (Y -> R) -> R) (phi psi : set X -> \bar R)
    (k : X -> daniell_weak_space (@compactly_supported_continuous_functions R Y)) :
  compact (@setT Y) -> continuous g ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) A ->
  is_daniell_positive_variation (@compactly_supported_continuous_functions R Y) A P ->
  is_daniell_negative_variation (@compactly_supported_continuous_functions R Y) A Q ->
  is_daniell_disintegration (daniell_pushforward (daniell_graph_map g) A) phi k ->
  is_measure psi -> is_function_lattice_regular (@compactly_supported_continuous_functions R X) psi ->
  is_real_integral_functional psi (@compactly_supported_continuous_functions R X)
    (daniell_pushforward g (compact_daniell_total_variation P Q)) -> phi=psi.
Proof.
move=> hY hg hA hP hQ hD hm hr hrep.
have [hrphi hI] := daniell_graph_variation_measure hY hg hA hP hQ hD.
apply: funext=> S.
exact (@function_lattice_regular_representation_unique R X
  (@compactly_supported_continuous_functions R X)
  (daniell_pushforward g (compact_daniell_total_variation P Q))
  (@compactly_supported_continuous_functions_lattice R X) phi psi
  (daniell_disintegration_measure hD) hm hI hrep hrphi hr S).
Qed.
