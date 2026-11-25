(** Federer (1969), 2.5.20, p. 114, final sentence: the variation of T for
    mu=h#gamma equals the image of gamma+ + gamma-. This proves the scalar
    value identity from the two least-upper-bound specifications. The
    bounded multiplier approximation is expanded in
    WeightedDaniellVariation.v; no variation identity is assumed. Source
    context: that file and CompactPushforwardSupport.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import HausdorffBinaryProduct CompactSupportFunctionUP CompactSupportProducts CompactSeparatedProduct
  CompactPushforwardSupport CompactUniformNorm FunctionLatticeUP VectorFunctionLattice
  DaniellIntegralUP DaniellVariationUP DaniellSpacePushforward DaniellSpaceCompactness
  VectorVariationFiniteBounds WeightedDaniellVariation ProductFibreVariationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [daniell_graph_fibre_variation]: the variation
    value at f is gamma+(f o g)+gamma-(f o g),
    supporting the final identification of Phi in Federer
    2.5.20, p. 114. The lower estimate uses actual
    continuous product tests, including near zeros of f o g. *)
Theorem daniell_graph_fibre_variation (R : realType) (X Y : metricType R)
    (g : Y -> X) (A P Q : (Y -> R) -> R) (f : X -> R) :
  compact (@setT Y) -> continuous g ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) A ->
  is_daniell_positive_variation (@compactly_supported_continuous_functions R Y) A P ->
  is_daniell_negative_variation (@compactly_supported_continuous_functions R Y) A Q ->
  positive_function_lattice (@compactly_supported_continuous_functions R X) f ->
  is_product_fibre_variation (daniell_pushforward (daniell_graph_map g) A) f
    (P (f \o g)+Q (f \o g)).
Proof.
move=> hY hg hA hP hQ hf.
have hp := compact_source_continuous_map_proper hY (@metric_hausdorff R X) hg.
have hfgK := compactly_supported_compose hg hp hf.1.
have hfg : positive_function_lattice (@compactly_supported_continuous_functions R Y) (f \o g).
  by split=> // y; exact: hf.2.
have hh := daniell_graph_map_continuous hg.
have hhp := compact_source_continuous_map_proper hY
  (hausdorff_binary_product (@metric_hausdorff R X) (@metric_hausdorff R Y)) hh.
have hL := @compact_support_vector_lattice R Y.
have hlin := daniell_compact_support_linear hA.
constructor.
- move=> u hu hub.
  have hup := compactly_supported_compose hh hhp hu.
  have hsym : lattice_symmetric_order_interval (@compactly_supported_continuous_functions R Y)
      (f \o g) (u \o daniell_graph_map g).
    split=> // y; exact: hub (g y) y.
  have hb := @finite_variation_sum_upper R Y _ A hL hlin.1 (f \o g)
    (P (f \o g)) (Q (f \o g)) hfg (hP _ hfg) (hQ _ hfg)
    (u \o daniell_graph_map g) hsym.
  exact: le_trans (ler_norm _) hb.
- move=> b hb.
  apply: (@compact_daniell_weighted_variation_least R Y A P Q (f \o g) b hY hA hP hQ hfg)=> r hr hr1.
  have hu := compactly_supported_separated_product hf.1 hr.
  apply: (hb (fun p : X*Y => f p.1 * r p.2) hu)=> x y.
  rewrite normrM (ger0_norm (hf.2 x)).
  have h := ler_wpM2l (hf.2 x) (hr1 y); by rewrite mulr1 in h.
Qed.
