(** Federer (1969), 2.5.20, p. 114, second paragraph: specialize to
    mu=h#gamma with h(y)=(g(y),y). The test u(x,y)=f(y) gives the displayed
    formula for gamma, and the image support gives spt k(x) subset
    g^{-1}{x}. The identification of the variation measure is separate.
    Source context: CompactPushforwardSupport.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import HausdorffBinaryProduct CompactSupportFunctionUP CompactSeparatedProduct
  CompactPushforwardSupport DaniellIntegralUP DaniellSpacePushforward
  DaniellSpaceCompactSpace DaniellSpaceWeakTopology CompactSupportDaniellSupport
  DaniellDisintegrationUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [daniell_graph_pushforward_daniell]: mu=h#gamma
    is a Daniell integral on K(X times Y), Federer
    2.5.20, p. 114, by the proper pushforward of
    2.5.19, p. 113. *)
Theorem daniell_graph_pushforward_daniell (R : realType) (X Y : metricType R)
    (g : Y -> X) (A : (Y -> R) -> R) :
  compact (@setT Y) -> continuous g ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) A ->
  is_daniell_integral (@compactly_supported_continuous_functions R (X*Y)%type)
    (daniell_pushforward (daniell_graph_map g) A).
Proof.
move=> hY hg hA; have hh := daniell_graph_map_continuous hg.
have hp := compact_source_continuous_map_proper hY
  (hausdorff_binary_product (@metric_hausdorff R X) (@metric_hausdorff R Y)) hh.
exact (@daniell_pushforward_daniell R Y (X*Y)%type (daniell_graph_map g) hh hp A hA).
Qed.

(** Source for [daniell_graph_decomposition_formula]: the
    displayed gamma(f)=integral k(x)(f) in Federer 2.5.20,
    p. 114. The measure and kernel are exactly those
    of the disintegration of h#gamma. *)
Theorem daniell_graph_decomposition_formula (R : realType) (X Y : metricType R)
    (g : Y -> X) (A : (Y -> R) -> R) (phi : set X -> \bar R)
    (k : X -> daniell_weak_space (@compactly_supported_continuous_functions R Y)) :
  compact (@setT X) ->
  is_daniell_disintegration (daniell_pushforward (daniell_graph_map g) A) phi k ->
  forall f, compactly_supported_continuous_functions f ->
    is_measure_integral phi (real_total_integrand (fun x => k x f)) (A f)%:E.
Proof.
move=> hX hD f hf.
have hu := compactly_supported_separated_product (@compact_space_constant_one R X hX) hf.
have he : (fun p : X*Y => (1 : R)*f p.2)=(fun p : X*Y => f p.2).
  by apply: funext=> p; rewrite mul1r.
rewrite he in hu.
have hi := daniell_decomposition_integral (daniell_disintegration_formula hD) hu.
exact: hi.
Qed.

(** Source for [daniell_graph_decomposition_fibre_support]:
    spt k(x) lies in g^{-1}{x} almost everywhere,
    Federer 2.5.20, p. 114, by spt(h#gamma) subset im h. *)
Theorem daniell_graph_decomposition_fibre_support (R : realType) (X Y : metricType R)
    (g : Y -> X) (A : (Y -> R) -> R) (phi : set X -> \bar R)
    (k : X -> daniell_weak_space (@compactly_supported_continuous_functions R Y)) :
  compact (@setT Y) -> continuous g ->
  is_daniell_integral (@compactly_supported_continuous_functions R Y) A ->
  is_daniell_disintegration (daniell_pushforward (daniell_graph_map g) A) phi k ->
  measure_almost_everywhere phi [set x |
    compact_support_daniell_support (k x) `<=` [set y | g y=x]].
Proof.
move=> hY hg hA hD.
have hs := compact_source_pushforward_support hY
  (hausdorff_binary_product (@metric_hausdorff R X) (@metric_hausdorff R Y)) (daniell_graph_map_continuous hg) hA.
apply: (@measure_almost_everywhere_mono R X phi (daniell_disintegration_measure hD) _ _ _
  (daniell_disintegration_support hD))=> x hx y hy.
exact (@daniell_graph_map_image_fibre X Y g x y (hs (x,y) (hx y hy))).
Qed.
