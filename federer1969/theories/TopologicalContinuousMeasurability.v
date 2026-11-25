(** Federer (1969), 2.10.1, p. 170: every continuous map into a metric space
    is measurable for the corrected topological construction. Use the book's
    cited criterion 2.3.2(8), p. 74. Common whole-space open refinements
    retain two independent cover constraints while a pulled- back small-ball
    cover prevents a generator from meeting both separated image pieces.
    Source context and the necessary correction of the topological cover
    quantifier: TopologicalCaratheodoryUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import OpenRefiningEnvelopeUP OpenRefiningEnvelopeLaws OpenRefiningEnvelope
  TopologicalCaratheodoryUP TopologicalCaratheodoryLaws TopologicalCaratheodoryMeasure
  CommonOpenCover OpenRefiningSeparation ContinuousMetricBallCover
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableSeparationUP MeasurableMetricCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [topological_caratheodory_continuous_measurable]:
    corrected full continuous-map assertion of Federer
    2.10.1, p. 170, using the whole-space cover convention.
    The source topology need not be metrizable or Hausdorff,
    and the metric target need not be separable. This follows
    from the proved separated-image criterion 2.3.2(8),
    p. 74, without a new measurability assumption. *)
Theorem topological_caratheodory_continuous_measurable (R : realType) (X : topologicalType)
    (Y : metricType R) (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (mu : set X -> \bar R) (f : X -> Y) :
  is_topological_caratheodory S cost mu -> (forall j, 0<=cost j) -> continuous f ->
  is_measure_measurable_function mu (partial_function_total f).
Proof.
move=> hmu hc hf; have hm := topological_caratheodory_is_measure hmu hc.
have hdom : measure_almost_everywhere mu (partial_function_domain (partial_function_total f)).
  rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
apply: (@measurable_metric_image_separation_iff R X Y mu hm _ hdom).2.
move=> T A B [e [he hdist]]; rewrite !partial_function_total_preimage.
pose A' := T `&` (f @^-1` A).
pose B' := T `&` (f @^-1` B).
apply: (@topological_caratheodory_add_bound R X J S cost mu A' (mu B') (mu T) hmu
  (topological_caratheodory_nonnegative hmu B'))=> H nu hH hn.
rewrite addeC.
apply: (@topological_caratheodory_add_bound R X J S cost mu B' (nu A') (mu T) hmu
  (open_refining_envelope_nonnegative hn A'))=> K xi hK hx.
pose P := continuous_metric_ball_cover f e.
pose L := common_open_cover (common_open_cover H K) P.
have hP : is_whole_space_open_cover P.
  exact: continuous_metric_ball_cover_whole hf he.
have hL : is_whole_space_open_cover L.
  exact: common_open_cover_whole (common_open_cover_whole hH hK) hP.
pose omega := open_refining_envelope S cost L.
have hw := open_refining_envelope_specification S cost L.
have hLH j : generator_refines_cover S L j -> generator_refines_cover S H j.
  move=> hr; apply: generator_common_cover_left.
  exact: generator_common_cover_left hr.
have hLK j : generator_refines_cover S L j -> generator_refines_cover S K j.
  move=> hr; apply: generator_common_cover_right.
  exact: generator_common_cover_left hr.
have hsep j : generator_refines_cover S L j ->
    forall x, A' x -> S j x -> forall y, B' y -> S j y -> False.
  move=> hr x [_ hfxA] hsx y [_ hfyB] hsy.
  have hball : generator_refines_cover S P j := generator_common_cover_right hr.
  have hsmall := @continuous_ball_cover_generator_image_bound R X J Y S f e j hball x y hsx hsy.
  have hlarge := hdist (f x) hfxA (f y) hfyB.
  by have := le_lt_trans hlarge hsmall; rewrite ltxx.
have hT : A' `|` B' `<=` T by move=> x [[htx _]|[htx _]].
have hb := @open_refining_envelope_separated_bound R X J S cost H K L nu xi omega
  A' B' T hn hx hw hc hLH hLK hsep hT.
have hupper := @topological_caratheodory_upper R X J S cost mu hmu T L omega hL hw.
rewrite addeC; exact: le_trans hb hupper.
Qed.
